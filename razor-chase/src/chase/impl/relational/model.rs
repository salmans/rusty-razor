//! A model as a `codd` database plus a union-find over its elements.
use super::{
    pre_processor::{Witness, Witnesses},
    union_find::UnionFind,
    Symbol, Tuple, ViewExpr,
};
use crate::chase::{
    r#impl::basic::BasicWitnessTerm, Admission, Bounder, Model, Observation, Rel, E,
};
use codd::{expression::Relation, Database, Tuples};
use itertools::Itertools;
use razor_fol::syntax::Sig;
use std::{collections::HashMap, fmt, rc::Rc};

/// What is known about an element beyond the facts: its Skolem depth, the depth of the
/// shallowest term that names it.
#[derive(Clone, Debug)]
pub(super) struct ElementInfo {
    pub depth: u32,
}

/// Is a [`Model`] implemented as a database of canonical tuples.
///
/// [`Model`]: crate::chase::Model
pub struct RelModel {
    id: u64,
    db: Database,
    relations: Rc<HashMap<Symbol, Relation<Tuple>>>,
    equality: UnionFind<E>,
    /// Function applications on canonical arguments and their canonical outputs.
    functions: im::HashMap<(Symbol, Tuple), E>,
    elements: im::HashMap<E, ElementInfo>,
    next_element: i32,
}

impl RelModel {
    /// Creates an empty model over `signature`. The `witnesses` get no relation: no view reads
    /// them, so the function table alone records the elements they name.
    pub(super) fn new(signature: &Sig, witnesses: &Witnesses) -> Self {
        let constants = signature
            .constants()
            .iter()
            .map(|c| Symbol::Const(c.clone()));
        let functions = signature
            .functions()
            .values()
            .map(|f| Symbol::Func(f.symbol.clone()));
        let predicates = signature
            .predicates()
            .values()
            .map(|p| Symbol::Pred(p.symbol.clone()));
        let mut db = Database::new();
        let relations: HashMap<Symbol, Relation<Tuple>> = constants
            .chain(functions)
            .filter(|symbol| witnesses.get(symbol).is_none())
            .chain(predicates)
            .chain(std::iter::once(Symbol::Domain))
            .map(|symbol| {
                let relation = db.add_relation::<Tuple>(&symbol.relation_name()).unwrap();
                (symbol, relation)
            })
            .collect();
        Self {
            id: rand::random(),
            db,
            relations: Rc::new(relations),
            equality: UnionFind::default(),
            functions: im::HashMap::new(),
            elements: im::HashMap::new(),
            next_element: 0,
        }
    }

    /// The database, for compiling views into it before the first fork.
    pub(super) fn database_mut(&mut self) -> &mut Database {
        &mut self.db
    }

    /// The canonical representative of `e`.
    #[inline]
    pub fn canon(&self, e: E) -> E {
        self.equality.find(e)
    }

    /// The number of elements in the domain.
    pub fn size(&self) -> usize {
        self.elements.len()
    }

    /// Does some element lie beyond `bound`, which would not admit it to the other elements?
    pub(super) fn exceeds<B: Bounder + ?Sized>(&self, bound: &B) -> bool {
        let others = self.size().saturating_sub(1);
        self.elements
            .values()
            .any(|info| bound.admit(others, info.depth) != Admission::Create)
    }

    pub(super) fn info(&self, e: E) -> &ElementInfo {
        &self.elements[&self.canon(e)]
    }

    fn relation(&self, symbol: &Symbol) -> &Relation<Tuple> {
        self.relations
            .get(symbol)
            .unwrap_or_else(|| panic!("no relation for symbol {:?}", symbol))
    }

    /// The canonical output of `function` on canonical `args`, if defined.
    pub(super) fn lookup(&self, function: &Symbol, args: &[E]) -> Option<E> {
        self.functions
            .get(&(function.clone(), args.to_vec()))
            .map(|e| self.canon(*e))
    }

    /// Creates a fresh element with the given Skolem depth.
    pub(super) fn new_element(&mut self, depth: u32) -> E {
        let e = E(self.next_element);
        self.next_element += 1;
        self.elements.insert(e, ElementInfo { depth });
        self.db
            .insert(self.relation(&Symbol::Domain), vec![vec![e]].into())
            .unwrap();
        e
    }

    /// Records the fact `function(args) = out` for canonical `args` and `out`. If the function
    /// was already defined on `args` with a different output, the two outputs are merged.
    pub(super) fn define(&mut self, function: &Symbol, args: Vec<E>, out: E) {
        let mut tuple = args.clone();
        tuple.push(out);
        if self.tabulate(function, args, out) {
            self.db
                .insert(self.relation(function), vec![tuple].into())
                .unwrap();
        }
    }

    /// Records that `witness(args)` names `e`, for canonical `args` and `e`. If the witness
    /// already named another element on `args`, the two are merged.
    pub(super) fn name(&mut self, witness: &Witness, args: Vec<E>, e: E) {
        self.tabulate(witness.symbol(), args, e);
    }

    /// Enters `symbol(args) = out` in the function table. Returns false, after merging the two
    /// outputs, if `symbol` was already defined on `args`.
    fn tabulate(&mut self, symbol: &Symbol, args: Vec<E>, out: E) -> bool {
        if let Some(existing) = self.lookup(symbol, &args) {
            if existing != out {
                self.merge(existing, out);
            }
            return false;
        }
        let depth = self.depth(&args);
        self.functions.insert((symbol.clone(), args), out);
        if let Some(info) = self
            .elements
            .get_mut(&out)
            .filter(|info| info.depth > depth)
        {
            info.depth = depth;
            self.lower(vec![out]);
        }
        true
    }

    /// The depth of an entry of the function table on canonical `args`: 0 for a constant, one
    /// more than the deepest argument otherwise.
    pub(super) fn depth(&self, args: &[E]) -> u32 {
        args.iter()
            .map(|a| self.info(*a).depth + 1)
            .max()
            .unwrap_or(0)
    }

    /// Lowers the depth of every element named by a term over a lowered element, and so on to a
    /// fixpoint. An element's depth is that of its shallowest name: after `f#0(e0) = e1` the
    /// entry `'c = e1` makes `e1` depth 0, and every `f(…, e1, …)` output one shallower.
    fn lower(&mut self, mut changed: Vec<E>) {
        while let Some(e) = changed.pop() {
            let e = self.canon(e);
            let entries: Vec<(u32, E)> = self
                .functions
                .iter()
                .filter(|((_, args), _)| args.contains(&e))
                .map(|((_, args), out)| (self.depth(args), self.canon(*out)))
                .collect();
            for (depth, out) in entries {
                let info = self
                    .elements
                    .get_mut(&out)
                    .expect("an output is an element");
                if depth < info.depth {
                    info.depth = depth;
                    changed.push(out);
                }
            }
        }
    }

    /// Adds a relational fact over canonical elements.
    pub(super) fn insert_fact(&mut self, predicate: &Symbol, tuple: Tuple) {
        self.db
            .insert(self.relation(predicate), vec![tuple].into())
            .unwrap();
    }

    /// Identifies two elements and rewrites every tuple that mentions the loser. Merges
    /// triggered by functionality cascade until the model is canonical again.
    pub(super) fn merge(&mut self, a: E, b: E) {
        let mut pending = vec![(a, b)];
        let mut winners = Vec::new();
        while let Some((a, b)) = pending.pop() {
            let Some((winner, loser)) = self.equality.union(a, b) else {
                continue;
            };
            winners.push(winner);
            // The merged element is denoted by the terms of both classes, so it is as shallow
            // as the shallower of the two.
            let loser_depth = self.elements.remove(&loser).map(|info| info.depth);
            if let (Some(depth), Some(info)) = (loser_depth, self.elements.get_mut(&winner)) {
                info.depth = info.depth.min(depth);
            }

            // rewrite relations:
            let symbols: Vec<Symbol> = self.relations.keys().cloned().collect();
            for symbol in symbols {
                let relation = self.relation(&symbol).clone();
                let content = self.db.evaluate(&relation).unwrap();
                let (stale, fresh): (Vec<Tuple>, Vec<Tuple>) = content
                    .iter()
                    .filter(|t| t.contains(&loser))
                    .map(|t| {
                        let rewritten: Tuple = t
                            .iter()
                            .map(|e| if *e == loser { winner } else { *e })
                            .collect();
                        (t.clone(), rewritten)
                    })
                    .unzip();
                if stale.is_empty() {
                    continue;
                }
                self.db.retract(&relation, stale.into()).unwrap();
                if symbol != Symbol::Domain {
                    self.db.insert(&relation, fresh.into()).unwrap();
                }
            }

            // rewrite the function table; collisions are new merges:
            let touched: Vec<((Symbol, Tuple), E)> = self
                .functions
                .iter()
                .filter(|((_, args), out)| args.contains(&loser) || **out == loser)
                .map(|(k, v)| (k.clone(), *v))
                .collect();
            for ((symbol, args), out) in touched {
                self.functions.remove(&(symbol.clone(), args.clone()));
                let args: Tuple = args
                    .iter()
                    .map(|e| if *e == loser { winner } else { *e })
                    .collect();
                let out = if out == loser { winner } else { out };
                match self.functions.get(&(symbol.clone(), args.clone())) {
                    Some(other) if *other != out => pending.push((*other, out)),
                    Some(_) => {}
                    None => {
                        self.functions.insert((symbol, args), out);
                    }
                }
            }
        }
        // the entries over a winner may now name their outputs by shallower terms:
        self.lower(winners);
    }

    /// Evaluates a stored view and returns its tuples.
    pub(super) fn evaluate_view(&self, view: &ViewExpr) -> Tuples<Tuple> {
        self.db.evaluate(view).unwrap()
    }

    /// Is `trigger` (canonicalized) still an active trigger of the sequent whose triggers
    /// `view` holds?
    pub(super) fn contains(&self, view: &ViewExpr, trigger: &[E]) -> bool {
        let trigger: Tuple = trigger.iter().map(|e| self.canon(*e)).collect();
        self.evaluate_view(view).binary_search(&trigger).is_ok()
    }

    fn content(&self, symbol: &Symbol) -> Vec<Tuple> {
        self.db
            .evaluate(self.relation(symbol))
            .unwrap()
            .into_tuples()
    }

    /// Function applications (over elements) that denote `e`, as witness terms.
    fn applications(&self, e: E) -> Vec<BasicWitnessTerm> {
        self.functions
            .iter()
            .filter(|(_, out)| self.canon(**out) == e)
            .map(|((symbol, args), _)| match symbol {
                Symbol::Const(c) => BasicWitnessTerm::Const(c.clone()),
                Symbol::Func(f) => BasicWitnessTerm::App {
                    function: f.clone(),
                    terms: args.iter().map(|a| BasicWitnessTerm::Elem(*a)).collect(),
                },
                _ => unreachable!(),
            })
            .collect()
    }
}

impl Model for RelModel {
    type TermType = BasicWitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<E> {
        self.elements.keys().copied().sorted().collect()
    }

    fn facts(&self) -> Vec<Observation<BasicWitnessTerm>> {
        let mut result = Vec::new();
        for symbol in self.relations.keys() {
            match symbol {
                Symbol::Pred(p) => {
                    for t in self.content(symbol) {
                        result.push(Observation::Fact {
                            relation: Rel::from(p.name()),
                            terms: t.into_iter().map(BasicWitnessTerm::Elem).collect(),
                        });
                    }
                }
                Symbol::Func(_) | Symbol::Const(_) => {}
                Symbol::Domain => {}
            }
        }
        for ((symbol, args), out) in self.functions.iter() {
            let left = match symbol {
                Symbol::Const(c) => BasicWitnessTerm::Const(c.clone()),
                Symbol::Func(f) => BasicWitnessTerm::App {
                    function: f.clone(),
                    terms: args.iter().map(|a| BasicWitnessTerm::Elem(*a)).collect(),
                },
                _ => unreachable!(),
            };
            result.push(Observation::Identity {
                left,
                right: BasicWitnessTerm::Elem(self.canon(*out)),
            });
        }
        result.sort();
        result
    }

    fn witness(&self, element: &E) -> Vec<BasicWitnessTerm> {
        self.applications(self.canon(*element))
    }

    fn element(&self, witness: &BasicWitnessTerm) -> Option<E> {
        match witness {
            BasicWitnessTerm::Elem(e) => {
                let e = self.canon(*e);
                self.elements.contains_key(&e).then_some(e)
            }
            BasicWitnessTerm::Const(c) => self.lookup(&Symbol::Const(c.clone()), &[]),
            BasicWitnessTerm::App { function, terms } => {
                let args: Option<Vec<E>> = terms.iter().map(|t| self.element(t)).collect();
                self.lookup(&Symbol::Func(function.clone()), &args?)
            }
        }
    }

    fn finalize(self) -> Self {
        self
    }
}

impl Clone for RelModel {
    fn clone(&self) -> Self {
        Self {
            id: rand::random(),
            db: self.db.clone(),
            relations: self.relations.clone(),
            equality: self.equality.clone(),
            functions: self.functions.clone(),
            elements: self.elements.clone(),
            next_element: self.next_element,
        }
    }
}

impl fmt::Debug for RelModel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let domain: Vec<String> = self.domain().iter().map(|e| e.to_string()).collect();
        let elements: Vec<String> = self
            .domain()
            .iter()
            .map(|e| {
                let witnesses: Vec<String> = self
                    .witness(e)
                    .iter()
                    .map(|w| w.to_string())
                    .sorted()
                    .collect();
                format!("{} -> {}", witnesses.join(", "), e)
            })
            .collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(
            f,
            "Domain: {{{}}}\nElements:{}\nFacts: {}\n",
            domain.join(", "),
            elements.join(", "),
            facts.join(", ")
        )
    }
}
