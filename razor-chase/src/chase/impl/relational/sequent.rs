//! A geometric sequent compiled into trigger views and the symbolic atoms of its head.
//!
//! A head disjunct `∃ȳ. φ` asks only that *some* elements satisfy `φ`, so its truth test
//! projects the existentials away. When none do, the chase creates them: an existential that a
//! function application of `φ` outputs (`∃y. y = g(x)`) is that application's value, and every
//! other one is a [`Binder`], whose [`Witness`] (minted here, over the sequent's universals)
//! names the element the chase creates. A function in a head, Skolem or not, always names a
//! specific element that other sequents may refer to, so the truth test checks its value.
//!
//! Relationalizing a sequent mints placeholder variables and the relations of its functions and
//! constants; a [`Vocabulary`] of the sequent's universals and the minted relations reads its
//! clauses back, so no name is parsed.
use super::{union_find::UnionFind, Symbol, Tuple, ViewExpr};
use crate::chase::Sequent;
use codd::{
    expression::{
        Difference, Empty, Join, Mono, Product, Project, Relation, Select, Singleton, Union,
    },
    Database,
};
use razor_fol::{
    syntax::{
        formula::{Atom, Atomic},
        Const, Formula, Func, Pred, Var, FOF,
    },
    transform::{FlatClause, Skolemizer, ToRelational, GNF, PCF},
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap},
};

/// The symbol that names the elements a [`Binder`] creates. It takes no part in any truth
/// test, so the database holds no relation for it: only the model's function table records the
/// elements it names.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Witness(Symbol);

impl Witness {
    /// A fresh witness over `scope`: a function of it, or a constant when it is empty.
    fn mint(skolemizer: &mut Skolemizer, scope: &[Var]) -> Self {
        Witness(if scope.is_empty() {
            Symbol::Const(skolemizer.constant())
        } else {
            Symbol::Func(skolemizer.function())
        })
    }

    pub(super) fn symbol(&self) -> &Symbol {
        &self.0
    }
}

/// Where the value of a head variable comes from when a disjunct is applied.
#[derive(Clone, Copy, Debug)]
pub(super) enum Attribute {
    /// A universal variable, taken from the trigger.
    Body(usize),
    /// An existential variable, produced by a function application of the disjunct.
    Exist(usize),
}

/// What a function application of a disjunct applies.
#[derive(Clone, Debug)]
pub(super) enum Function {
    /// A function or constant of the database, whose applications are facts.
    Symbol(Symbol),
    /// A witness of a binder, whose applications only name the elements it creates.
    Witness(Witness),
}

impl Function {
    /// The symbol under which the model tabulates the function's applications.
    pub(super) fn symbol(&self) -> &Symbol {
        match self {
            Function::Symbol(symbol) => symbol,
            Function::Witness(witness) => witness.symbol(),
        }
    }
}

/// An atom of a head disjunct over the attributes of a trigger and of the disjunct's
/// existentials; balancing the disjunct makes it true.
#[derive(Clone, Debug)]
pub(super) enum SymbolicAtom {
    /// `function(args) = out`, whose output element is created when needed.
    Function {
        function: Function,
        args: Vec<Attribute>,
        out: Attribute,
    },
    /// A relational fact `symbol(args)`.
    Relation {
        symbol: Symbol,
        args: Vec<Attribute>,
    },
    /// An equation between two elements.
    Equation(Attribute, Attribute),
}

impl SymbolicAtom {
    /// The elements the atom reads, which must be known before it is balanced.
    fn inputs(&self) -> Vec<&Attribute> {
        match self {
            SymbolicAtom::Function { args, .. } | SymbolicAtom::Relation { args, .. } => {
                args.iter().collect()
            }
            SymbolicAtom::Equation(a, b) => vec![a, b],
        }
    }
}

/// A disjunct of a head, ready to be applied.
#[derive(Clone, Debug)]
pub(super) struct Branch {
    /// The atoms that make the disjunct true, each after the atoms producing its inputs.
    pub atoms: Vec<SymbolicAtom>,
    /// The number of existential variables of the disjunct, which [`Attribute::Exist`] indexes;
    /// it sizes `Balance::exist` in the evaluator.
    pub existential_count: usize,
}

impl Branch {
    /// Does applying the disjunct create elements?
    pub fn creates_elements(&self) -> bool {
        self.existential_count > 0
    }
}

/// A geometric sequent compiled for the relational chase.
#[derive(Clone)]
pub struct RelSequent {
    /// The sequent's active triggers: the environments (over the universal variables) under
    /// which the body holds and no disjunct of the head does, i.e. the homomorphisms of the body
    /// that cannot be extended to the head.
    pub(super) triggers: ViewExpr,
    /// The disjuncts of the head. Empty for a failing sequent.
    pub(super) branches: Vec<Branch>,
    body_formula: FOF,
    head_formula: FOF,
}

impl RelSequent {
    /// Compiles `sequent`, storing its views in `db`. `skolemizer` mints one witness for every
    /// existential of the head, in order, over the variables it depends on
    /// ([`GNF::scopes`]), whether or not it becomes a binder. Returns `None`
    /// when the sequent can never have a trigger (a disjunct of its head is `⊤`).
    pub(super) fn compile(
        sequent: &GNF,
        db: &mut Database,
        skolemizer: &mut Skolemizer,
    ) -> Option<Self> {
        let (vocabulary, body, head) = Vocabulary::relationalize(sequent);
        let universals = &vocabulary.universals;
        let body = Conjunction::from_flat(&body, &vocabulary);
        let head: Vec<HeadClause> = sequent
            .scopes()
            .zip(&head)
            .map(|((disjunct, scope), clause)| {
                let scope: Vec<Var> = scope.into_iter().cloned().collect();
                let witnesses = disjunct
                    .existentials()
                    .iter()
                    .map(|v| (Witness::mint(skolemizer, &scope), v.clone()))
                    .collect();
                HeadClause::new(clause, witnesses, &scope, &vocabulary)
            })
            .collect();

        if head.iter().any(HeadClause::is_top) {
            return None;
        }

        let body_view = db.store_view(body.plan(universals, &[])).unwrap();
        let head_expr: Mono<Tuple> = head
            .iter()
            .map(|c| c.plan(universals))
            .reduce(|acc, next| Union::new(acc, next).into())
            .unwrap_or_else(|| Empty::new().into());
        let head_view = db.store_view(head_expr).unwrap();
        let difference: Mono<Tuple> =
            Difference::new(Mono::from(body_view), Mono::from(head_view)).into();
        let triggers = db.store_view(difference).unwrap();

        Some(Self {
            triggers,
            branches: head.iter().map(|c| c.branch(universals)).collect(),
            body_formula: sequent.body().into(),
            head_formula: sequent.head().into(),
        })
    }

    /// The triggers a chase step fires on: all of them when the head has one disjunct (a Horn
    /// sequent saturates in one step), the first one only otherwise (a later step forks again
    /// on the rest, so every combination of choices is explored).
    pub(super) fn firing<'t>(&self, triggers: &'t [Tuple]) -> &'t [Tuple] {
        if self.branches.len() == 1 {
            triggers
        } else {
            &triggers[..1]
        }
    }
}

impl Sequent for RelSequent {
    fn body(&self) -> FOF {
        self.body_formula.clone()
    }

    fn head(&self) -> FOF {
        self.head_formula.clone()
    }
}

impl std::fmt::Display for RelSequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} -> {}", self.body_formula, self.head_formula)
    }
}

impl std::fmt::Debug for RelSequent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// A variable of a relationalized clause, classified once when the clause is read. Universals
/// order before existentials, so an existential yields to a universal in [`Aliases`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ClauseVar {
    /// A variable of the sequent, bound by the trigger.
    Universal(Var),
    /// A variable introduced by relationalization: the output of a function application or an
    /// existentially quantified variable of a head.
    Existential(Var),
}

/// What relationalizing a sequent established about the names in its clauses: the sequent's
/// universal variables, and the function or constant behind each relation it minted. Every
/// other variable was minted, and every other predicate is one of the theory's.
struct Vocabulary {
    universals: Vec<Var>,
    relations: HashMap<Pred, Symbol>,
}

impl Vocabulary {
    /// Relationalizes the body and every head disjunct of `sequent`, recording what it mints. A
    /// placeholder is named `?N` for display only.
    fn relationalize(sequent: &GNF) -> (Self, FlatClause, Vec<FlatClause>) {
        let mut counter = 0u32;
        let mut var_generator = || {
            let name = format!("?{}", counter);
            counter += 1;
            Var::from(name)
        };
        let relations = RefCell::new(HashMap::new());
        let relation = |symbol: Symbol| {
            let predicate = Pred::from(symbol.relation_name());
            relations.borrow_mut().insert(predicate.clone(), symbol);
            predicate
        };
        let mut const_generator = |c: &Const| relation(Symbol::Const(c.clone()));
        let mut fn_generator = |f: &Func| relation(Symbol::Func(f.clone()));
        let mut flatten = |conjunction: &PCF| {
            conjunction
                .relational_with(&mut var_generator, &mut const_generator, &mut fn_generator)
                .into_clauses()
                .pop()
                .expect("a conjunction relationalizes to one clause")
        };
        let body = flatten(sequent.body());
        let head = sequent
            .head()
            .iter()
            .map(|disjunct| flatten(disjunct.atoms()))
            .collect();
        let vocabulary = Vocabulary {
            universals: sequent.free_vars().into_iter().cloned().collect(),
            relations: relations.into_inner(),
        };
        (vocabulary, body, head)
    }

    fn var(&self, v: &Var) -> ClauseVar {
        if self.universals.contains(v) {
            ClauseVar::Universal(v.clone())
        } else {
            ClauseVar::Existential(v.clone())
        }
    }

    fn symbol(&self, predicate: &Pred) -> Symbol {
        self.relations
            .get(predicate)
            .cloned()
            .unwrap_or_else(|| Symbol::Pred(predicate.clone()))
    }
}

/// An atom of a relationalized clause.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ClauseAtom {
    /// `symbol(args)` for a predicate or the domain.
    Relation {
        symbol: Symbol,
        args: Vec<ClauseVar>,
    },
    /// `symbol(args) = out` for a function or a constant (a function without arguments).
    Function {
        symbol: Symbol,
        args: Vec<ClauseVar>,
        out: ClauseVar,
    },
}

impl ClauseAtom {
    /// The atom over the columns of `symbol`'s relation; functions store their output last.
    fn new(symbol: Symbol, mut columns: Vec<ClauseVar>) -> Self {
        match symbol {
            Symbol::Func(_) | Symbol::Const(_) => {
                let out = columns
                    .pop()
                    .expect("a function relation has an output column");
                ClauseAtom::Function {
                    symbol,
                    args: columns,
                    out,
                }
            }
            Symbol::Pred(_) | Symbol::Domain => ClauseAtom::Relation {
                symbol,
                args: columns,
            },
        }
    }

    fn domain(v: ClauseVar) -> Self {
        ClauseAtom::Relation {
            symbol: Symbol::Domain,
            args: vec![v],
        }
    }

    fn symbol(&self) -> &Symbol {
        match self {
            ClauseAtom::Relation { symbol, .. } | ClauseAtom::Function { symbol, .. } => symbol,
        }
    }

    /// The variables of the columns of the atom's relation, in order.
    fn columns(&self) -> Vec<ClauseVar> {
        match self {
            ClauseAtom::Relation { args, .. } => args.clone(),
            ClauseAtom::Function { args, out, .. } => {
                args.iter().chain(std::iter::once(out)).cloned().collect()
            }
        }
    }

    fn vars_mut(&mut self) -> impl Iterator<Item = &mut ClauseVar> {
        let (args, out) = match self {
            ClauseAtom::Relation { args, .. } => (args, None),
            ClauseAtom::Function { args, out, .. } => (args, Some(out)),
        };
        args.iter_mut().chain(out)
    }
}

/// What a clause asks of a model once its equalities are resolved: atoms over variables plus
/// the equalities that remain between universal variables. A body is one; so is the truth test
/// of a head disjunct.
struct Conjunction {
    atoms: Vec<ClauseAtom>,
    equalities: Vec<(Var, Var)>,
}

impl Conjunction {
    /// Resolves the equalities of a flat clause by renaming existential variables, keeping the
    /// equalities between universals as constraints.
    fn from_flat(clause: &FlatClause, vocabulary: &Vocabulary) -> Self {
        let (mut aliases, atoms) = Aliases::read(clause, vocabulary);
        let atoms = aliases.share_applications(atoms);
        Self::new(atoms, aliases)
    }

    fn new(mut atoms: Vec<ClauseAtom>, aliases: Aliases) -> Self {
        atoms.sort();
        atoms.dedup();
        Self {
            atoms,
            equalities: aliases.into_equalities(),
        }
    }

    fn is_empty(&self) -> bool {
        self.atoms.is_empty() && self.equalities.is_empty()
    }

    /// The conjunction as a query plan over `output`. Output, equality and `ranged` variables
    /// that no atom mentions range over the domain, and every variable but the output is
    /// projected away. The atoms are natural-joined left to right, the equalities become
    /// selections, and the result is projected to `output`.
    fn plan(&self, output: &[Var], ranged: &[ClauseVar]) -> Mono<Tuple> {
        let mut atoms = self.atoms.clone();
        let mentioned: Vec<ClauseVar> = atoms.iter().flat_map(ClauseAtom::columns).collect();
        let output: Vec<ClauseVar> = output.iter().cloned().map(ClauseVar::Universal).collect();
        let constrained = self.equalities.iter().flat_map(|(l, r)| [l, r]);
        for v in output
            .iter()
            .cloned()
            .chain(constrained.cloned().map(ClauseVar::Universal))
            .chain(ranged.iter().cloned())
        {
            if mentioned.contains(&v) {
                continue;
            }
            let domain = ClauseAtom::domain(v);
            if !atoms.contains(&domain) {
                atoms.push(domain);
            }
        }

        let mut plan = atoms
            .iter()
            .map(Plan::atom)
            .reduce(Plan::join)
            .unwrap_or_else(|| Plan {
                expr: Singleton::new(Vec::new()).into(),
                attrs: Vec::new(),
            });
        for (l, r) in &self.equalities {
            let (i, j) = (
                plan.attrs
                    .iter()
                    .position(|a| *a == ClauseVar::Universal(l.clone()))
                    .unwrap(),
                plan.attrs
                    .iter()
                    .position(|a| *a == ClauseVar::Universal(r.clone()))
                    .unwrap(),
            );
            plan.expr = Select::new(plan.expr, move |t: &Tuple| t[i] == t[j]).into();
        }
        if plan.attrs != output {
            let pos = plan.positions(&output);
            plan.expr = Project::new(plan.expr, move |t: &Tuple| {
                pos.iter().map(|i| t[*i]).collect()
            })
            .into();
        }
        plan.expr
    }
}

/// `∃ var`, named by `witness(args)` when the chase has to create it.
#[derive(Clone, Debug)]
struct Binder {
    witness: Witness,
    args: Vec<ClauseVar>,
    var: ClauseVar,
}

/// A disjunct of a head: the existentials it binds and the conjunction that must hold of them.
struct HeadClause {
    binders: Vec<Binder>,
    conjunction: Conjunction,
}

impl HeadClause {
    /// Reads a flat head clause whose existentials come with the `witnesses` minted for them
    /// over the universals of `scope`.
    /// An existential becomes a binder unless a function application of the clause produces it
    /// from the universals and the existentials bound before it. When several are left, the
    /// first that no application outputs is bound, so `∃y, z. y = f(z)` binds `z` alone; when
    /// every one is an output, the applications form a cycle and the first one is bound.
    fn new(
        clause: &FlatClause,
        witnesses: Vec<(Witness, Var)>,
        scope: &[Var],
        vocabulary: &Vocabulary,
    ) -> Self {
        let (mut aliases, atoms) = Aliases::read(clause, vocabulary);
        let atoms = aliases.share_applications(atoms);
        let mut unbound: Vec<(Witness, ClauseVar)> = witnesses
            .into_iter()
            .map(|(witness, v)| (witness, aliases.find(&vocabulary.var(&v))))
            .collect();
        let outputs: BTreeSet<&ClauseVar> = atoms
            .iter()
            .filter_map(|atom| match atom {
                ClauseAtom::Function { out, .. } => Some(out),
                ClauseAtom::Relation { .. } => None,
            })
            .collect();
        let mut known = Known::default();
        let mut binders = Vec::new();
        loop {
            known.produce(&atoms);
            unbound.retain(|(_, v)| !known.contains(v));
            if unbound.is_empty() {
                break;
            }
            let first = unbound
                .iter()
                .position(|(_, v)| !outputs.contains(v))
                .unwrap_or(0);
            let (witness, var) = unbound.remove(first);
            known.bind(var.clone());
            let args = scope.iter().map(|v| vocabulary.var(v)).collect();
            binders.push(Binder { witness, args, var });
        }
        Self {
            binders,
            conjunction: Conjunction::new(atoms, aliases),
        }
    }

    /// Is the disjunct `⊤`?
    fn is_top(&self) -> bool {
        self.binders.is_empty() && self.conjunction.is_empty()
    }

    /// The truth test of the disjunct over `output`: the binders only ask that some element
    /// exists, so their variables range over the domain and are projected away with the other
    /// existentials.
    fn plan(&self, output: &[Var]) -> Mono<Tuple> {
        let bound: Vec<ClauseVar> = self.binders.iter().map(|b| b.var.clone()).collect();
        self.conjunction.plan(output, &bound)
    }

    /// The disjunct as symbolic atoms over the sequent's `universals`. Existential variables are
    /// numbered in order of first sight and domain atoms are skipped. The binders come first;
    /// every function application follows the applications producing its arguments, and
    /// equalities between universals become equations.
    fn branch(&self, universals: &[Var]) -> Branch {
        let mut existentials: Vec<Var> = Vec::new();
        let attr = |v: &ClauseVar, existentials: &mut Vec<Var>| -> Attribute {
            match v {
                ClauseVar::Universal(u) => Attribute::Body(
                    universals
                        .iter()
                        .position(|w| w == u)
                        .expect("a universal of a head is a variable of the sequent"),
                ),
                ClauseVar::Existential(e) => {
                    Attribute::Exist(match existentials.iter().position(|x| x == e) {
                        Some(j) => j,
                        None => {
                            existentials.push(e.clone());
                            existentials.len() - 1
                        }
                    })
                }
            }
        };

        let binders = self.binders.iter().map(|binder| SymbolicAtom::Function {
            function: Function::Witness(binder.witness.clone()),
            args: binder
                .args
                .iter()
                .map(|v| attr(v, &mut existentials))
                .collect(),
            out: attr(&binder.var, &mut existentials),
        });
        let mut pending: Vec<SymbolicAtom> = binders.collect();
        pending.extend(
            self.conjunction
                .atoms
                .iter()
                .filter(|atom| *atom.symbol() != Symbol::Domain)
                .map(|atom| match atom {
                    ClauseAtom::Relation { symbol, args } => SymbolicAtom::Relation {
                        symbol: symbol.clone(),
                        args: args.iter().map(|v| attr(v, &mut existentials)).collect(),
                    },
                    ClauseAtom::Function { symbol, args, out } => SymbolicAtom::Function {
                        function: Function::Symbol(symbol.clone()),
                        args: args.iter().map(|v| attr(v, &mut existentials)).collect(),
                        out: attr(out, &mut existentials),
                    },
                }),
        );
        let mut bound: Vec<bool> = vec![false; existentials.len()];
        let is_bound = |a: &Attribute, bound: &[bool]| match a {
            Attribute::Body(_) => true,
            Attribute::Exist(j) => bound[*j],
        };

        let mut atoms = Vec::new();
        while !pending.is_empty() {
            let before = pending.len();
            let mut i = 0;
            while i < pending.len() {
                if pending[i].inputs().iter().all(|a| is_bound(a, &bound)) {
                    let atom = pending.remove(i);
                    if let SymbolicAtom::Function {
                        out: Attribute::Exist(j),
                        ..
                    } = atom
                    {
                        bound[j] = true;
                    }
                    atoms.push(atom);
                } else {
                    i += 1;
                }
            }
            assert!(
                pending.len() < before,
                "an existential variable of a head is not produced by a function: {:?}",
                pending
            );
        }
        for (l, r) in &self.conjunction.equalities {
            atoms.push(SymbolicAtom::Equation(
                attr(&ClauseVar::Universal(l.clone()), &mut existentials),
                attr(&ClauseVar::Universal(r.clone()), &mut existentials),
            ));
        }
        Branch {
            atoms,
            existential_count: existentials.len(),
        }
    }
}

/// The clause variables whose elements are known while a disjunct is applied: the universals,
/// and the existentials bound or produced so far.
#[derive(Default)]
struct Known(BTreeSet<ClauseVar>);

impl Known {
    fn contains(&self, v: &ClauseVar) -> bool {
        match v {
            ClauseVar::Universal(_) => true,
            ClauseVar::Existential(_) => self.0.contains(v),
        }
    }

    fn bind(&mut self, v: ClauseVar) {
        self.0.insert(v);
    }

    /// Adds the outputs of the function applications of `atoms` whose arguments are known, to a
    /// fixpoint.
    fn produce(&mut self, atoms: &[ClauseAtom]) {
        while let Some(out) = atoms.iter().find_map(|atom| match atom {
            ClauseAtom::Function { args, out, .. }
                if !self.contains(out) && args.iter().all(|a| self.contains(a)) =>
            {
                Some(out.clone())
            }
            _ => None,
        }) {
            self.0.insert(out);
        }
    }
}

/// The aliases of one clause: the clause variables that its equalities and shared
/// applications equate. Existentials are renamed to the variables they equal, so universals are
/// always roots and an identification of two universals remains as an equality.
#[derive(Default)]
struct Aliases {
    classes: UnionFind<ClauseVar>,
    equalities: Vec<(Var, Var)>,
}

impl Aliases {
    /// Reads a flat clause: identifies the variables its equalities equate and returns its
    /// atoms, not yet renamed.
    fn read(clause: &FlatClause, vocabulary: &Vocabulary) -> (Self, Vec<ClauseAtom>) {
        let mut aliases = Aliases::default();
        for literal in clause.iter() {
            if let Atomic::Equals(eq) = literal {
                aliases.identify(
                    &vocabulary.var(eq.left.symbol()),
                    &vocabulary.var(eq.right.symbol()),
                );
            }
        }
        let atoms = clause
            .iter()
            .filter_map(|literal| match literal {
                Atomic::Atom(Atom { predicate, terms }) => Some(ClauseAtom::new(
                    vocabulary.symbol(predicate),
                    terms.iter().map(|t| vocabulary.var(t.symbol())).collect(),
                )),
                Atomic::Equals(_) => None,
            })
            .collect();
        (aliases, atoms)
    }

    fn find(&self, v: &ClauseVar) -> ClauseVar {
        self.classes.find(v.clone())
    }

    /// Identifies `a` and `b`. An existential yields to a universal, since universals are the
    /// smaller [`ClauseVar`]s; two universals stay apart and are recorded as an equality.
    fn identify(&mut self, a: &ClauseVar, b: &ClauseVar) {
        match (self.find(a), self.find(b)) {
            (ClauseVar::Universal(l), ClauseVar::Universal(r)) if l != r => {
                self.equalities.push((l, r))
            }
            (a, b) => {
                self.classes.union(a, b);
            }
        }
    }

    /// Rewrites `atoms` so that applications of one function to the same arguments share one
    /// output. Relationalization gives every occurrence of a term its own output variable.
    /// Functionality already makes those outputs equal in every model, so sharing is only an
    /// optimization: it saves joins in the views and atoms in the branches.
    ///
    /// Each round rewrites the atoms through the aliases, groups the function applications by
    /// symbol and arguments, identifies the outputs of each group with its first one and keeps
    /// one application per group. Identifying outputs can make further arguments equal, so the
    /// rounds repeat until every group has one member. Each round either stops or removes at
    /// least one atom, so the rounds terminate.
    fn share_applications(&mut self, mut atoms: Vec<ClauseAtom>) -> Vec<ClauseAtom> {
        loop {
            for v in atoms.iter_mut().flat_map(ClauseAtom::vars_mut) {
                *v = self.find(v);
            }
            let mut kept = Vec::new();
            let mut groups: BTreeMap<(Symbol, Vec<ClauseVar>), Vec<ClauseVar>> = BTreeMap::new();
            for atom in atoms {
                match atom {
                    ClauseAtom::Function { symbol, args, out } => {
                        groups.entry((symbol, args)).or_default().push(out)
                    }
                    relation @ ClauseAtom::Relation { .. } => kept.push(relation),
                }
            }
            let settled = groups.values().all(|outs| outs.len() == 1);
            for ((symbol, args), outs) in groups {
                for out in &outs[1..] {
                    self.identify(&outs[0], out);
                }
                let out = outs[0].clone();
                kept.push(ClauseAtom::Function { symbol, args, out });
            }
            if settled {
                return kept;
            }
            atoms = kept;
        }
    }

    /// The equalities between universals, which are never renamed.
    fn into_equalities(self) -> Vec<(Var, Var)> {
        let mut equalities = self.equalities;
        equalities.sort();
        equalities.dedup();
        equalities
    }
}

/// An expression under construction together with the variables of its columns.
struct Plan {
    expr: Mono<Tuple>,
    attrs: Vec<ClauseVar>,
}

impl Plan {
    /// The columns of `self` that hold `vars`.
    fn positions(&self, vars: &[ClauseVar]) -> Vec<usize> {
        vars.iter()
            .map(|v| self.attrs.iter().position(|a| a == v).unwrap())
            .collect()
    }

    /// The relation of `atom`, with repeated variables selected equal and kept once.
    fn atom(atom: &ClauseAtom) -> Self {
        let vars = atom.columns();
        let mut expr: Mono<Tuple> = Relation::new(atom.symbol().relation_name()).into();
        let mut attrs: Vec<ClauseVar> = Vec::new();
        let mut keep: Vec<usize> = Vec::new();
        let mut constraints: Vec<(usize, usize)> = Vec::new();
        for (i, v) in vars.iter().enumerate() {
            match attrs.iter().position(|a| a == v) {
                Some(first) => constraints.push((keep[first], i)),
                None => {
                    attrs.push(v.clone());
                    keep.push(i);
                }
            }
        }
        for (i, j) in constraints {
            expr = Select::new(expr, move |t: &Tuple| t[i] == t[j]).into();
        }
        if keep.len() != vars.len() {
            expr = Project::new(expr, move |t: &Tuple| keep.iter().map(|i| t[*i]).collect()).into();
        }
        Plan { expr, attrs }
    }

    /// The natural join of two plans (a product when they share no variable).
    fn join(self, right: Plan) -> Self {
        let shared: Vec<ClauseVar> = self
            .attrs
            .iter()
            .filter(|a| right.attrs.contains(a))
            .cloned()
            .collect();
        let right_new: Vec<usize> = right
            .attrs
            .iter()
            .enumerate()
            .filter(|(_, a)| !shared.contains(a))
            .map(|(i, _)| i)
            .collect();
        let mut attrs = self.attrs.clone();
        attrs.extend(right_new.iter().map(|i| right.attrs[*i].clone()));

        let expr: Mono<Tuple> = if shared.is_empty() {
            Product::new(self.expr, right.expr, move |l: &Tuple, r: &Tuple| {
                let mut t = l.clone();
                t.extend(right_new.iter().map(|i| r[*i]));
                t
            })
            .into()
        } else {
            let lk = self.positions(&shared);
            let rk = right.positions(&shared);
            Join::new(
                self.expr,
                right.expr,
                move |t: &Tuple| lk.iter().map(|i| t[*i]).collect::<Tuple>(),
                move |t: &Tuple| rk.iter().map(|i| t[*i]).collect::<Tuple>(),
                move |_: &Tuple, l: &Tuple, r: &Tuple| {
                    let mut t = l.clone();
                    t.extend(right_new.iter().map(|i| r[*i]));
                    t
                },
            )
            .into()
        };
        Plan { expr, attrs }
    }
}
