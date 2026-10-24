//! Turns a first-order theory into compiled sequents and an empty model. Skolemization records
//! the symbols it introduces in `Skolems`, the one place that tells a Skolem symbol apart.
use super::{model::RelModel, sequent::RelSequent, union_find::UnionFind, Symbol};
use crate::chase::PreProcessor;
use razor_fol::{
    syntax::{formula::Atomic, term::Complex, Const, Formula, Func, Pred, Term, Theory, Var, FOF},
    transform::{ToGNF, ToSNF, GNF, PCF},
};
use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
};

/// Skolemizes a theory, converts it to geometric normal form and compiles every sequent.
///
/// The Skolem symbols that stand for a head's existentials (`Witnesses::classify` decides
/// which) are read back as existentials: the sequents the normal form split around them are
/// merged again, and a head's truth test asks only that an element exists where they occur.
/// Every other Skolem symbol is an ordinary function.
#[derive(Clone, Debug, Default)]
pub struct RelPreProcessor;

/// The functions and constants of `formula`'s signature.
fn symbols<F: Formula>(formula: &F) -> Vec<Symbol> {
    let sig = formula.signature().expect("invalid signature");
    let functions = sig
        .functions()
        .values()
        .map(|f| Symbol::Func(f.symbol.clone()));
    let constants = sig.constants().iter().map(|c| Symbol::Const(c.clone()));
    functions.chain(constants).collect()
}

/// The symbols Skolemization introduced: the one authority on them, since it mints every one.
///
/// A minted name (`c#N`, `f#N`) only displays the symbol and keeps it apart from the others;
/// `#` is not an identifier character, so it cannot collide with a parsed symbol, and the name
/// is never parsed back.
#[derive(Default)]
pub(super) struct Skolems {
    constants: HashSet<Const>,
    functions: HashSet<Func>,
}

impl Skolems {
    /// A fresh Skolem constant.
    fn constant(&mut self) -> Const {
        let c = Const::from(format!("c#{}", self.constants.len()));
        self.constants.insert(c.clone());
        c
    }

    /// A fresh Skolem function.
    fn function(&mut self) -> Func {
        let f = Func::from(format!("f#{}", self.functions.len()));
        self.functions.insert(f.clone());
        f
    }

    /// Did Skolemization introduce `symbol`?
    fn contains(&self, symbol: &Symbol) -> bool {
        match symbol {
            Symbol::Const(c) => self.constants.contains(c),
            Symbol::Func(f) => self.functions.contains(f),
            Symbol::Pred(_) | Symbol::Domain => false,
        }
    }

    /// The Skolem symbols of `formula`.
    fn of<F: Formula>(&self, formula: &F) -> Vec<Symbol> {
        symbols(formula)
            .into_iter()
            .filter(|s| self.contains(s))
            .collect()
    }
}

/// Does every application of `symbol` in `disjunct` take all of the disjunct's variables as
/// arguments? If not, the symbol's `∃` was in the scope of a universal the application does not
/// see.
fn scoped(symbol: &Symbol, disjunct: &PCF) -> bool {
    fn walk(term: &Complex, symbol: &Symbol, universals: &BTreeSet<&Var>) -> bool {
        match term {
            Complex::Var(_) => true,
            Complex::Const(c) => *symbol != Symbol::Const(c.clone()) || universals.is_empty(),
            Complex::App { function, terms } => {
                let sees_all = *symbol != Symbol::Func(function.clone())
                    || universals.is_subset(&terms.iter().flat_map(Term::vars).collect());
                sees_all && terms.iter().all(|t| walk(t, symbol, universals))
            }
        }
    }
    let universals: BTreeSet<&Var> = disjunct.free_vars().into_iter().collect();
    disjunct.iter().all(|literal| {
        let terms: Vec<&Complex> = match literal {
            Atomic::Atom(atom) => atom.terms.iter().collect(),
            Atomic::Equals(eq) => vec![&eq.left, &eq.right],
        };
        terms.into_iter().all(|t| walk(t, symbol, &universals))
    })
}

/// A Skolem symbol that only names the elements a disjunct creates and takes no part in
/// deciding whether a head is already true. Only [`Witnesses::classify`] makes one.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Witness(Symbol);

impl Witness {
    pub(super) fn symbol(&self) -> &Symbol {
        &self.0
    }
}

impl Borrow<Symbol> for Witness {
    fn borrow(&self) -> &Symbol {
        &self.0
    }
}

/// The witnesses of a theory.
pub(super) struct Witnesses(HashSet<Witness>);

impl Witnesses {
    /// Decides which Skolem symbols are witnesses. A symbol is one iff it occurs in no body, all
    /// its head occurrences share one body up to a renaming of variables (so `merge_witnessed`
    /// can reunite the split sequents and a single disjunct creates the element it names), and
    /// every variable of a disjunct mentioning it is an argument of each of its applications
    /// there (the arguments are the universals in scope at its `∃`; a variable outside them
    /// means `∃y ∀u`, one element for all `u`). Any other Skolem symbol must denote the same
    /// element wherever it occurs, which only an ordinary function guarantees.
    fn classify(sequents: &[GNF], skolems: &Skolems) -> Self {
        let in_bodies: HashSet<Symbol> =
            sequents.iter().flat_map(|g| skolems.of(g.body())).collect();
        let mut bodies: HashMap<Symbol, &PCF> = HashMap::new();
        let mut shared: HashSet<Symbol> = HashSet::new();
        for disjunct in sequents.iter().flat_map(|g| g.head().iter()) {
            for symbol in skolems.of(disjunct) {
                if !scoped(&symbol, disjunct) {
                    shared.insert(symbol);
                }
            }
        }
        for gnf in sequents {
            for symbol in skolems.of(gnf.head()) {
                match bodies.get(&symbol) {
                    Some(body) if Renaming::onto(gnf, body).is_none() => {
                        shared.insert(symbol);
                    }
                    Some(_) => {}
                    None => {
                        bodies.insert(symbol, gnf.body());
                    }
                }
            }
        }
        Witnesses(
            bodies
                .into_keys()
                .filter(|s| !in_bodies.contains(s) && !shared.contains(s))
                .map(Witness)
                .collect(),
        )
    }

    /// The witness `symbol` is, if it is one.
    pub(super) fn get(&self, symbol: &Symbol) -> Option<&Witness> {
        self.0.get(symbol)
    }

    /// The witnesses of `formula`.
    fn of<F: Formula>(&self, formula: &F) -> Vec<&Witness> {
        symbols(formula)
            .into_iter()
            .filter_map(|s| self.0.get(&s))
            .collect()
    }
}

/// An injective renaming of a sequent's variables that turns its body into another, built while
/// matching one onto the other; two bodies related by one are variants of each other.
#[derive(Clone, Default)]
struct Renaming(HashMap<Var, Var>);

impl Renaming {
    /// The renaming of the variables of `gnf` that turns its body into `body` and maps every
    /// other variable of `gnf` to itself, if it exists and captures no variable.
    fn onto(gnf: &GNF, body: &PCF) -> Option<Self> {
        let from = Kind::group(gnf.body());
        let to = Kind::group(body);
        if from.len() != to.len() {
            return None;
        }
        let renaming = from.iter().zip(&to).try_fold(
            Renaming::default(),
            |renaming, ((a, from), (b, to))| {
                (a == b && from.len() == to.len())
                    .then_some(renaming)?
                    .literals(from, to)
            },
        )?;
        let unrenamed: Vec<&Var> = gnf
            .free_vars()
            .into_iter()
            .filter(|v| !renaming.0.contains_key(*v))
            .collect();
        unrenamed
            .into_iter()
            .try_fold(renaming, |renaming, v| renaming.pair(v, v))
    }

    /// Extends `self` to match `from` onto a permutation of `to`, trying every candidate. Only
    /// literals of one [`Kind`] are passed, so a mismatch elsewhere never backtracks here.
    fn literals(self, from: &[&Atomic<Complex>], to: &[&Atomic<Complex>]) -> Option<Self> {
        let Some((first, rest)) = from.split_first() else {
            return Some(self);
        };
        (0..to.len()).find_map(|j| {
            let renaming = self.clone().literal(first, to[j])?;
            let others: Vec<&Atomic<Complex>> = to
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != j)
                .map(|(_, l)| *l)
                .collect();
            renaming.literals(rest, &others)
        })
    }

    fn literal(self, from: &Atomic<Complex>, to: &Atomic<Complex>) -> Option<Self> {
        match (from, to) {
            (Atomic::Atom(a), Atomic::Atom(b)) if a.predicate == b.predicate => {
                self.terms(&a.terms, &b.terms)
            }
            (Atomic::Equals(a), Atomic::Equals(b)) => {
                self.term(&a.left, &b.left)?.term(&a.right, &b.right)
            }
            _ => None,
        }
    }

    fn terms(self, from: &[Complex], to: &[Complex]) -> Option<Self> {
        if from.len() != to.len() {
            return None;
        }
        from.iter()
            .zip(to)
            .try_fold(self, |renaming, (a, b)| renaming.term(a, b))
    }

    fn term(self, from: &Complex, to: &Complex) -> Option<Self> {
        match (from, to) {
            (Complex::Var(a), Complex::Var(b)) => self.pair(a, b),
            (Complex::Const(a), Complex::Const(b)) if a == b => Some(self),
            (
                Complex::App {
                    function: f,
                    terms: a,
                },
                Complex::App {
                    function: g,
                    terms: b,
                },
            ) if f == g => self.terms(a, b),
            _ => None,
        }
    }

    /// Maps `from` to `to`, unless `from` is already mapped elsewhere or `to` already taken.
    fn pair(mut self, from: &Var, to: &Var) -> Option<Self> {
        match self.0.get(from) {
            Some(image) => (image == to).then_some(self),
            None if self.0.values().any(|image| image == to) => None,
            None => {
                self.0.insert(from.clone(), to.clone());
                Some(self)
            }
        }
    }

    fn apply(&self, gnf: &GNF) -> GNF {
        gnf.rename_var(&|v: &Var| self.0.get(v).cloned().unwrap_or_else(|| v.clone()))
    }
}

/// What a literal can only be matched onto: an atom of the same predicate and arity, or an
/// equation.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Kind<'a> {
    Atom(&'a Pred, usize),
    Equals,
}

impl<'a> Kind<'a> {
    fn of(literal: &'a Atomic<Complex>) -> Self {
        match literal {
            Atomic::Atom(atom) => Kind::Atom(&atom.predicate, atom.terms.len()),
            Atomic::Equals(_) => Kind::Equals,
        }
    }

    /// The literals of `body` grouped by kind.
    fn group(body: &'a PCF) -> BTreeMap<Self, Vec<&'a Atomic<Complex>>> {
        let mut groups: BTreeMap<Self, Vec<&'a Atomic<Complex>>> = BTreeMap::new();
        for literal in body.iter() {
            groups.entry(Kind::of(literal)).or_default().push(literal);
        }
        groups
    }
}

/// Merges the sequents whose heads share a witness, so that the conjuncts of a Skolemized head
/// share their existential again. Skolem symbols are per formula, so the sequents linked by
/// common witnesses are exactly the split heads of one formula; by [`Witnesses::classify`] they
/// share one body up to a renaming of variables. Sequents without a witness in the head are
/// kept as they are.
fn merge_witnessed(sequents: Vec<GNF>, witnesses: &Witnesses) -> Vec<GNF> {
    let (witnessed, mut plain): (Vec<GNF>, Vec<GNF>) = sequents
        .into_iter()
        .partition(|gnf| !witnesses.of(gnf.head()).is_empty());
    let mut links: UnionFind<usize> = UnionFind::default();
    let mut first: HashMap<&Witness, usize> = HashMap::new();
    for (i, gnf) in witnessed.iter().enumerate() {
        for witness in witnesses.of(gnf.head()) {
            let j = *first.entry(witness).or_insert(i);
            links.union(i, j);
        }
    }
    let mut groups: Vec<(usize, GNF)> = Vec::new();
    for (i, gnf) in witnessed.into_iter().enumerate() {
        let root = links.find(i);
        match groups.iter_mut().find(|(r, _)| *r == root) {
            Some((_, merged)) => {
                let renaming = Renaming::onto(&gnf, merged.body())
                    .expect("sequents sharing a witness share a body up to renaming");
                let head = merged
                    .head()
                    .cross_union(renaming.apply(&gnf).head())
                    .simplify();
                *merged = GNF::from((merged.body().clone(), head));
            }
            None => groups.push((root, gnf)),
        }
    }
    plain.extend(groups.into_iter().map(|(_, gnf)| gnf));
    plain
}

impl PreProcessor for RelPreProcessor {
    type Sequent = RelSequent;
    type Model = RelModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        let skolems = RefCell::new(Skolems::default());
        let sequents: Vec<GNF> = theory
            .iter()
            .map(|f| {
                f.snf_with(&mut || skolems.borrow_mut().constant(), &mut || {
                    skolems.borrow_mut().function()
                })
            })
            .flat_map(|f| f.gnf())
            .collect();

        let witnesses = Witnesses::classify(&sequents, &skolems.into_inner());
        let sequents = merge_witnessed(sequents, &witnesses);

        let geometric: Theory<GNF> = sequents.into_iter().collect();
        let signature = geometric.signature().expect("invalid theory signature");
        let mut model = RelModel::new(&signature, &witnesses);
        let sequents = geometric
            .formulae()
            .iter()
            .filter_map(|gnf| RelSequent::compile(gnf, model.database_mut(), &witnesses))
            .collect();
        (sequents, model)
    }
}

#[cfg(test)]
mod tests {
    use super::super::sequent::{Function, SymbolicAtom};
    use super::*;

    fn gnf(text: &str) -> GNF {
        GNF::try_from(text.parse::<FOF>().unwrap()).unwrap()
    }

    #[test]
    fn renaming_maps_a_body_onto_its_variant() {
        let target = gnf("P(x, y) & Q(y) -> R(f(x))");
        assert!(Renaming::onto(&gnf("Q(w) & P(z, w) -> S(f(z))"), target.body()).is_some());
        assert!(Renaming::onto(&gnf("Q(z) & P(z, w) -> S(f(z))"), target.body()).is_none());
    }

    #[test]
    fn renaming_matches_wide_bodies_quickly() {
        let wide = |last: &str| {
            let rs: Vec<String> = (1..=12).map(|i| format!("R(x{})", i)).collect();
            gnf(&format!("{} & {} -> Q(c)", rs.join(" & "), last))
        };
        let start = std::time::Instant::now();
        assert!(Renaming::onto(&wide("S(y)"), wide("T(y)").body()).is_none());
        assert!(Renaming::onto(&wide("S(y)"), wide("S(z)").body()).is_some());
        assert!(start.elapsed() < std::time::Duration::from_secs(1));
    }

    #[test]
    fn renaming_never_captures_a_head_variable() {
        let target = gnf("P(x) -> Q(f(x))");
        assert!(Renaming::onto(&gnf("P(z) -> R(f(x))"), target.body()).is_none());
    }

    #[test]
    fn a_user_constant_named_like_a_skolem_constant_is_a_function() {
        let fact = Pred::from("P").app(vec![Complex::from(Const::from("c#9"))]);
        let theory: Theory<FOF> = std::iter::once(FOF::from(fact)).collect();
        let (sequents, _) = RelPreProcessor.pre_process(&theory);
        assert!(matches!(
            &sequents[0].branches[0].atoms[0],
            SymbolicAtom::Function {
                function: Function::Symbol(Symbol::Const(c)),
                ..
            } if c.name() == "c#9"
        ));
    }
}
