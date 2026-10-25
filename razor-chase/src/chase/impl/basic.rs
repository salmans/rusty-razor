//! Provides a "basic" implementation of the chase.
//!
//! This implementation is used as a reference for the correctness of other implementations
//! of the [chase].
//!
//! **Note**: The performance of `chase::impl::basic` is not a concern.
//!
//! [chase]: crate::chase#the-chase
//!
use crate::chase::*;
use either::Either;
use itertools::Itertools;
use razor_fol::{
    syntax::{
        formula::{Atomic, Equals},
        term::Complex,
        Const, Formula, Func, Var, FOF,
    },
    transform::{Geometrization, Symbols, ToGNF, GNF},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt,
};

// Is a *positive* literal apearing in the body and the head of sequents
pub type Literal = Atomic<Complex>;

/// Is a straight forward implementation for [`WitnessTerm`], where elements are of type
/// [`E`].
///
/// [`WitnessTerm`]: crate::chase::WitnessTerm
/// [`E`]: crate::chase::E
#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum BasicWitnessTerm {
    /// Wraps an instance of [`E`], witnessing itself.
    ///
    /// [`E`]: crate::chase::E
    Elem(E),

    /// Wraps an instance of [`Const`] as a witness term.
    ///
    /// [`Const`]: razor_fol::syntax::Const
    Const(Const),

    /// Corresponds to a composite witness term, made by applying an instance of [`Func`]
    /// to a list of
    /// witness terms.
    ///
    /// [`Func`]: razor_fol::syntax::Func
    App { function: Func, terms: Vec<Self> },

    /// Corresponds to the element that a [`Witness`] names for the witness terms of the
    /// universals its existential depends on.
    Witness { witness: Witness, terms: Vec<Self> },
}

impl BasicWitnessTerm {
    /// Given a `term` and an assignment function `assign` from variables of the term to witness
    /// terms of a [`Model`], constructs a [`WitnessTerm`].
    fn witness(term: &Complex, assign: &impl Fn(&Var) -> Self) -> Self {
        match term {
            Complex::Const(c) => Self::Const(c.clone()),
            Complex::Var(v) => assign(v),
            Complex::App { function, terms } => {
                let terms = terms.iter().map(|t| Self::witness(t, assign)).collect();
                Self::App {
                    function: function.clone(),
                    terms,
                }
            }
        }
    }

    /// Builds a term by applying `function` on `args` as arguments.
    pub fn apply(function: Func, terms: Vec<Self>) -> Self {
        BasicWitnessTerm::App { function, terms }
    }

    /// The arguments of `self`: none for an element or a constant.
    fn terms(&self) -> &[Self] {
        match self {
            Self::Elem(_) | Self::Const(_) => &[],
            Self::App { terms, .. } | Self::Witness { terms, .. } => terms,
        }
    }

    /// `self` with `terms` as its arguments; an element or a constant has none to replace.
    fn with_terms(&self, terms: Vec<Self>) -> Self {
        match self {
            Self::Elem(_) | Self::Const(_) => self.clone(),
            Self::App { function, .. } => Self::App {
                function: function.clone(),
                terms,
            },
            Self::Witness { witness, .. } => Self::Witness {
                witness: *witness,
                terms,
            },
        }
    }
}

impl WitnessTerm for BasicWitnessTerm {
    type ElementType = E;
}

impl fmt::Display for BasicWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Elem(e) => write!(f, "{}", e),
            Self::Const(c) => write!(f, "{}", c),
            Self::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
            Self::Witness { witness, terms } if terms.is_empty() => write!(f, "{}", witness),
            Self::Witness { witness, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", witness, ts.join(", "))
            }
        }
    }
}

impl fmt::Debug for BasicWitnessTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl From<Const> for BasicWitnessTerm {
    fn from(constant: Const) -> Self {
        Self::Const(constant)
    }
}

impl From<&Const> for BasicWitnessTerm {
    fn from(constant: &Const) -> Self {
        Self::from(constant.clone())
    }
}

impl From<E> for BasicWitnessTerm {
    fn from(element: E) -> Self {
        BasicWitnessTerm::Elem(element)
    }
}

impl From<&E> for BasicWitnessTerm {
    fn from(element: &E) -> Self {
        Self::from(*element)
    }
}

/// Is a basic instance of [`Model`] with terms of type [`WitnessTerm`].
///
/// [`Model`]: crate::chase::Model
pub struct BasicModel {
    /// Is a unique identifier for this model.
    id: u64,

    /// Keeps track of the next index to assign to a new element of this model.
    element_index: i32,

    /// Maps *flat* witness terms to elements of this model.
    ///
    /// **Hint**: Flat (witness) terms are terms that do not contain any composite sub-terms,
    /// consisting of functions applications.
    rewrites: BTreeMap<BasicWitnessTerm, E>,

    /// Contains a list of relational facts that are true in this model.
    facts: BTreeSet<Observation<BasicWitnessTerm>>,

    /// Maintains a list of rewrite rules from elements to elements with which they have been
    /// identified.
    ///
    /// **Explanation**: When augmenting a model with a list of [observations] (such as observations
    /// that come from the head of a sequent being evaluated), identity observations are
    /// augmented by collapsing elements, that is, removing one element in favor of the other one.
    /// However, other augmenting observations may still point to an element that was removed as a
    /// result of augmenting an `Identity` observation.
    ///
    /// `equality_history` is used to keep track of identifications of elements temporarily during
    /// the time a model is being augmented in a [chase-step]. `equality_history` in a model becomes
    /// outdated after the [chase-step] ends.
    ///
    /// [observations]: crate::chase::Observation
    /// [chase-step]: crate::chase#chase-step
    equality_history: HashMap<E, E>,

    /// The Skolem depth of every element: the depth of the shallowest term that names it.
    depths: BTreeMap<E, u32>,
}

impl BasicModel {
    /// Creates a new empty instance of this model.
    pub fn new() -> Self {
        Self {
            id: rand::random(),
            element_index: 0,
            rewrites: BTreeMap::new(),
            facts: BTreeSet::new(),
            equality_history: HashMap::new(),
            depths: BTreeMap::new(),
        }
    }

    /// Returns references to the elements of this model.
    fn domain_ref(&self) -> Vec<&E> {
        self.rewrites.values().unique().collect()
    }

    /// Returns a reference to an element witnessed by the given witness term.
    fn element_ref(&self, witness: &BasicWitnessTerm) -> Option<&E> {
        match witness {
            BasicWitnessTerm::Elem(element) => {
                self.domain_ref().into_iter().find(|e| e.eq(&element))
            }
            _ => {
                let terms: Option<Vec<BasicWitnessTerm>> = witness
                    .terms()
                    .iter()
                    .map(|t| self.element_ref(t).map(|e| (*e).into()))
                    .collect();
                self.rewrites.get(&witness.with_terms(terms?))
            }
        }
    }

    /// Applies the rewrite rules in `equality_history` of `self` to reduce an element to
    /// the representative element of the equational class to which it belongs.
    fn history(&self, element: &E) -> E {
        let mut result = element;
        let mut next;
        while {
            next = self.equality_history.get(result);
            next.is_some() && next.unwrap() != result
        } {
            result = next.unwrap()
        }

        *result
    }

    /// Creates a new element for the given `witness` and records that `witness` denotes the new
    /// element.
    fn new_element(&mut self, witness: BasicWitnessTerm) -> E {
        let element = E(self.element_index);
        self.element_index += 1;
        self.depths.insert(element, self.depth(&witness));
        self.rewrites.insert(witness, element);
        element
    }

    /// The Skolem depth of the element that `witness` denotes, or would denote once recorded:
    /// a constant has depth 0 and an application one more than its deepest argument.
    fn depth(&self, witness: &BasicWitnessTerm) -> u32 {
        if let Some(element) = self.element_ref(witness) {
            return self.depths[element];
        }
        match witness {
            BasicWitnessTerm::Elem(element) => self.depths[&self.history(element)],
            _ => self.depth_over(witness.terms()),
        }
    }

    /// The Skolem depth of an application to `terms`: one more than its deepest argument, or 0
    /// with none.
    fn depth_over(&self, terms: &[BasicWitnessTerm]) -> u32 {
        terms.iter().map(|t| self.depth(t) + 1).max().unwrap_or(0)
    }

    /// Lowers the depth of every element named by a term over a lowered element, and so on to a
    /// fixpoint. An element's depth is that of its shallowest name: after `f#0(e0) = e1` the
    /// entry `'c = e1` makes `e1` depth 0, and every `f(…, e1, …)` output one shallower.
    fn lower(&mut self, mut changed: Vec<E>) {
        while let Some(e) = changed.pop() {
            let entries: Vec<(u32, E)> = self
                .rewrites
                .iter()
                .filter(|(key, _)| key.terms().contains(&BasicWitnessTerm::Elem(e)))
                .map(|(key, out)| (self.depth_over(key.terms()), *out))
                .collect();
            for (depth, out) in entries {
                let current = self
                    .depths
                    .get_mut(&out)
                    .expect("every element has a depth");
                if depth < *current {
                    *current = depth;
                    changed.push(out);
                }
            }
        }
    }

    /// Would observing `observation` take `self` beyond `bound`? Every term that denotes no
    /// element yet counts as one new element of its own depth.
    fn exceeds<B: Bounder + ?Sized>(
        &self,
        bound: &B,
        observation: &Observation<BasicWitnessTerm>,
    ) -> bool {
        let terms = match observation {
            Observation::Fact { terms, .. } => terms.iter().collect(),
            Observation::Identity { left, right } => vec![left, right],
        };
        let new: Vec<&BasicWitnessTerm> = terms
            .into_iter()
            .filter(|t| self.element_ref(t).is_none())
            .collect();
        let size = self.domain_ref().len();
        new.iter()
            .enumerate()
            .any(|(index, t)| bound.admit(size + index, self.depth(t)) != Admission::Create)
    }

    /// Records the given `witness` in `self` and returns the element, denoted by
    /// `witness`.
    ///
    /// **Note**: `record` creates new elements that are denoted by `witness` and all sub-terms of
    /// `witness` and adds them to the domain of `self`.
    fn record(&mut self, witness: &BasicWitnessTerm) -> E {
        match witness {
            BasicWitnessTerm::Elem(element) => {
                let element = self.history(element);
                if self.domain().iter().any(|e| element.eq(e)) {
                    element
                } else {
                    unreachable!("missing element `{}`", element)
                }
            }
            _ => {
                let terms: Vec<BasicWitnessTerm> = witness
                    .terms()
                    .iter()
                    .map(|t| self.record(t).into())
                    .collect();
                let witness = witness.with_terms(terms);
                if let Some(e) = self.rewrites.get(&witness) {
                    *e
                } else {
                    self.new_element(witness)
                }
            }
        }
    }

    /// Replaces all instances of `from` with `to` in the `rewrite` of `self` and is used
    /// when augmenting the model with an `Identity` [`Observation`].
    ///
    /// **Note**: When augmenting a model with an `Identity`, we simply replace all instances of one
    /// side of the identity (i.e., the element denoted by one [witness term]) with the other
    /// one.
    ///
    /// Returns the pairs of elements that two rewrites, now over the same term, denote: by
    /// congruence they must be identified too.
    ///
    /// [`Observation`]: crate::chase::Observation
    /// [witness term]: crate::chase::WitnessTerm
    fn reduce_rewrites(&mut self, from: &E, to: &E) -> Vec<(E, E)> {
        let mut congruent = Vec::new();
        let mut new_rewrite: BTreeMap<BasicWitnessTerm, E> = BTreeMap::new();
        self.rewrites.iter().for_each(|(k, v)| {
            // k is a flat term over elements:
            let terms = k
                .terms()
                .iter()
                .map(|t| match t {
                    BasicWitnessTerm::Elem(element) if element == to => {
                        BasicWitnessTerm::Elem(*from)
                    }
                    _ => t.clone(),
                })
                .collect();
            let key = k.with_terms(terms);

            let value = if v == to { *from } else { *v };
            if let Some(other) = new_rewrite.insert(key, value) {
                if other != value {
                    congruent.push((other, value));
                }
            }
        });
        self.rewrites = new_rewrite;
        congruent
    }

    /// Replaces all instances of `from` with `to` in the `facts` of `self` and is used
    /// when augmenting the model with an `Identity` [`Observation`].
    ///
    /// **Note**: When augmenting a model with an identity, we simply replace all instances of one
    /// side of the identity (i.e., the element corresponding to its [witness term]) with the other
    /// one.
    ///
    /// [`Observation`]: crate::chase::Observation
    /// [witness term]: crate::chase::WitnessTerm
    fn reduce_facts(&mut self, from: &E, to: &E) {
        self.facts = self
            .facts
            .iter()
            .map(|f| {
                if let Observation::Fact {
                    ref relation,
                    ref terms,
                } = f
                {
                    let terms: Vec<BasicWitnessTerm> = terms
                        .iter()
                        .map(|t| {
                            if let BasicWitnessTerm::Elem(element) = t {
                                if element == to {
                                    (*from).into()
                                } else {
                                    (*t).clone()
                                }
                            } else {
                                (*t).clone() // should never happen
                            }
                        })
                        .collect();
                    Observation::Fact {
                        relation: relation.clone(),
                        terms,
                    }
                } else {
                    f.clone() // should never happen
                }
            })
            .collect();
    }

    /// Augments `self` with `observation`, making `observation` true in `self`.
    fn observe(&mut self, observation: &Observation<BasicWitnessTerm>) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<BasicWitnessTerm> =
                    terms.iter().map(|t| self.record(t).into()).collect();
                let observation = Observation::Fact {
                    relation: relation.clone(),
                    terms,
                };
                self.facts.insert(observation);
            }
            Observation::Identity { left, right } => {
                let left = self.record(left);
                let right = self.record(right);
                self.merge(left, right);
            }
        }
    }

    /// Identifies `a` and `b`, keeping the older element, and then every pair of elements that
    /// congruence identifies in turn, until no two rewrites of one term disagree.
    fn merge(&mut self, a: E, b: E) {
        let mut pending = vec![(a, b)];
        let mut winners = Vec::new();
        while let Some((a, b)) = pending.pop() {
            let (a, b) = (self.history(&a), self.history(&b));
            if a == b {
                continue;
            }
            let (from, to) = if a > b { (b, a) } else { (a, b) };
            pending.extend(self.reduce_rewrites(&from, &to));
            self.reduce_facts(&from, &to);
            // the merged element is denoted by the terms of both, so it is the shallower:
            let depth = self.depths.remove(&to).expect("every element has a depth");
            self.depths.entry(from).and_modify(|d| *d = (*d).min(depth));
            self.equality_history.insert(to, from);
            winners.push(from);
        }
        let winners = winners.iter().map(|e| self.history(e)).collect();
        self.lower(winners);
    }

    /// Returns true if `observation` is true in `self`; otherwise, returns false.
    fn is_observed(&self, observation: &Observation<BasicWitnessTerm>) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<&E>> = terms.iter().map(|t| self.element_ref(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    false
                } else {
                    let terms: Vec<BasicWitnessTerm> =
                        terms.into_iter().map(|e| (*e.unwrap()).into()).collect();
                    let obs = Observation::Fact {
                        relation: relation.clone(),
                        terms,
                    };
                    self.facts.iter().any(|f| obs.eq(f))
                }
            }
            Observation::Identity { left, right } => {
                let left = self.element(left);
                left.is_some() && left == self.element(right)
            }
        }
    }
}

impl Default for BasicModel {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for BasicModel {
    fn clone(&self) -> Self {
        Self {
            id: rand::random(),
            element_index: self.element_index,
            rewrites: self.rewrites.clone(),
            facts: self.facts.clone(),
            // In the `basic` implementation, a model is cloned after being processed in a
            // chase-step, so its `equality_history` does not need to persist after cloning it.
            equality_history: HashMap::new(),
            depths: self.depths.clone(),
        }
    }
}

impl Model for BasicModel {
    type TermType = BasicWitnessTerm;

    fn get_id(&self) -> u64 {
        self.id
    }

    fn domain(&self) -> Vec<E> {
        self.domain_ref().into_iter().cloned().collect()
    }

    fn facts(&self) -> Vec<Observation<Self::TermType>> {
        self.facts.clone().into_iter().sorted().dedup().collect()
    }

    fn witness(&self, element: &E) -> Vec<BasicWitnessTerm> {
        self.rewrites
            .iter()
            .filter(|(_, e)| *e == element)
            .map(|(t, _)| t)
            .cloned()
            .collect()
    }

    fn element(&self, witness: &BasicWitnessTerm) -> Option<E> {
        self.element_ref(witness).cloned()
    }

    fn finalize(self) -> Self {
        self
    }
}

impl fmt::Debug for BasicModel {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self.domain().into_iter().map(|e| e.to_string()).collect();
        let elements: Vec<String> = self
            .domain()
            .iter()
            .sorted()
            .map(|e| {
                let witnesses: Vec<String> =
                    self.witness(e).iter().map(|w| w.to_string()).collect();
                let witnesses = witnesses.into_iter().sorted();
                format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
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

/// Is represented by a list of [`Literal`]s in the body and a list of [`BasicDisjunct`]s in the
/// head.
#[derive(Clone)]
pub struct BasicSequent {
    /// Is the list of free variables in the sequent and is used for memoization.
    pub free_vars: Vec<Var>,

    /// Represents the body of the sequent as a list of [`Literal`]s. The literals in
    /// `body_literals` are assumed to be conjoined.
    ///
    /// **Note**: See [here](crate::chase#background) for more information about the structure
    /// of geometric sequents.
    pub body: Vec<Literal>,

    /// Represents the head of the sequent as a list of disjuncts.
    ///
    /// **Note**: See [here](crate::chase#background) for more information about the structure
    /// of geometric sequents.
    pub head: Vec<BasicDisjunct>,

    // other fields:
    body_fof: FOF,
    head_fof: FOF,
}

impl BasicSequent {
    /// Reads `sequent`, introducing one witness from `witnesses` for every existential of its
    /// head, in order, over its dependencies ([`GNF::dependencies`]).
    fn new(sequent: &GNF, witnesses: &mut Witnesses) -> Self {
        let free_vars: Vec<Var> = sequent.free_vars().into_iter().cloned().collect();
        let body = sequent.body().iter().cloned().collect();
        let head = sequent
            .head()
            .iter()
            .map(|disjunct| {
                let scope = sequent.dependencies(disjunct);
                let origins: Vec<Origin> = disjunct
                    .existentials()
                    .iter()
                    .map(|v| witnesses.fresh(v.clone(), scope.clone()))
                    .collect();
                let occurring = disjunct.atoms().free_vars();
                let unmentioned = origins
                    .iter()
                    .filter(|o| !occurring.contains(&&o.existential))
                    .map(|o| {
                        let v = Complex::from(o.existential.clone());
                        Literal::from(Equals {
                            left: v.clone(),
                            right: v,
                        })
                    });
                let literals = disjunct
                    .atoms()
                    .iter()
                    .cloned()
                    .chain(unmentioned)
                    .collect();
                BasicDisjunct { literals, origins }
            })
            .collect();

        Self {
            free_vars,
            body,
            head,
            body_fof: sequent.body().into(),
            head_fof: sequent.head().into(),
        }
    }
}

impl fmt::Display for BasicSequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let body: Vec<String> = self.body.iter().map(|l| l.to_string()).collect();
        let head: Vec<String> = self.head.iter().map(|d| d.to_string()).collect();
        write!(f, "[{}] -> [{}]", body.join(", "), head.join(", "))
    }
}

/// A disjunct of a sequent's head: conjoined [`Literal`]s over the universals of the sequent
/// and the existentials of the disjunct, each existential named by the witness of its
/// [`Origin`]. The evaluator creates the element of a witness when the disjunct must hold, and
/// an existential that occurs in no atom keeps the equation `y = y`, so its element is still
/// created.
#[derive(Clone)]
pub struct BasicDisjunct {
    /// The conjoined literals of the disjunct.
    pub literals: Vec<Literal>,

    /// The witnesses of the existentials of the disjunct.
    pub origins: Vec<Origin>,
}

impl BasicDisjunct {
    /// The origin of `variable` when it is an existential of the disjunct.
    fn origin(&self, variable: &Var) -> Option<&Origin> {
        self.origins.iter().find(|o| &o.existential == variable)
    }

    /// The witness term of `variable` when the universals denote the elements `assign` gives
    /// them: an existential is its witness applied to the elements of its arguments.
    fn term(&self, variable: &Var, assign: &impl Fn(&Var) -> E) -> BasicWitnessTerm {
        match self.origin(variable) {
            Some(origin) => BasicWitnessTerm::Witness {
                witness: origin.witness,
                terms: origin.args.iter().map(|v| assign(v).into()).collect(),
            },
            None => assign(variable).into(),
        }
    }

    /// `term` with every existential displayed as its witness applied to its arguments.
    fn show(&self, term: &Complex) -> String {
        match term {
            Complex::Var(v) => match self.origin(v) {
                Some(origin) if origin.args.is_empty() => origin.witness.to_string(),
                Some(origin) => format!("{}({})", origin.witness, origin.args.iter().join(", ")),
                None => v.to_string(),
            },
            Complex::Const(c) => c.to_string(),
            Complex::App { function, terms } => {
                format!(
                    "{}({})",
                    function,
                    terms.iter().map(|t| self.show(t)).join(", ")
                )
            }
        }
    }
}

impl fmt::Display for BasicDisjunct {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let literals: Vec<String> = self
            .literals
            .iter()
            .map(|l| match l {
                Atomic::Atom(atom) => format!(
                    "{}({})",
                    atom.predicate,
                    atom.terms.iter().map(|t| self.show(t)).join(", ")
                ),
                Atomic::Equals(equals) => {
                    format!("{} = {}", self.show(&equals.left), self.show(&equals.right))
                }
            })
            .collect();
        write!(f, "[{}]", literals.join(", "))
    }
}

impl Sequent for BasicSequent {
    fn body(&self) -> FOF {
        self.body_fof.clone()
    }

    fn head(&self) -> FOF {
        self.head_fof.clone()
    }
}

/// A simple instance of [`PreProcessor`] that converts the input theory to a vector of [`Sequent`] following
/// the conversion to geometric normal form, removing existentials by its [`Geometrization`].
/// Also provides the empty [`Model`];
///
/// [`PreProcessor`]: crate::chase::PreProcessor
#[derive(Clone, Copy, Debug, Default)]
pub struct BasicPreProcessor {
    geometrization: Geometrization,
}

impl BasicPreProcessor {
    /// A pre-processor that removes existentials by `geometrization`.
    pub fn new(geometrization: Geometrization) -> Self {
        Self { geometrization }
    }
}

impl PreProcessor for BasicPreProcessor {
    type Sequent = BasicSequent;
    type Model = BasicModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        let mut symbols = Symbols::default();
        let gnfs: Vec<GNF> = theory
            .iter()
            .flat_map(|f| f.gnf_with(self.geometrization, &mut symbols))
            .collect();
        let mut witnesses = Witnesses::new(&symbols);
        let sequents = gnfs
            .iter()
            .map(|sequent| BasicSequent::new(sequent, &mut witnesses))
            .collect();
        (sequents, BasicModel::new())
    }
}

/// Is a reference implementation of [`Evaluator`] for evaluating a basic [`Sequent`] in a basic [`Model`]
/// within a [chase-step].
///
/// It honours every [`Bounder`], but never reuses elements: as the oracle it builds the partial
/// model, so [`Admission::Reuse`] is treated as [`Admission::Overflow`].
///
/// [`Evaluator`]: crate::chase::Evaluator
/// [chase-step]: crate::chase#chase-step
pub struct BasicEvaluator;

impl<'s, Stg: Strategy<&'s BasicSequent>> Evaluator<'s, Stg> for BasicEvaluator {
    type Sequent = BasicSequent;
    type Model = BasicModel;

    fn evaluate<B: Bounder + ?Sized>(
        &self,
        initial_model: &BasicModel,
        strategy: &mut Stg,
        bound: &B,
    ) -> Option<EvaluateResult<BasicModel>> {
        let domain: Vec<&E> = initial_model.domain_ref().clone();
        let domain_size = domain.len();
        for sequent in strategy {
            let vars = &sequent.free_vars;
            let vars_size = vars.len();
            if domain_size == 0 && vars_size > 0 {
                continue; // empty models can only be extended with sequents with no free variables.
            }

            // maintain a list of indices into the model elements to which variables are mapped
            let mut assignment: Vec<usize> = std::iter::repeat_n(0, vars_size).collect();

            // try all the variable assignments to the elements of the model
            // (notice the do-while pattern)
            while {
                // construct a map from variables to elements
                let mut assignment_map: HashMap<&Var, E> = HashMap::new();
                for (i, item) in assignment.iter().enumerate().take(vars_size) {
                    assignment_map.insert(vars.get(i).unwrap(), *(*domain.get(*item).unwrap()));
                }
                // construct a "characteristic function" for the assignment map
                let assignment_func = |v: &Var| *assignment_map.get(v).unwrap();

                // build body and head observations
                let body: Vec<Observation<BasicWitnessTerm>> = sequent
                    .body
                    .iter()
                    .map(|l| observe_literal(l, &|v| assignment_func(v).into()))
                    .collect();
                let head: Vec<Vec<Observation<BasicWitnessTerm>>> = sequent
                    .head
                    .iter()
                    .map(|d| {
                        d.literals
                            .iter()
                            .map(|l| observe_literal(l, &|v| d.term(v, &assignment_func)))
                            .collect()
                    })
                    .collect();

                // if all body observations are true in the model but not all the head observations
                // are true, extend the model:
                if body.iter().all(|o| initial_model.is_observed(o))
                    && !head
                        .iter()
                        .any(|os| os.iter().all(|o| initial_model.is_observed(o)))
                {
                    if head.is_empty() {
                        return None; // the chase fails if the head is empty (false)
                    } else {
                        let extend = make_extend(bound, initial_model);
                        let models: Vec<Either<BasicModel, BasicModel>> =
                            head.iter().map(extend).collect();

                        let result = EvaluateResult::from(models);
                        if !result.empty() {
                            // this evaluator instantiates the first matching sequent with the first
                            // matching assignment
                            return Some(result);
                        }
                    }
                }

                // try the next variable assignment
                domain_size > 0 && next_assignment(&mut assignment, domain_size - 1)
            } {}
        }
        Some(EvaluateResult::new()) // if none of the assignments apply, the model is complete already
    }
}

// Returns a closure that returns a cloned extension of the given model, extended by a given set of
// observations within `bound`: a model wrapped in `Either::Right` has reached `bound` and misses
// the observations beyond it, while a model wrapped in `Either::Left` has not.
fn make_extend<'m, B: Bounder + ?Sized>(
    bound: &'m B,
    model: &'m BasicModel,
) -> impl FnMut(&'m Vec<Observation<BasicWitnessTerm>>) -> Either<BasicModel, BasicModel> {
    move |os: &Vec<Observation<BasicWitnessTerm>>| {
        let mut model = model.clone();
        let mut modified = false;
        os.iter().for_each(|o| {
            if model.exceeds(bound, o) {
                if !model.is_observed(o) {
                    modified = true;
                }
            } else if !model.is_observed(o) {
                model.observe(o);
            }
        });
        if modified {
            Either::Right(model)
        } else {
            Either::Left(model)
        }
    }
}

// The observation of `lit` when its variables denote the witness terms `assign` gives them.
fn observe_literal(
    lit: &Literal,
    assign: &impl Fn(&Var) -> BasicWitnessTerm,
) -> Observation<BasicWitnessTerm> {
    match lit {
        Atomic::Atom(this) => {
            let terms = this
                .terms
                .iter()
                .map(|t| BasicWitnessTerm::witness(t, assign))
                .collect();
            Observation::Fact {
                relation: Rel::from(this.predicate.name()),
                terms,
            }
        }
        Atomic::Equals(this) => {
            let left = BasicWitnessTerm::witness(&this.left, assign);
            let right = BasicWitnessTerm::witness(&this.right, assign);
            Observation::Identity { left, right }
        }
    }
}

// Implements a counter to enumerate all the possible assignments of a domain of elements to free
// variables of a sequent. It mutates the given a list of indices, corresponding to mapping of each
// position to an element of a domain to the next assignment. Returns true if a next assignment
// exists and false otherwise.
fn next_assignment(vec: &mut [usize], last: usize) -> bool {
    for item in vec.iter_mut() {
        if *item != last {
            *item += 1;
            return true;
        } else {
            *item = 0;
        }
    }
    false
}

#[cfg(test)]
mod test_basic {
    use super::*;
    use crate::chase::{
        chase_all, chase_step, scheduler::FIFO, strategy::Linear, Depth, DepthMode, DomainSize,
        Scheduler, Unbounded,
    };
    use crate::test_prelude::*;
    use std::iter::FromIterator;

    // Witness Elements
    pub fn _e_0() -> BasicWitnessTerm {
        e_0().into()
    }

    pub fn _e_1() -> BasicWitnessTerm {
        e_1().into()
    }

    pub fn _e_2() -> BasicWitnessTerm {
        e_2().into()
    }

    pub fn _e_3() -> BasicWitnessTerm {
        e_3().into()
    }

    pub fn _e_4() -> BasicWitnessTerm {
        e_4().into()
    }

    // Witness Constants
    pub fn _a_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_a())
    }

    pub fn _b_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_b())
    }

    pub fn _c_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_c())
    }

    pub fn _d_() -> BasicWitnessTerm {
        BasicWitnessTerm::Const(_d())
    }

    #[test]
    fn test_witness_const() {
        assert_eq!(_a_(), _a().into());
        assert_eq!("'a", _a_().to_string());
    }

    #[test]
    fn test_observation() {
        assert_eq!("<R(e#0)>", _R_().app1(_e_0()).to_string());
        assert_eq!(
            "<R(e#0, e#1, e#2)>",
            _R_().app3(_e_0(), _e_1(), _e_2()).to_string()
        );
        assert_eq!("<e#0 = e#1>", _e_0().equals(_e_1()).to_string());
    }

    #[test]
    fn test_empty_model() {
        let model = BasicModel::new();
        let empty_domain: Vec<E> = Vec::new();
        let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
        assert_eq!(empty_domain, model.domain());
        assert_eq_sets(&empty_facts, &model.facts());
    }

    #[test]
    fn test_witness_app() {
        let f_0 = BasicWitnessTerm::apply(f(), vec![]);
        assert_eq!("f()", f_0.to_string());
        assert_eq!(
            "f('c)",
            BasicWitnessTerm::apply(f(), vec![_c_()]).to_string()
        );
        let g_0 = BasicWitnessTerm::apply(g(), vec![]);
        assert_eq!(
            "f(g())",
            BasicWitnessTerm::apply(f(), vec![g_0]).to_string()
        );
        assert_eq!(
            "f('c, g('d))",
            BasicWitnessTerm::apply(f(), vec![_c_(), BasicWitnessTerm::apply(g(), vec![_d_()])])
                .to_string()
        );
    }

    #[test]
    fn test_observe() {
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app0());
            assert_eq_sets(&Vec::from_iter(vec![_R_().app0()]), &model.facts());
            assert!(model.is_observed(&_R_().app0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(_c_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            assert_eq_sets(&Vec::from_iter(vec![_R_().app1(_e_0())]), &model.facts());
            assert!(model.is_observed(&_R_().app1(_c_())));
            assert!(model.is_observed(&_R_().app1(_e_0())));
            assert!(!model.is_observed(&_R_().app1(_e_1())));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
            assert_eq_sets(&empty_facts, &model.facts());
            assert_eq_sets(&Vec::from_iter(vec![_a_(), _b_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_a_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            let empty_facts: Vec<Observation<BasicWitnessTerm>> = Vec::new();
            assert_eq_sets(&empty_facts, &model.facts());
            assert_eq_sets(&Vec::from_iter(vec![_a_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_P_().app1(_a_()));
            model.observe(&_Q_().app1(_b_()));
            model.observe(&_a_().equals(_b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_P_().app1(_e_0()), _Q_().app1(_e_0())]),
                &model.facts(),
            );
            assert!(model.is_observed(&_P_().app1(_e_0())));
            assert!(model.is_observed(&_P_().app1(_a_())));
            assert!(model.is_observed(&_P_().app1(_b_())));
            assert!(model.is_observed(&_Q_().app1(_e_0())));
            assert!(model.is_observed(&_Q_().app1(_a_())));
            assert!(model.is_observed(&_Q_().app1(_b_())));
            assert_eq_sets(&Vec::from_iter(vec![_a_(), _b_()]), &model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(BasicWitnessTerm::apply(f(), vec![_c_()])));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1()]), &model.domain());
            assert_eq_sets(&Vec::from_iter(vec![_R_().app1(_e_1())]), &model.facts());
            assert!(model.is_observed(&_R_().app1(_e_1())));
            assert!(model.is_observed(&_R_().app1(BasicWitnessTerm::apply(f(), vec![_c_()]))));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(f(), vec![_e_0()])]),
                &model.witness(&e_1()),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(_a_(), _b_()));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app2(_e_0(), _e_1())]),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app2(_e_0(), _e_1())));
            assert!(!model.is_observed(&_R_().app2(_e_0(), _e_0())));
            assert_eq_sets(&Vec::from_iter(vec![_a_()]), &model.witness(&e_0()));
            assert_eq_sets(&Vec::from_iter(vec![_b_()]), &model.witness(&e_1()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(
                BasicWitnessTerm::apply(f(), vec![_c_()]),
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_c_()])]),
            ));
            assert_eq_sets(&Vec::from_iter(vec![e_0(), e_1(), e_2()]), &model.domain());
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app2(_e_1(), _e_2())]),
                &model.facts(),
            );
            assert!(model.is_observed(&_R_().app2(_e_1(), _e_2())));
            assert!(model.is_observed(&_R_().app2(
                BasicWitnessTerm::apply(f(), vec![_c_()]),
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_c_()])])
            )));
            assert!(model
                .is_observed(&_R_().app(vec![BasicWitnessTerm::apply(f(), vec![_c_()]), _e_2()])));
            assert_eq_sets(&Vec::from_iter(vec![_c_()]), &model.witness(&e_0()));
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(f(), vec![_e_0()])]),
                &model.witness(&e_1()),
            );
            assert_eq_sets(
                &Vec::from_iter(vec![BasicWitnessTerm::apply(g(), vec![_e_1()])]),
                &model.witness(&e_2()),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app(vec![_a_(), _b_()]));
            model.observe(&_S_().app(vec![_c_(), _d_()]));
            assert_eq_sets(
                &Vec::from_iter(vec![e_0(), e_1(), e_2(), e_3()]),
                &model.domain(),
            );
            assert_eq_sets(
                &Vec::from_iter(vec![_R_().app2(_e_0(), _e_1()), _S_().app2(_e_2(), _e_3())]),
                &model.facts(),
            );
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app(vec![_a_(), BasicWitnessTerm::apply(f(), vec![_a_()])]));
            model.observe(&_S_().app(vec![_b_()]));
            model.observe(&_R_().app(vec![
                BasicWitnessTerm::apply(g(), vec![BasicWitnessTerm::apply(f(), vec![_a_()])]),
                _b_(),
            ]));
            model.observe(&_S_().app(vec![_c_()]));
            assert_eq_sets(
                &Vec::from_iter(vec![e_0(), e_1(), e_2(), e_3(), e_4()]),
                &model.domain(),
            );
            assert_eq_sets(
                &Vec::from_iter(vec![
                    _R_().app2(_e_0(), _e_1()),
                    _S_().app1(_e_4()),
                    _S_().app1(_e_2()),
                    _R_().app2(_e_3(), _e_2()),
                ]),
                &model.facts(),
            );
        }
    }

    #[test]
    #[should_panic]
    fn test_observe_missing_element() {
        let mut model = BasicModel::new();
        model.observe(&_R_().app1(_e_0()));
    }

    // The sequents of the theory of the single formula `text`.
    fn sequents(text: &str) -> Vec<BasicSequent> {
        let theory: Theory<FOF> = format!("{};", text).parse().unwrap();
        BasicPreProcessor::default().pre_process(&theory).0
    }

    #[test]
    fn test_build_sequent() {
        assert_debug_string("[]", sequents("true -> true"));
        assert_debug_string("[]", sequents("true -> true & true"));
        assert_debug_string("[]", sequents("true -> true | true"));
        assert_debug_string("[[] -> []]", sequents("true -> false"));
        assert_debug_string("[[] -> []]", sequents("true -> false & true"));
        assert_debug_string("[[] -> []]", sequents("true -> true & false"));
        assert_debug_string("[]", sequents("true -> true | false"));
        assert_debug_string("[]", sequents("true -> false | true"));
        assert_debug_string("[[P(x)] -> [[Q(x)]]]", sequents("P(x) -> Q(x)"));
        assert_debug_string(
            "[[P(x), Q(x)] -> [[Q(y)]]]",
            sequents("P(x) & Q(x) -> Q(y)"),
        );
        assert_debug_string(
            "[[P(x, z), Q(x)] -> [[Q(x)], [R(z)]], [P(x, z), Q(x)] -> [[Q(x)], [S(z)]]]",
            sequents("P(x, z) & Q(x) -> Q(x) | (R(z) & S(z))"),
        );
        assert_debug_string(
"[[D(x, y, z)] -> [[P(x)], [P(y)], [P(z)]], [D(x, y, z)] -> [[P(x)], [P(y)], [Q(z)]], [D(x, y, z)] -> [[P(x)], [Q(y)], [P(z)]], [D(x, y, z)] -> [[P(x)], [Q(y)], [Q(z)]], [D(x, y, z)] -> [[Q(x)], [P(y)], [P(z)]], [D(x, y, z)] -> [[Q(x)], [P(y)], [Q(z)]], [D(x, y, z)] -> [[Q(x)], [Q(y)], [P(z)]], [D(x, y, z)] -> [[Q(x)], [Q(y)], [Q(z)]]]",
            sequents("D(x, y, z) -> (P(x) & Q(x)) | (P(y) & Q(y)) | (P(z) & Q(z))"),
        );
    }

    #[test]
    fn existentials_become_witness_terms_over_the_universals() {
        assert_debug_string(
            "[[P(x)] -> [[Q(x, f#0(x))]]]",
            sequents("P(x) -> exists y. Q(x, y)"),
        );
        assert_debug_string("[[] -> [['c#0 = 'c#0]]]", sequents("exists y. y = y"));
    }

    fn run(theory: &Theory<FOF>) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor::default();
        let (sequents, init_model) = pre_processor.pre_process(theory);

        let evaluator = BasicEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();

        let mut scheduler = FIFO::new();
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, &Unbounded)
    }

    fn run_domain_bounded(theory: &Theory<FOF>, bound: usize) -> Vec<BasicModel> {
        let pre_processor = BasicPreProcessor::default();
        let (sequents, init_model) = pre_processor.pre_process(theory);
        let evaluator = BasicEvaluator;
        let strategy: Linear<_> = sequents.iter().collect();
        let mut scheduler = FIFO::new();
        let bound = DomainSize(bound);
        scheduler.add(init_model, strategy);
        chase_all(&mut scheduler, &evaluator, &bound)
    }

    #[test]
    fn depth_bound_reports_partial_models() {
        let theory: Theory<FOF> = "exists x. P(x); P(x) -> exists y. (R(x, y) & P(y));"
            .parse()
            .unwrap();
        for mode in [DepthMode::Pure, DepthMode::Reuse] {
            let (sequents, init_model) = BasicPreProcessor::default().pre_process(&theory);
            let strategy: Linear<_> = sequents.iter().collect();
            let mut scheduler = FIFO::new();
            scheduler.add(init_model, strategy);
            let bound = Depth { max: 2, mode };
            let mut complete = Vec::new();
            let mut incomplete = Vec::new();
            while !scheduler.empty() {
                chase_step(
                    &mut scheduler,
                    &BasicEvaluator,
                    &bound,
                    |m| complete.push(m),
                    |m| incomplete.push(m),
                );
            }
            assert!(complete.is_empty());
            assert_eq!(1, incomplete.len());
            assert_eq!(3, incomplete[0].domain().len());
        }
    }

    #[test]
    fn test_core() {
        std::fs::read_dir("../theories/core")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.extension().is_some_and(|e| e == "raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let expected: BTreeSet<String> =
                    read_file(path.with_extension("model").to_str().unwrap())
                        .split("\n-- -- -- -- -- -- -- -- -- --\n")
                        .filter(|s| !s.is_empty())
                        .map(Into::into)
                        .collect();
                let result: BTreeSet<_> = run(&theory).into_iter().map(print_basic_model).collect();
                assert_eq!(
                    expected,
                    result,
                    "invalid result for theory {}",
                    path.with_extension("").to_str().unwrap()
                );
            });
    }

    #[test]
    fn test_bounded() {
        std::fs::read_dir("../theories/bounded")
            .unwrap()
            .map(|item| item.unwrap().path())
            .filter(|path| path.extension().is_some_and(|e| e == "raz"))
            .for_each(|path| {
                let theory = read_theory_from_file(path.to_str().unwrap());
                let config = read_file(path.with_extension("config").to_str().unwrap())
                    .parse::<usize>()
                    .unwrap();
                let expected: BTreeSet<String> =
                    read_file(path.with_extension("model").to_str().unwrap())
                        .split("\n-- -- -- -- -- -- -- -- -- --\n")
                        .filter(|s| !s.is_empty())
                        .map(Into::into)
                        .collect();
                let result: BTreeSet<_> = run_domain_bounded(&theory, config)
                    .into_iter()
                    .map(print_basic_model)
                    .collect();
                assert_eq!(
                    expected,
                    result,
                    "invalid result for theory {}",
                    path.with_extension("").to_str().unwrap()
                );
            });
    }
}
