use super::syntax::{*, Term::*, Formula::*};
use std::collections::HashMap;
use std::cmp::Ordering::Equal;
use itertools::Itertools;

/// ## Substitution
/// A *substitution* is a function from variables to terms.
pub trait Substitution {
    fn apply(&self, v: &V) -> Term;
}

/// A function from Variable to Term is a substitution.
impl<F> Substitution for F
    where F: Fn(&V) -> Term {
    fn apply(&self, v: &V) -> Term {
        self(v)
    }
}

/// A map from Variable to Term is a substitution.
impl Substitution for HashMap<&V, Term> {
    fn apply(&self, v: &V) -> Term {
        self.get(v)
            .map(|t| t.clone())
            .unwrap_or(v.clone().into())
    }
}

/// ## VariableRenaming
/// A *variable renaming* function is a function from variables to variables
/// as a special case of substitution.
pub trait VariableRenaming {
    fn apply(&self, v: &V) -> V;
}

/// A function from Variable to Variable is a variable renaming.
impl<F> VariableRenaming for F
    where F: Fn(&V) -> V {
    fn apply(&self, v: &V) -> V {
        self(v)
    }
}

/// A map from Variable to Variable is a variable renaming.
impl VariableRenaming for HashMap<&V, V> {
    fn apply(&self, v: &V) -> V {
        self.get(v)
            .map(|var| var.clone())
            .unwrap_or(v.clone().into())
    }
}

/// TermBased is the trait of objects constructed from terms.
trait TermBased {
    /// Applies a term transformation function.
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self;

    /// Applies a variable renaming.
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self;

    /// Applies a substitution.
    fn substitute(&self, sub: &impl Substitution) -> Self;
}

impl TermBased for Term {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        f(self)
    }

    /// Applies a variable renaming on the term.
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => Term::var(renaming.apply(v)),
            App { function, terms } => {
                let terms = terms.iter()
                    .map(|t| t.rename_vars(renaming))
                    .collect();
                function.clone().app(terms)
            }
        }
    }

    /// Applies a substitution on the term.
    fn substitute(&self, sub: &impl Substitution) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => sub.apply(v),
            App { function, terms } => {
                let terms = terms.iter()
                    .map(|t| t.substitute(sub))
                    .collect();
                function.clone().app(terms)
            }
        }
    }
}

impl TermBased for Formula {
    #[inline]
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        match self {
            Top | Bottom => self.clone(),
            Atom { predicate, terms } => predicate.clone()
                .app(terms.iter()
                    .map(f)
                    .collect()
                ),
            Equals { left, right } => f(left).equals(f(right)),
            Not { formula } => not(formula.transform(f)),
            And { left, right } => left
                .transform(f)
                .and(right.transform(f)),
            Or { left, right } => left
                .transform(f)
                .or(right.transform(f)),
            Implies { left, right } => left
                .transform(f)
                .implies(right.transform(f)),
            Iff { left, right } => left
                .transform(f)
                .iff(right.transform(f)),
            Exists { variables, formula } => exists(
                variables.clone(),
                formula.transform(f),
            ),
            Forall { variables, formula } => forall(
                variables.clone(),
                formula.transform(f),
            ),
        }
    }

    /// Applies a variable renaming function on **free** variables of the formula.
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        // this does not rename bound variables of the formula
        self.transform(&|t: &Term| t.rename_vars(renaming))
    }

    /// Applies a substitution function on the **free** variables of the formula.
    fn substitute(&self, substitution: &impl Substitution) -> Self {
        self.transform(&|t: &Term| t.substitute(substitution))
    }
}

/// SkolemGenerator generates Skolem function names. To assure uniqueness of Skolem functions in a
/// theory, a unique instance of this generator must be used when Skolemizing the theory.
pub struct SkolemGenerator {
    prefix: String,
    index: i32,
}

impl SkolemGenerator {
    /// Creates a new SkolemGenerator with the default prefix `sk#`.
    pub fn new() -> SkolemGenerator {
        SkolemGenerator {
            prefix: "sk#".to_string(),
            index: 0,
        }
    }
    /// Creates a new SkolemGenerator with a custom `prefix`.
    pub fn new_with(prefix: &str) -> SkolemGenerator {
        SkolemGenerator {
            prefix: prefix.to_string(),
            index: 0,
        }
    }
    /// Returns the next Skolem function name.
    pub fn next(&mut self) -> String {
        let result = format!("{}{}", self.prefix, self.index);
        self.index += 1;
        result
    }
}

impl Formula {
    /// ## Prenex Normal Form (PNF)
    /// A Prenex Normal Form (PNF) is a formula with all quantifiers (existential and universal) and
    /// bound variables at the front, followed by a quantifier-free part.
    /// `Formula.pnf()` returns a PNF equivalent to the given formula.
    pub fn pnf(&self) -> Formula {
        // Renames the input variable with a postfix until it's not in the list of no collision variables.
        fn rename(variable: &V, no_collision_variables: &Vec<&V>) -> V {
            let mut name = variable.0.clone();
            let names: Vec<&String> = no_collision_variables
                .into_iter()
                .map(|v| &v.0)
                .collect();
            while names.contains(&&name) {
                name.push_str("`")
            }
            return V::new(&name);
        }

        fn shared_variables<'a>(quantifier_vars: &'a Vec<V>, other_vars: &Vec<&V>) -> Vec<&'a V> {
            quantifier_vars.iter()
                .filter(|v| other_vars.contains(v))
                .collect()
        }

        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { formula } => { // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
                let formula = formula.pnf();
                match formula {
                    Forall { variables, formula } => exists(
                        variables,
                        not(*formula).pnf(),
                    ),
                    Exists { variables, formula } => forall(
                        variables,
                        not(*formula).pnf(),
                    ),
                    _ => not(formula)
                }
            }
            And { left, right } => { // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, formula.and(right)).pnf()
                } else if let Exists { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, formula.and(right)).pnf()
                } else if let Forall { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, left.and(formula)).pnf()
                } else if let Exists { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, left.and(formula)).pnf()
                } else {
                    And { left: Box::new(left), right: Box::new(right) }
                }
            }
            Or { left, right } => { // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, formula.or(right)).pnf()
                } else if let Exists { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, formula.or(right)).pnf()
                } else if let Forall { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, left.or(formula)).pnf()
                } else if let Exists { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, left.or(formula)).pnf()
                } else {
                    Or { left: Box::new(left), right: Box::new(right) }
                }
            }
            Implies { left, right } => { // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, formula.implies(right)).pnf()
                } else if let Exists { ref variables, ref formula } = left {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, formula.implies(right)).pnf()
                } else if let Forall { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    forall(variables, left.implies(formula)).pnf()
                } else if let Exists { ref variables, ref formula } = right {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| if shared_vars.contains(&v) {
                        rename(v, &all_vars)
                    } else {
                        v.clone()
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);

                    exists(variables, left.implies(formula)).pnf()
                } else {
                    Implies { left: Box::new(left), right: Box::new(right) }
                }
            }
            Iff { left, right } => left.clone()
                .implies(*right.clone())
                .and(right.clone().implies(*left.clone())
                ).pnf(),
            Exists { variables, formula } => exists(
                variables.clone(),
                formula.pnf(),
            ),
            Forall { variables, formula } => forall(
                variables.clone(),
                formula.pnf(),
            ),
        }
    }

    /// ## Skolem Normal Form (SNF)
    /// A Skolem Normal Form (SNF) is a PNF with only universal quantifiers.
    /// (see: https://en.wikipedia.org/wiki/Skolem_normal_form)
    /// `Formula.snf()` returns an SNF equivalent to the given formula.
    pub fn snf(&self) -> Formula {
        self.snf_with(&mut SkolemGenerator::new())
    }

    /// When generating Skolem function names (including Skolem constants), `Formula.snf_with(generator)`
    /// uses an existing `SkolemGenerator` to avoid collision in naming.
    pub fn snf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        fn helper(formula: Formula, mut skolem_vars: Vec<V>, generator: &mut SkolemGenerator) -> Formula {
            match formula {
                Forall { variables, formula } => {
                    skolem_vars.append(&mut variables.clone());
                    forall(variables, helper(*formula, skolem_vars, generator))
                }
                Exists { variables, formula } => {
                    let mut map: HashMap<&V, Term> = HashMap::new();

                    variables.iter().for_each(|v| if skolem_vars.is_empty() {
                        map.insert(&v, C::new(&generator.next()).into());
                    } else {
                        let vars: Vec<Term> = skolem_vars
                            .iter()
                            .map(|v| v.clone().into())
                            .collect();
                        map.insert(&v, Func::new(&generator.next()).app(vars));
                    });

                    let substituted = formula.substitute(&map);
                    helper(substituted, skolem_vars, generator)
                }
                _ => formula
            }
        }

        // Skolemization only makes sense for PNF formulas.
        let free_vars: Vec<V> = self.free_vars()
            .into_iter()
            .map(|v| v.clone())
            .collect();
        helper(self.pnf(), free_vars, generator)
    }

    /// ## Negation Normal Form (SNF)
    /// A Negation Normal Form (NNF) is a formula where negation is only applied to its atomic
    /// (including equations) subformulas.
    /// `Formula.nnf()` returns an NNF equivalent to the given formula.
    fn nnf(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { ref formula } => {
                match **formula {
                    Top => Bottom,
                    Bottom => Top,
                    Atom { .. } | Equals { .. } => self.clone(),
                    Not { ref formula } => *formula.clone(),
                    And { ref left, ref right } => not(*left.clone())
                        .nnf()
                        .or(not(*right.clone())
                            .nnf()),
                    Or { ref left, ref right } => not(*left.clone())
                        .nnf()
                        .and(not(*right.clone())
                            .nnf()),
                    Implies { ref left, ref right } => left.nnf()
                        .and(not(*right.clone())
                            .nnf()),
                    Iff { ref left, ref right } => left.nnf()
                        .and(not(*right.clone())
                            .nnf())
                        .or(not(*left.clone())
                            .nnf()
                            .and(right.nnf())),
                    Exists { ref variables, ref formula } => forall(
                        variables.clone(),
                        not(*formula.clone()).nnf(),
                    ),
                    Forall { ref variables, ref formula } => exists(
                        variables.clone(),
                        not(*formula.clone()).nnf(),
                    ),
                }
            }
            And { left, right } => left.nnf().and(right.nnf()),
            Or { left, right } => left.nnf().or(right.nnf()),
            Implies { left, right } => not(*left.clone())
                .nnf()
                .or(right.nnf()),
            Iff { left, right } => not(*left.clone())
                .nnf()
                .or(right.nnf())
                .and(left.nnf()
                    .or(not(*right.clone())
                        .nnf())),
            Exists { variables, formula } => exists(
                variables.clone(),
                formula.nnf(),
            ),
            Forall { variables, formula } => forall(
                variables.clone(),
                formula.nnf(),
            ),
        }
    }

    /// ## Conjunctive Normal Form (CNF)
    /// A Conjunctive Normal Form (CNF) is a formula that is the conjunction of zero or more clauses.
    /// A clause is a disjunction of atomic formulas (including equations). All of the variables
    /// are assumed to be universally quantified.
    /// `Formula.cnf()` returns a CNF equivalent to the given formula.
    pub fn cnf(&self) -> Formula {
        self.cnf_with(&mut SkolemGenerator::new())
    }

    /// `Formula.cnf_with(generator)` uses an existing `SkolemGenerator` to avoid collision in the
    /// names of the Skolem function (and constant) for formulas in the same theory.
    pub fn cnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        // The following distributes conjunctions in the given formula. The function assumes that
        // its input is an NNF.
        fn distribute_or(formula: &Formula) -> Formula {
            match formula {
                Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
                And { left, right } => distribute_or(left)
                    .and(distribute_or(right)),
                Or { left, right } => {
                    let left = distribute_or(left);
                    let right = distribute_or(right);
                    if let And { left: l, right: r } = left {
                        distribute_or(&l.or(right.clone()))
                            .and(distribute_or(&r.or(right)))
                    } else if let And { left: l, right: r } = right {
                        distribute_or(&left.clone().or(*l)).and(
                            distribute_or(&left.or(*r)))
                    } else {
                        left.or(right)
                    }
                }
                Forall { variables, formula } => forall(
                    variables.clone(),
                    distribute_or(formula),
                ),
                _ => panic!("something is wrong: expecting a formula in negation normal form")
            }
        }

        // The following eliminates the existential quantifiers of the input formula.
        fn remove_forall(formula: Formula) -> Formula {
            if let Forall { formula, .. } = formula {
                remove_forall(*formula)
            } else {
                formula
            }
        }

        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_or(&nnf))
    }

    /// ## Disjunctive Normal Form (DNF)
    /// A Disjunctive Normal Form (DNF) is a formula that is the disjunction of zero or more conjuncts.
    /// A conjunct is a conjunction of atomic formulas (including equations). All of the variables
    /// are assumed to be universally quantified.
    /// `Formula.dnf()` returns a DNF equivalent to the given formula.
    pub fn dnf(&self) -> Formula {
        self.dnf_with(&mut SkolemGenerator::new())
    }

    /// `Formula.dnf_with(generator)` uses an existing `SkolemGenerator` to avoid collision in the
    /// names of the Skolem function (and constant) for formulas in the same theory.
    pub fn dnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        // The following distributes disjunction in the given formula. The function assumes that
        // its input is an NNF.
        fn distribute_and(formula: &Formula) -> Formula {
            match formula {
                Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
                Or { left, right } => distribute_and(left)
                    .or(distribute_and(right)),
                And { left, right } => {
                    let left = distribute_and(left);
                    let right = distribute_and(right);
                    if let Or { left: l, right: r } = left {
                        distribute_and(&l.and(right.clone()))
                            .or(distribute_and(&r.and(right)))
                    } else if let Or { left: l, right: r } = right {
                        distribute_and(&left.clone().and(*l))
                            .or(distribute_and(&left.and(*r)))
                    } else {
                        And { left: Box::new(left), right: Box::new(right) }
                    }
                }
                Forall { variables, formula } => forall(
                    variables.clone(),
                    distribute_and(formula),
                ),
                _ => panic!("Something is wrong: expecting a formula in negation normal form.")
            }
        }

        // The following eliminates the existential quantifiers of the input formula.
        fn remove_forall(formula: Formula) -> Formula {
            if let Forall { formula, .. } = formula {
                remove_forall(*formula)
            } else {
                formula
            }
        }

        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_and(&nnf))
    }

    /// Applies syntactic transformations to simplify the input formula.
    pub fn simplify(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { formula } => {
                let formula = formula.simplify();
                match formula {
                    Top => Bottom,
                    Bottom => Top,
                    Not { formula } => formula.simplify(),
                    _ => not(formula)
                }
            }
            And { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Bottom
                } else if let Bottom = right {
                    Bottom
                } else if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else {
                    left.and(right)
                }
            }
            Or { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Bottom = left {
                    right
                } else if let Bottom = right {
                    left
                } else {
                    left.or(right)
                }
            }
            Implies { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Top = left {
                    right
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.implies(right)
                }
            }
            Iff { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else if let Bottom = left {
                    not(right).simplify()
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.iff(right)
                }
            }
            Exists { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars.iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    exists(vs, formula)
                }
            }
            Forall { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars.iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    forall(vs, formula)
                }
            }
        }
    }

    /// ## Geometric Normal Form (GNF)
    /// `Formula.gnf()` returns a list of formulas in GNF, equivalent to the given formula.
    /// (see https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf)
    pub fn gnf(&self) -> Vec<Formula> {
        self.gnf_with(&mut SkolemGenerator::new())
    }

    /// `Formula.gnf_with(generator)` uses an existing `SkolemGenerator` to avoid collision in the
    /// names of the Skolem function (and constant) for formulas in the same theory.
    pub fn gnf_with(&self, generator: &mut SkolemGenerator) -> Vec<Formula> {
        // For any disjunct of the CNF, the negative literals form the body of the geometric form
        // and the positive literals form its head:
        fn split_sides(disjunct: Formula) -> (Vec<Formula>, Vec<Formula>) {
            match disjunct {
                Or { left, right } => {
                    let (mut left_body, mut left_head) = split_sides(*left);
                    let (mut right_body, mut right_head) = split_sides(*right);

                    left_body.append(&mut right_body);
                    let body: Vec<Formula> = left_body.into_iter().unique().collect();

                    left_head.append(&mut right_head);
                    let head: Vec<Formula> = left_head.into_iter().unique().collect();

                    (body, head)
                }
                Not { formula } => (vec![*formula], vec![]),
                _ => (vec![], vec![disjunct])
            }
        }

        // Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
        fn to_implication(disjunct: Formula) -> Formula {
            let (body, head) = split_sides(disjunct);
            let body = body
                .into_iter()
                .fold(Top, |x, y| x.and(y))
                .simplify();
            let head = head
                .into_iter()
                .fold(Bottom, |x, y| x.or(y))
                .simplify();
            body.implies(head)
        }

        // Split the CNF to a set of disjuncts.
        fn get_disjuncts(cnf: Formula) -> Vec<Formula> {
            match cnf {
                And { left, right } => {
                    let mut left = get_disjuncts(*left);
                    let mut right = get_disjuncts(*right);
                    left.append(&mut right);
                    left.into_iter().unique().collect()
                }
                _ => vec![cnf]
            }
        }

        get_disjuncts(self.cnf_with(generator))
            .into_iter()
            .map(to_implication)
            .collect()
    }
}

impl Theory {
    /// ## Geometric Normal Form (GNF)
    /// `Theory.gnf()` transforms the given theory to a geometric theory (with all formulas in
    /// geometric normal form).
    pub fn gnf(&self) -> Theory {
        let mut generator = SkolemGenerator::new();
        let formulas: Vec<Formula> = self.formulas
            .iter()
            .flat_map(|f| f.gnf_with(&mut generator))
            .collect();
        Theory::new(compress_geometric(formulas))
    }
}

fn compress_geometric(formulas: Vec<Formula>) -> Vec<Formula> {
    formulas.into_iter().sorted_by(|f1, f2| { // sort sequents by their body
        match (f1, f2) {
            (Implies { left: f1, .. }, Implies { left: f2, .. }) => f1.cmp(f2),
            _ => Equal
        }
    }).into_iter().coalesce(|f1, f2| { // merge the ones with the same body:
        match f1 {
            Implies { left: ref l1, right: ref r1 } => {
                let l_vars = l1.free_vars();
                let r_vars = r1.free_vars();
                // compress sequents with no free variables that show up only in head:
                if r_vars.iter().all(|rv| l_vars
                    .iter()
                    .any(|lv| lv == rv)) {
                    match f2 {
                        Implies { left: ref l2, right: ref r2 } => {
                            let l_vars = l2.free_vars();
                            let r_vars = r2.free_vars();
                            if r_vars.iter().all(|rv| l_vars
                                .iter()
                                .any(|lv| lv == rv)) {
                                if l1 == l2 {
                                    Ok(l2.clone().implies(r1.clone().and(*r2.clone())))
                                } else {
                                    Err((f1, f2))
                                }
                            } else {
                                Err((f2, f1))
                            }
                        }
                        _ => Err((f2, f1))
                    }
                } else {
                    Err((f1, f2))
                }
            }
            _ => Err((f1, f2))
        }
    }).map(|f| { // convert the head to dnf and simplify it:
        match f {
            Implies { left, right: r } => left.implies(simplify_dnf(r.dnf())),
            _ => f
        }
    }).collect()
}

// Simplifies the given DNF as a helper for compress geometric.
fn simplify_dnf(formula: Formula) -> Formula {
    fn disjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            Or { left, right } => {
                let mut lefts = disjunct_list(*left);
                let mut rights = disjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    fn conjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            And { left, right } => {
                let mut lefts = conjunct_list(*left);
                let mut rights = conjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    let disjuncts: Vec<Vec<Formula>> = disjunct_list(formula)
        .into_iter()
        .map(|d| conjunct_list(d)
            .into_iter()
            .unique()
            .collect())
        .collect();

    let disjuncts: Vec<Vec<Formula>> = disjuncts
        .iter()
        .filter(|d| !disjuncts
            .iter()
            .any(|dd| (dd.len() < d.len() || (dd.len() == d.len() && dd < d))
                && dd
                .iter()
                .all(|cc| d
                    .iter()
                    .any(|c| cc == c)
                )
            )
        ).map(|d| d.clone())
        .unique()
        .collect();

    disjuncts
        .into_iter()
        .map(|d| d
            .into_iter()
            .fold1(|f1, f2| f1.and(f2))
            .unwrap())
        .fold1(|f1, f2| f1.or(f2))
        .unwrap()
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::test_prelude::*;
    use std::collections::HashMap;
    use crate::formula::parser::{parse_formula, parse_theory_unsafe};

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<&V, Term> = HashMap::new();
            assert_eq!(x(), x().substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &_x();
            let y_var = y();

            map.insert(x_v, y_var);
            assert_eq!(y(), x().substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &_x();
            let y_v = &_y();
            let term_1 = g().app1(z());
            let term_2 = h().app2(z(), y());

            map.insert(x_v, term_1);
            map.insert(y_v, term_2);
            assert_eq!(f().app2(g().app1(z()), h().app2(z(), y())),
                       f().app2(x(), y()).substitute(&map));
        }
    }

    #[test]
    fn test_rename_term() {
        assert_eq!(x(), x().rename_vars(&|v: &V| v.clone()));
        assert_eq!(y(), x().rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(x(), x().rename_vars(&|v: &V| {
            if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(f().app1(y()), f().app1(x()).rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(f().app1(x()), f().app1(x()).rename_vars(&|v: &V| {
            if *v == _z() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(f().app2(z(), z()), f().app2(x(), y()).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(f().app2(y(), g().app2(y(), h().app1(z()))),
                   f().app2(x(), g().app2(x(), h().app1(y()))).rename_vars(&|v: &V| {
                       if *v == _x() {
                           _y()
                       } else if *v == _y() {
                           _z()
                       } else {
                           v.clone()
                       }
                   }));
    }

    #[test]
    fn test_substitute_term() {
        assert_eq!(x(), x().substitute(&|v: &V| v.clone().into()));
        assert_eq!(a(), a().substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(y(), x().substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(a(), x().substitute(&|v: &V| {
            if *v == _x() {
                a()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app1(z()), x().substitute(&|v: &V| {
            if *v == _x() {
                f().app1(z())
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(x(), x().substitute(&|v: &V| {
            if *v == _y() {
                z()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app1(y()), f().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app1(g().app1(h().app2(y(), z()))), f().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                g().app1(h().app2(y(), z()))
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app1(x()), f().app1(x()).substitute(&|v: &V| {
            if *v == _y() {
                z()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app2(g().app1(z()), h().app2(z(), y())),
                   f().app2(x(), y()).substitute(&|v: &V| {
                       if *v == _x() {
                           g().app1(z())
                       } else if *v == _y() {
                           h().app2(z(), y())
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(f().app2(f().app1(f().app0()), g().app2(f().app1(f().app0()), h().app1(z()))),
                   f().app2(x(), g().app2(x(), h().app1(y()))).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(f().app0())
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(f().app2(f().app1(a()), g().app2(f().app1(a()), h().app1(z()))),
                   f().app2(x(), g().app2(x(), h().app1(y()))).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(a())
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().into()
                       }
                   }));
    }

    #[test]
    fn test_rename_formula() {
        assert_eq!(Top, Top.rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(Bottom, Bottom.rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(z().equals(z()), x().equals(y()).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(x()), P().app1(x()).rename_vars(&|v: &V| {
            if *v == _x() {
                _x()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(y()), P().app1(x()).rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app3(y(), z(), y()), P().app3(x(), y(), x()).rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(not(P().app3(y(), z(), y())), not(P().app3(x(), y(), x())).rename_vars(&|v: &V| {
            if *v == _x() {
                _y()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(z()).and(Q().app1(z())), P().app1(x()).and(Q().app1(y())).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(z()).or(Q().app1(z())), P().app1(x()).or(Q().app1(y())).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(z()).implies(Q().app1(z())), P().app1(x()).implies(Q().app1(y())).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(P().app1(z()).iff(Q().app1(z())), P().app1(x()).iff(Q().app1(y())).rename_vars(&|v: &V| {
            if *v == _x() {
                _z()
            } else if *v == _y() {
                _z()
            } else {
                v.clone()
            }
        }));
        assert_eq!(exists2(_x(), _y(), P().app3(y(), y(), y())),
                   exists2(_x(), _y(), P().app3(x(), y(), z())).rename_vars(&|v: &V| {
                       if *v == _x() {
                           _y()
                       } else if *v == _z() {
                           _y()
                       } else {
                           v.clone()
                       }
                   }));
        assert_eq!(forall2(_x(), _y(), P().app3(y(), y(), y())),
                   forall2(_x(), _y(), P().app3(x(), y(), z())).rename_vars(&|v: &V| {
                       if *v == _x() {
                           _y()
                       } else if *v == _z() {
                           _y()
                       } else {
                           v.clone()
                       }
                   }));
        assert_eq!(
            exists1(_x(),
                    forall1(_y(),
                            P().app1(y()).or(Q().app1(z()).and(R().app1(z()))),
                    ).and(not(z().equals(z())))),
            exists1(_x(),
                    forall1(_y(),
                            P().app1(x()).or(Q().app1(y()).and(R().app1(z()))),
                    ).and(not(y().equals(y()))),
            ).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            }));
    }


    #[test]
    fn test_substitute_formula() {
        assert_eq!(Top, Top.substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(Bottom, Bottom.substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(f().app1(g().app1(z())).equals(g().app1(f().app1(z()))), x().equals(y()).substitute(&|v: &V| {
            if *v == _x() {
                f().app1(g().app1(z()))
            } else if *v == _y() {
                g().app1(f().app1(z()))
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(P().app1(h().app1(y())), P().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                h().app1(y())
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(P().app1(g().app1(g().app1(x()))), P().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                g().app1(g().app1(x()))
            } else {
                v.clone().into()
            }
        }));
        assert_eq!(P().app3(y(), f().app1(z()), y()),
                   P().app3(x(), y(), x()).substitute(&|v: &V| {
                       if *v == _x() {
                           y()
                       } else if *v == _y() {
                           f().app1(z())
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(not(P().app3(h().app0(), z(), h().app0())),
                   not(P().app3(x(), y(), x())).substitute(&|v: &V| {
                       if *v == _x() {
                           h().app0()
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(f().app1(g().app0())).and(Q().app1(h().app1(z()))),
                   P().app1(x()).and(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app0())
                       } else if *v == _y() {
                           h().app1(z())
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(f().app1(g().app0())).or(Q().app1(h().app1(z()))),
                   P().app1(x()).or(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app0())
                       } else if *v == _y() {
                           h().app1(z())
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(f().app0()).implies(Q().app1(g().app0())),
                   P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app0()
                       } else if *v == _y() {
                           g().app0()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(a()).implies(Q().app1(b())),
                   P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           a()
                       } else if *v == _y() {
                           b()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(f().app0()).iff(Q().app1(g().app0())),
                   P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app0()
                       } else if *v == _y() {
                           g().app0()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(P().app1(a()).iff(Q().app1(b())),
                   P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           a()
                       } else if *v == _y() {
                           b()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(exists2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
                   exists2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app1(y()))
                       } else if *v == _z() {
                           y()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(forall2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
                   forall2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app1(y()))
                       } else if *v == _z() {
                           y()
                       } else {
                           v.clone().into()
                       }
                   }));
        assert_eq!(
            exists1(_x(),
                    forall1(_y(),
                            P().app1(y()).or(Q().app1(z()).and(R().app1(z()))),
                    ).and(not(z().equals(z())))),
            exists1(_x(),
                    forall1(_y(),
                            P().app1(x()).or(Q().app1(y()).and(R().app1(z()))),
                    ).and(not(y().equals(y()))),
            ).substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else if *v == _y() {
                    z()
                } else {
                    v.clone().into()
                }
            }));
    }

    #[test]
    fn test_pnf() {
        assert_debug_string("TRUE", parse_formula("TRUE").pnf());
        assert_debug_string("FALSE", parse_formula("FALSE").pnf());
        assert_debug_string("P(x)", parse_formula("P(x)").pnf());
        assert_debug_string("x = y", parse_formula("x = y").pnf());
        assert_debug_string("~P(x)", parse_formula("~P(x)").pnf());
        assert_debug_string("P(x) & Q(y)", parse_formula("P(x) & Q(y)").pnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("P(x) | Q(y)").pnf());
        assert_debug_string("P(x) -> Q(y)", parse_formula("P(x) -> Q(y)").pnf());
        assert_debug_string("(P(x) -> Q(y)) & (Q(y) -> P(x))", parse_formula("P(x) <=> Q(y)").pnf());
        assert_debug_string("? x. ((P(x) & (~Q(y))) | R(z))",
                            parse_formula("? x. P(x) & ~Q(y) | R(z)").pnf());
        assert_debug_string("! x. ((P(x) & (~Q(y))) | R(z))",
                            parse_formula("! x. P(x) & ~Q(y) | R(z)").pnf());
        // sanity checking:
        assert_debug_string("! x. (~P(x))", parse_formula("~? x. P(x)").pnf());
        assert_debug_string("! x. (P(x) & Q(y))", parse_formula("(! x. P(x)) & Q(y)").pnf());
        assert_debug_string("? x. (P(x) & Q(y))", parse_formula("(? x. P(x)) & Q(y)").pnf());
        assert_debug_string("! x`. (P(x`) & Q(x))", parse_formula("(! x. P(x)) & Q(x)").pnf());
        assert_debug_string("? x`. (P(x`) & Q(x))", parse_formula("(? x. P(x)) & Q(x)").pnf());
        assert_debug_string("! x`, y`. (P(x`, y`) & Q(x, y))",
                            parse_formula("(! x, y. P(x, y)) & Q(x, y)").pnf());
        assert_debug_string("? x`, y`. (P(x`, y`) & Q(x, y))",
                            parse_formula("(? x, y. P(x, y)) & Q(x, y)").pnf());
        assert_debug_string("! x. (Q(y) & P(x))",
                            parse_formula("Q(y) & ! x. P(x)").pnf());
        assert_debug_string("? x. (Q(y) & P(x))",
                            parse_formula("Q(y) & ? x. P(x)").pnf());
        assert_debug_string("! x`. (Q(x) & P(x`))",
                            parse_formula("Q(x) & ! x. P(x)").pnf());
        assert_debug_string("? x`. (Q(x) & P(x`))",
                            parse_formula("Q(x) & ? x. P(x)").pnf());
        assert_debug_string("! x`, y`. (Q(x, y) & P(x`, y`))",
                            parse_formula("Q(x, y) & ! x, y. P(x, y)").pnf());
        assert_debug_string("? x`, y`. (Q(x, y) & P(x`, y`))",
                            parse_formula("Q(x, y) & ? x, y. P(x, y)").pnf());
        assert_debug_string("! x. (P(x) | Q(y))", parse_formula("(! x. P(x)) | Q(y)").pnf());
        assert_debug_string("? x. (P(x) | Q(y))", parse_formula("(? x. P(x)) | Q(y)").pnf());
        assert_debug_string("! x`. (P(x`) | Q(x))", parse_formula("(! x. P(x)) | Q(x)").pnf());
        assert_debug_string("? x`. (P(x`) | Q(x))", parse_formula("(? x. P(x)) | Q(x)").pnf());
        assert_debug_string("! x`, y`. (P(x`, y`) | Q(x, y))",
                            parse_formula("(! x, y. P(x, y)) | Q(x, y)").pnf());
        assert_debug_string("? x`, y`. (P(x`, y`) | Q(x, y))",
                            parse_formula("(? x, y. P(x, y)) | Q(x, y)").pnf());
        assert_debug_string("! x. (Q(y) | P(x))",
                            parse_formula("Q(y) | ! x. P(x)").pnf());
        assert_debug_string("? x. (Q(y) | P(x))",
                            parse_formula("Q(y) | ? x. P(x)").pnf());
        assert_debug_string("! x`. (Q(x) | P(x`))",
                            parse_formula("Q(x) | ! x. P(x)").pnf());
        assert_debug_string("? x`. (Q(x) | P(x`))",
                            parse_formula("Q(x) | ? x. P(x)").pnf());
        assert_debug_string("! x`, y`. (Q(x, y) | P(x`, y`))",
                            parse_formula("Q(x, y) | ! x, y. P(x, y)").pnf());
        assert_debug_string("? x`, y`. (Q(x, y) | P(x`, y`))",
                            parse_formula("Q(x, y) | ? x, y. P(x, y)").pnf());
        assert_debug_string("? x. (P(x) -> Q(y))", parse_formula("(! x. P(x)) -> Q(y)").pnf());
        assert_debug_string("! x. (P(x) -> Q(y))", parse_formula("(? x. P(x)) -> Q(y)").pnf());
        assert_debug_string("? x`. (P(x`) -> Q(x))", parse_formula("(! x. P(x)) -> Q(x)").pnf());
        assert_debug_string("! x`. (P(x`) -> Q(x))", parse_formula("(? x. P(x)) -> Q(x)").pnf());
        assert_debug_string("? x`, y`. (P(x`, y`) -> Q(x, y))",
                            parse_formula("(! x, y. P(x, y)) -> Q(x, y)").pnf());
        assert_debug_string("! x`, y`. (P(x`, y`) -> Q(x, y))",
                            parse_formula("(? x, y. P(x, y)) -> Q(x, y)").pnf());
        assert_debug_string("! x. (Q(y) -> P(x))",
                            parse_formula("Q(y) -> ! x. P(x)").pnf());
        assert_debug_string("? x. (Q(y) -> P(x))",
                            parse_formula("Q(y) -> ? x. P(x)").pnf());
        assert_debug_string("! x`. (Q(x) -> P(x`))",
                            parse_formula("Q(x) -> ! x. P(x)").pnf());
        assert_debug_string("? x`. (Q(x) -> P(x`))",
                            parse_formula("Q(x) -> ? x. P(x)").pnf());
        assert_debug_string("! x`, y`. (Q(x, y) -> P(x`, y`))",
                            parse_formula("Q(x, y) -> ! x, y. P(x, y)").pnf());
        assert_debug_string("? x`, y`. (Q(x, y) -> P(x`, y`))",
                            parse_formula("Q(x, y) -> ? x, y. P(x, y)").pnf());

        assert_debug_string("? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                            parse_formula("(! x. P(x)) <=> Q(y)").pnf());
        assert_debug_string("! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                            parse_formula("(? x. P(x)) <=> Q(y)").pnf());
        assert_debug_string("? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                            parse_formula("(! x. P(x)) <=> Q(x)").pnf());
        assert_debug_string("! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                            parse_formula("(? x. P(x)) <=> Q(x)").pnf());
        assert_debug_string("? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                            parse_formula("(! x, y. P(x, y)) <=> Q(x, y)").pnf());
        assert_debug_string("! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                            parse_formula("(? x, y. P(x, y)) <=> Q(x, y)").pnf());
        assert_debug_string("! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                            parse_formula("Q(y) <=> ! x. P(x)").pnf());
        assert_debug_string("? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                            parse_formula("Q(y) <=> ? x. P(x)").pnf());
        assert_debug_string("! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                            parse_formula("Q(x) <=> ! x. P(x)").pnf());
        assert_debug_string("? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                            parse_formula("Q(x) <=> ? x. P(x)").pnf());
        assert_debug_string("! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                            parse_formula("Q(x, y) <=> ! x, y. P(x, y)").pnf());
        assert_debug_string("? x`, y`. (! x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                            parse_formula("Q(x, y) <=> ? x, y. P(x, y)").pnf());
        //renaming tests
        assert_debug_string("! x``, x`. (P(x``) & Q(x))",
                            forall2(_x(), _x_1(), P().app1(x())).and(Q().app1(x())).pnf());
        assert_debug_string("? x``, x`. (P(x``) & Q(x))",
                            exists2(_x(), _x_1(), P().app1(x())).and(Q().app1(x())).pnf());
        assert_debug_string("? x``. (P(x``) & Q(x, x`))",
                            exists1(_x(), P().app1(x())).and(Q().app2(x(), x_1())).pnf());
        assert_debug_string("? x``. (P(x``, x`) & Q(x))",
                            exists1(_x(), P().app2(x(), x_1())).and(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (Q(x) & P(x``))",
                            Q().app1(x()).and(forall2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``, x`. (Q(x) & P(x``))",
                            Q().app1(x()).and(exists2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x, x`) & P(x``))",
                            Q().app2(x(), x_1()).and(exists1(_x(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x) & P(x``, x`))",
                            Q().app1(x()).and(exists1(_x(), P().app2(x(), x_1()))).pnf());

        assert_debug_string("! x``, x`. (P(x``) | Q(x))",
                            forall2(_x(), _x_1(), P().app1(x())).or(Q().app1(x())).pnf());
        assert_debug_string("? x``, x`. (P(x``) | Q(x))",
                            exists2(_x(), _x_1(), P().app1(x())).or(Q().app1(x())).pnf());
        assert_debug_string("? x``. (P(x``) | Q(x, x`))",
                            exists1(_x(), P().app1(x())).or(Q().app2(x(), x_1())).pnf());
        assert_debug_string("? x``. (P(x``, x`) | Q(x))",
                            exists1(_x(), P().app2(x(), x_1())).or(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (Q(x) | P(x``))",
                            Q().app1(x()).or(forall2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``, x`. (Q(x) | P(x``))",
                            Q().app1(x()).or(exists2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x, x`) | P(x``))",
                            Q().app2(x(), x_1()).or(exists1(_x(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x) | P(x``, x`))",
                            Q().app1(x()).or(exists1(_x(), P().app2(x(), x_1()))).pnf());

        assert_debug_string("? x``, x`. (P(x``) -> Q(x))",
                            forall2(_x(), _x_1(), P().app1(x())).implies(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (P(x``) -> Q(x))",
                            exists2(_x(), _x_1(), P().app1(x())).implies(Q().app1(x())).pnf());
        assert_debug_string("! x``. (P(x``) -> Q(x, x`))",
                            exists1(_x(), P().app1(x())).implies(Q().app2(x(), x_1())).pnf());
        assert_debug_string("! x``. (P(x``, x`) -> Q(x))",
                            exists1(_x(), P().app2(x(), x_1())).implies(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (Q(x) -> P(x``))",
                            Q().app1(x()).implies(forall2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``, x`. (Q(x) -> P(x``))",
                            Q().app1(x()).implies(exists2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x, x`) -> P(x``))",
                            Q().app2(x(), x_1()).implies(exists1(_x(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (Q(x) -> P(x``, x`))",
                            Q().app1(x()).implies(exists1(_x(), P().app2(x(), x_1()))).pnf());

        assert_debug_string("? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
                            forall2(_x(), _x_1(), P().app1(x())).iff(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
                            exists2(_x(), _x_1(), P().app1(x())).iff(Q().app1(x())).pnf());
        assert_debug_string("! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
                            exists1(_x(), P().app1(x())).iff(Q().app2(x(), x_1())).pnf());
        assert_debug_string("! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
                            exists1(_x(), P().app2(x(), x_1())).iff(Q().app1(x())).pnf());
        assert_debug_string("! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
                            Q().app1(x()).iff(forall2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
                            Q().app1(x()).iff(exists2(_x(), _x_1(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
                            Q().app2(x(), x_1()).iff(exists1(_x(), P().app1(x()))).pnf());
        assert_debug_string("? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
                            Q().app1(x()).iff(exists1(_x(), P().app2(x(), x_1()))).pnf());
        // both sides of binary formulas
        assert_debug_string("! x. (! x`. (P(x) & Q(x`)))",
                            parse_formula("(! x. P(x)) & (! x. Q(x))").pnf());
        assert_debug_string("! x. (? x`. (P(x) & Q(x`)))",
                            parse_formula("(! x. P(x)) & (? x. Q(x))").pnf());
        assert_debug_string("? x. (! x`. (P(x) & Q(x`)))",
                            parse_formula("(? x. P(x)) & (! x. Q(x))").pnf());
        assert_debug_string("? x. (? x`. (P(x) & Q(x`)))",
                            parse_formula("(? x. P(x)) & (? x. Q(x))").pnf());
        assert_debug_string("! x. (! x`. (P(x) | Q(x`)))",
                            parse_formula("(! x. P(x)) | (! x. Q(x))").pnf());
        assert_debug_string("! x. (? x`. (P(x) | Q(x`)))",
                            parse_formula("(! x. P(x)) | (? x. Q(x))").pnf());
        assert_debug_string("? x. (! x`. (P(x) | Q(x`)))",
                            parse_formula("(? x. P(x)) | (! x. Q(x))").pnf());
        assert_debug_string("? x. (? x`. (P(x) | Q(x`)))",
                            parse_formula("(? x. P(x)) | (? x. Q(x))").pnf());
        assert_debug_string("? x. (! x`. (P(x) -> Q(x`)))",
                            parse_formula("(! x. P(x)) -> (! x. Q(x))").pnf());
        assert_debug_string("? x. (? x`. (P(x) -> Q(x`)))",
                            parse_formula("(! x. P(x)) -> (? x. Q(x))").pnf());
        assert_debug_string("! x. (! x`. (P(x) -> Q(x`)))",
                            parse_formula("(? x. P(x)) -> (! x. Q(x))").pnf());
        assert_debug_string("! x. (? x`. (P(x) -> Q(x`)))",
                            parse_formula("(? x. P(x)) -> (? x. Q(x))").pnf());
        assert_debug_string("? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                            parse_formula("(! x. P(x)) <=> (! x. Q(x))").pnf());
        assert_debug_string("? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                            parse_formula("(! x. P(x)) <=> (? x. Q(x))").pnf());
        assert_debug_string("! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                            parse_formula("(? x. P(x)) <=> (! x. Q(x))").pnf());
        assert_debug_string("! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                            parse_formula("(? x. P(x)) <=> (? x. Q(x))").pnf());
        // multiple steps
        assert_debug_string("? x. (~(~P(x)))", parse_formula("~~?x.P(x)").pnf());
        assert_debug_string("! x. (~(~P(x)))", parse_formula("~~!x.P(x)").pnf());
        assert_debug_string("! x`. (P(x) & (Q(x`) & R(x)))", parse_formula("P(x) & ((! x. Q(x)) & R(x))").pnf());
        assert_debug_string("? x`. (P(x) & (Q(x`) & R(x)))", parse_formula("P(x) & ((? x. Q(x)) & R(x))").pnf());
        assert_debug_string("! x`. (P(x) | (Q(x`) | R(x)))", parse_formula("P(x) | ((! x. Q(x)) | R(x))").pnf());
        assert_debug_string("? x`. (P(x) | (Q(x`) | R(x)))", parse_formula("P(x) | ((? x. Q(x)) | R(x))").pnf());
        assert_debug_string("? x`. (P(x) -> (Q(x`) -> R(x)))", parse_formula("P(x) -> ((! x. Q(x)) -> R(x))").pnf());
        assert_debug_string("! x`. (P(x) -> (Q(x`) -> R(x)))", parse_formula("P(x) -> ((? x. Q(x)) -> R(x))").pnf());
        assert_debug_string("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))",
                            parse_formula("P(x) <=> ((! x. Q(x)) <=> R(x))").pnf());
        assert_debug_string("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))",
                            parse_formula("P(x) <=> ((? x. Q(x)) <=> R(x))").pnf());
        // random formulas
        assert_debug_string("! x. (? y. (P(x) -> (P(y) & Q(x, y))))",
                            parse_formula("!x . (P(x) -> ?y . (P(y) & Q(x, y)))").pnf());
        assert_debug_string("? x. (! y. (P(x) & (P(y) -> Q(x, y))))",
                            parse_formula("?x . (P(x) & !y . (P(y) -> Q(x, y)))").pnf());
        assert_debug_string("! x. (? y. (P(x) -> (~(P(y) -> Q(x, y)))))",
                            parse_formula("!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))").pnf());
        assert_debug_string("! x. (! z. ((P() | Q(x)) -> R(z)))",
                            parse_formula("(P() | ? x. Q(x)) -> !z. R(z)").pnf());
        assert_debug_string("! x. (? y. (! z. (! x`. (! w. ((Q(x) & (~R(x`))) | ((~Q(y)) -> R(y)))))))",
                            parse_formula("!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))").pnf());
        assert_debug_string("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))",
                            parse_formula("!x. (!y. P(x, y) -> ?y. Q(x, y))").pnf());
    }

    #[test]
    fn test_snf() {
        assert_debug_string("P('sk#0)"
                            , exists1(_x(), P().app1(x())).snf());
        assert_debug_string("! x. P(x, sk#0(x))"
                            , forall1(_x()
                                      , exists1(_y(), P().app2(x(), y()))).snf());
        assert_debug_string("P(x, sk#0(x))"
                            , exists1(_y(), P().app2(x(), y())).snf());
        assert_debug_string("! x. P(x, f(g(sk#0(x)), h(sk#0(x))))"
                            , forall1(_x()
                                      , exists1(_y()
                                                , P().app2(x(), f().app2(g().app1(y()), h().app1(y()))))).snf());
        assert_debug_string("('sk#0 = 'sk#1) & ('sk#1 = 'sk#2)",
                            exists3(_x(), _y(), _z(), x().equals(y()).and(y().equals(z()))).snf());
        assert_debug_string("! y. (Q('sk#0, y) | P(sk#1(y), y, sk#2(y)))"
                            , exists1(_x()
                                      , forall1(_y()
                                                , Q().app2(x(), y())
                                                    .or(exists2(_x(), _z(), P().app3(x(), y(), z()))))).snf());
        assert_debug_string("! x. (! z. P(x, sk#0(x), z))",
                            forall1(_x()
                                    , exists1(_y()
                                              , forall1(_z()
                                                        , P().app3(x(), y(), z())))).snf());
        assert_debug_string("! x. (R(g(x)) | R(x, sk#0(x)))"
                            , forall1(_x(),
                                      R().app1(g().app1(x()))
                                          .or(exists1(_y(), R().app2(x(), y())))).snf());
        assert_debug_string("! y. (! z. (! v. P('sk#0, y, z, sk#1(y, z), v, sk#2(y, z, v))))"
                            , exists1(_x()
                                      , forall1(_y()
                                                , forall1(_z()
                                                          , exists1(_u()
                                                                    , forall1(_v()
                                                                              , exists1(_w()
                                                                                        , P().app(vec![x(), y(), z(), u(), v(), w()]))))))).snf());
        {
            let mut generator = SkolemGenerator::new();
            assert_debug_string("P('sk#0)", exists1(_x(), P().app1(x())).snf_with(&mut generator));
            assert_debug_string("Q('sk#1)", exists1(_x(), Q().app1(x())).snf_with(&mut generator));
        }
    }

    #[test]
    fn test_nnf() {
        assert_debug_string("TRUE", parse_formula("TRUE").nnf());
        assert_debug_string("FALSE", parse_formula("FALSE").nnf());
        assert_debug_string("P(x)", parse_formula("P(x)").nnf());
        assert_debug_string("x = y", parse_formula("x = y").nnf());
        assert_debug_string("~P(x)", parse_formula("~P(x)").nnf());
        assert_debug_string("P(x) & Q(y)", parse_formula("P(x) & Q(y)").nnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("P(x) | Q(y)").nnf());
        assert_debug_string("(~P(x)) | Q(y)", parse_formula("P(x) -> Q(y)").nnf());
        assert_debug_string("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", parse_formula("P(x) <=> Q(y)").nnf());
        assert_debug_string("? x. P(x)", parse_formula("?x. P(x)").nnf());
        assert_debug_string("! x. P(x)", parse_formula("!x. P(x)").nnf());
        // sanity checking
        assert_debug_string("FALSE", parse_formula("~TRUE").nnf());
        assert_debug_string("TRUE", parse_formula("~FALSE").nnf());
        assert_debug_string("P(x)", parse_formula("~~P(x)").nnf());
        assert_debug_string("x = y", parse_formula("~~x = y").nnf());
        assert_debug_string("(~P(x)) | (~Q(y))", parse_formula("~(P(x) & Q(y))").nnf());
        assert_debug_string("(~P(x)) & (~Q(y))", parse_formula("~(P(x) | Q(y))").nnf());
        assert_debug_string("P(x) & (~Q(y))", parse_formula("~(P(x) -> Q(y))").nnf());
        assert_debug_string("(P(x) & (~Q(y))) | ((~P(x)) & Q(y))", parse_formula("~(P(x) <=> Q(y))").nnf());
        assert_debug_string("((~P(x)) & (~Q(y))) | R(z)", parse_formula("(P(x) | Q(y)) -> R(z)").nnf());
        assert_debug_string("(((~P(x)) & (~Q(y))) | R(z)) & ((P(x) | Q(y)) | (~R(z)))",
                            parse_formula("(P(x) | Q(y)) <=> R(z)").nnf());
        assert_debug_string("! x. (~P(x))", parse_formula("~?x. P(x)").nnf());
        assert_debug_string("? x. (~P(x))", parse_formula("~!x. P(x)").nnf());
        // recursive application
        assert_debug_string("P(x) & Q(y)", parse_formula("~~P(x) & ~~Q(y)").nnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("~~P(x) | ~~Q(y)").nnf());
        assert_debug_string("(~P(x)) | Q(y)", parse_formula("~~P(x) -> ~~Q(y)").nnf());
        assert_debug_string("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", parse_formula("~~P(x) <=> ~~Q(y)").nnf());
        assert_debug_string("? x. P(x)", parse_formula("?x. ~~P(x)").nnf());
        assert_debug_string("! x. P(x)", parse_formula("!x. ~~P(x)").nnf());
        assert_debug_string("~P(x)", parse_formula("~~~P(x)").nnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("~(~P(x) & ~Q(y))").nnf());
        assert_debug_string("P(x) & Q(y)", parse_formula("~(~P(x) | ~Q(y))").nnf());
        assert_debug_string("(~P(x)) & Q(y)", parse_formula("~(~P(x) -> ~Q(y))").nnf());
        assert_debug_string("(P(x) & Q(x)) | (P(y) & Q(y))", parse_formula("~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))").nnf());
        assert_debug_string("(P(x) & Q(x)) & (P(y) & Q(y))", parse_formula("~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))").nnf());
        assert_debug_string("((~P(x)) | (~Q(x))) & (P(y) & Q(y))", parse_formula("~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))").nnf());
        assert_debug_string("(((~P(x)) | (~Q(x))) & (P(y) & Q(y))) | ((P(x) & Q(x)) & ((~P(y)) | (~Q(y))))",
                            parse_formula("~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))").nnf());
        assert_debug_string("! x. (? y. (P(x) & (~Q(y))))", parse_formula("~?x. !y. (P(x) -> Q(y))").nnf());
        assert_debug_string("(! x. (~P(x))) | (? y. (~Q(y)))", parse_formula("~((?x. P(x)) & (!y. Q(y)))").nnf());
    }

    #[test]
    fn test_cnf() {
        assert_debug_string("TRUE", parse_formula("TRUE").cnf());
        assert_debug_string("FALSE", parse_formula("FALSE").cnf());
        assert_debug_string("P(f(), g(f(), f()))", parse_formula("P(f(), g(f(), f()))").cnf());
        assert_debug_string("P(x)", parse_formula("P(x)").cnf());
        assert_debug_string("x = y", parse_formula("x=y").cnf());
        assert_debug_string("P(x) & Q(y)", parse_formula("P(x) & Q(y)").cnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("P(x) | Q(y)").cnf());
        assert_debug_string("(~P(x)) | Q(y)", parse_formula("P(x) -> Q(y)").cnf());
        assert_debug_string("((~P(x)) | Q(y)) & ((~Q(y)) | P(x))", parse_formula("P(x) <=> Q(y)").cnf());
        assert_debug_string("P(x)", parse_formula("!x. P(x)").cnf());
        assert_debug_string("P(f(), g(f(), x))", parse_formula("!x. P(f(), g(f(), x))").cnf());
        // quantifier-free formulas
        assert_debug_string("((~P(x1)) | (~Q(y))) & ((~P(x2)) | (~Q(y)))",
                            parse_formula("~((P(x1) | P(x2)) and Q(y))").cnf());
        assert_debug_string("(P(x) | Q(x)) & (P(x) | (~Q(y)))",
                            parse_formula("P(x) | ~(Q(x) -> Q(y))").cnf());
        assert_debug_string("((~P(x)) | R(z)) & ((~Q(y)) | R(z))",
                            parse_formula("(P(x) | Q(y)) -> R(z)").cnf());
        assert_debug_string("((P(x) | (Q(x) | Q(y))) & (P(x) | (Q(x) | (~Q(x))))) & ((P(x) | ((~Q(y)) | Q(y))) & (P(x) | ((~Q(y)) | (~Q(x)))))",
                            parse_formula("P(x) | ~(Q(x) <=> Q(y))").cnf());
        assert_debug_string("(((~P(x)) | R(z)) & ((~Q(y)) | R(z))) & ((~R(z)) | (P(x) | Q(y)))",
                            parse_formula("(P(x) | Q(y)) <=> R(z)").cnf());
        assert_debug_string("(P(x) | (Q(x) | R(y))) & (P(x) | (Q(x) | R(z)))",
                            parse_formula("P(x) | (Q(x) | (R(y) & R(z)))").cnf());
        assert_debug_string("((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & ((P(x2) | Q(x1)) & (P(x2) | Q(x2)))",
                            parse_formula("(P(x1) & P(x2)) | (Q(x1) & Q(x2))").cnf());
        //random formulas
        assert_debug_string("P('sk#0)", parse_formula("?x. P(x)").cnf());
        assert_debug_string("P('sk#0) & Q(f(), 'sk#0)", parse_formula("?x. (P(x) & Q(f(), x))").cnf());
        assert_debug_string("((~P(y)) | (~Q(x, y))) | R(x)",
                            parse_formula("!x. ((? y. P(y) & Q(x, y))  -> R(x))").cnf());
        assert_debug_string("(~P(x)) | ((~Q(y)) | (~R(x, y)))",
                            parse_formula("!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))").cnf());
        assert_debug_string("((~P(y, sk#0(y))) | Q(y)) & ((~Q(sk#0(y))) | Q(y))",
                            parse_formula("!y. (!x. (P(y, x) | Q(x)) -> Q(y))").cnf());
        assert_debug_string("P('sk#0, 'sk#1)", parse_formula("?x. ?y. P(x, y)").cnf());
        assert_debug_string("P('sk#0, 'sk#1)", parse_formula("?x, y. P(x, y)").cnf());
        assert_debug_string("P(x, sk#0(x))", parse_formula("!x. ?y. P(x, y)").cnf());
        assert_debug_string("((~R(z)) | P(sk#0(z), x)) & (((~R(z)) | (~Q(u`, x`, y))) & ((~R(z)) | (~(w = f(u`)))))",
                            parse_formula("R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))").cnf());
        assert_debug_string("(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                            parse_formula("!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))").cnf());
        assert_debug_string("P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                            parse_formula("?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))").cnf());
        assert_debug_string("((~P(x)) | ((~P(y)) | P(f(x, y)))) & (((~P(x)) | Q(x, sk#0(x, y))) & ((~P(x)) | (~P(sk#0(x, y)))))",
                            parse_formula("!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))").cnf());
    }

    #[test]
    fn test_dnf() {
        assert_debug_string("TRUE", parse_formula("TRUE").dnf());
        assert_debug_string("FALSE", parse_formula("FALSE").dnf());
        assert_debug_string("P(f(), g(f(), f()))", parse_formula("P(f(), g(f(), f()))").dnf());
        assert_debug_string("P(x)", parse_formula("P(x)").dnf());
        assert_debug_string("x = y", parse_formula("x=y").dnf());
        assert_debug_string("P(x) & Q(y)", parse_formula("P(x) & Q(y)").dnf());
        assert_debug_string("P(x) | Q(y)", parse_formula("P(x) | Q(y)").dnf());
        assert_debug_string("(~P(x)) | Q(y)", parse_formula("P(x) -> Q(y)").dnf());
        assert_debug_string("(((~P(x)) & (~Q(y))) | ((~P(x)) & P(x))) | ((Q(y) & (~Q(y))) | (Q(y) & P(x)))", parse_formula("P(x) <=> Q(y)").dnf());
        assert_debug_string("P(x)", parse_formula("!x. P(x)").dnf());
        assert_debug_string("P(f(), g(f(), x))", parse_formula("!x. P(f(), g(f(), x))").dnf());
        // quantifier-free formulas
        assert_debug_string("((~P(x1)) & (~P(x2))) | (~Q(y))",
                            parse_formula("~((P(x1) | P(x2)) and Q(y))").dnf());
        assert_debug_string("P(x) | (Q(x) & (~Q(y)))",
                            parse_formula("P(x) | ~(Q(x) -> Q(y))").dnf());
        assert_debug_string("((~P(x)) & (~Q(y))) | R(z)",
                            parse_formula("(P(x) | Q(y)) -> R(z)").dnf());
        assert_debug_string("P(x) | ((Q(x) & (~Q(y))) | (Q(y) & (~Q(x))))",
                            parse_formula("P(x) | ~(Q(x) <=> Q(y))").dnf());
        assert_debug_string("((((~P(x)) & (~Q(y))) & (~R(z))) | ((((~P(x)) & (~Q(y))) & P(x)) | (((~P(x)) & (~Q(y))) & Q(y)))) | ((R(z) & (~R(z))) | ((R(z) & P(x)) | (R(z) & Q(y))))",
                            parse_formula("(P(x) | Q(y)) <=> R(z)").dnf());
        assert_debug_string("P(x) | (Q(x) | (R(y) & R(z)))",
                            parse_formula("P(x) | (Q(x) | (R(y) & R(z)))").dnf());
        assert_debug_string("(P(x1) & P(x2)) | (Q(x1) & Q(x2))",
                            parse_formula("(P(x1) & P(x2)) | (Q(x1) & Q(x2))").dnf());
        //random formulas
        assert_debug_string("P('sk#0)", parse_formula("?x. P(x)").dnf());
        assert_debug_string("P('sk#0) & Q(f(), 'sk#0)", parse_formula("?x. (P(x) & Q(f(), x))").dnf());
        assert_debug_string("((~P(y)) | (~Q(x, y))) | R(x)",
                            parse_formula("!x. ((? y. P(y) & Q(x, y))  -> R(x))").dnf());
        assert_debug_string("(~P(x)) | ((~Q(y)) | (~R(x, y)))",
                            parse_formula("!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))").dnf());
        assert_debug_string("((~P(y, sk#0(y))) & (~Q(sk#0(y)))) | Q(y)",
                            parse_formula("!y. (!x. (P(y, x) | Q(x)) -> Q(y))").dnf());
        assert_debug_string("P('sk#0, 'sk#1)", parse_formula("?x. ?y. P(x, y)").dnf());
        assert_debug_string("P('sk#0, 'sk#1)", parse_formula("?x, y. P(x, y)").dnf());
        assert_debug_string("P(x, sk#0(x))", parse_formula("!x. ?y. P(x, y)").dnf());
        assert_debug_string("(~R(z)) | (P(sk#0(z), x) & ((~Q(u`, x`, y)) & (~(w = f(u`)))))",
                            parse_formula("R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))").dnf());
        assert_debug_string("(P(sk#0(x)) & (~Q(x, sk#0(x)))) | Q(sk#1(x), x)",
                            parse_formula("!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))").dnf());
        assert_debug_string("((P('sk#0) & (~Q('sk#0, y))) | (P('sk#0) & (y = z))) | (P('sk#0) & (~Q('sk#0, z)))",
                            parse_formula("?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))").dnf());
        assert_debug_string("(~P(x)) | (((~P(y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))) | (P(f(x, y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))))",
                            parse_formula("!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))").dnf());
    }

    #[test]
    fn test_simplify() {
        assert_debug_string("FALSE", parse_formula("~TRUE").simplify());
        assert_debug_string("TRUE", parse_formula("~FALSE").simplify());
        assert_debug_string("~P(x)", parse_formula("~P(x)").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE & TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("FALSE & FALSE").simplify());
        assert_debug_string("FALSE", parse_formula("FALSE & TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("TRUE & FALSE").simplify());
        assert_debug_string("P(x)", parse_formula("P(x) & TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("FALSE & P(x)").simplify());
        assert_debug_string("FALSE", parse_formula("P(x) & FALSE").simplify());
        assert_debug_string("P(x)", parse_formula("TRUE & P(x)").simplify());
        assert_debug_string("P(x) & Q(x)", parse_formula("P(x) & Q(x)").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE | TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("FALSE | FALSE").simplify());
        assert_debug_string("TRUE", parse_formula("FALSE | TRUE").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE | FALSE").simplify());
        assert_debug_string("TRUE", parse_formula("P(x) | TRUE").simplify());
        assert_debug_string("P(x)", parse_formula("FALSE | P(x)").simplify());
        assert_debug_string("P(x)", parse_formula("P(x) | FALSE").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE | P(x)").simplify());
        assert_debug_string("P(x) | Q(x)", parse_formula("P(x) | Q(x)").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE -> TRUE").simplify());
        assert_debug_string("TRUE", parse_formula("FALSE -> FALSE").simplify());
        assert_debug_string("TRUE", parse_formula("FALSE -> TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("TRUE -> FALSE").simplify());
        assert_debug_string("TRUE", parse_formula("P(x) -> TRUE").simplify());
        assert_debug_string("TRUE", parse_formula("FALSE -> P(x)").simplify());
        assert_debug_string("~P(x)", parse_formula("P(x) -> FALSE").simplify());
        assert_debug_string("P(x)", parse_formula("TRUE -> P(x)").simplify());
        assert_debug_string("P(x) -> Q(x)", parse_formula("P(x) -> Q(x)").simplify());
        assert_debug_string("TRUE", parse_formula("TRUE <=> TRUE").simplify());
        assert_debug_string("TRUE", parse_formula("FALSE <=> FALSE").simplify());
        assert_debug_string("FALSE", parse_formula("FALSE <=> TRUE").simplify());
        assert_debug_string("FALSE", parse_formula("TRUE <=> FALSE").simplify());
        assert_debug_string("P(x)", parse_formula("P(x) <=> TRUE").simplify());
        assert_debug_string("~P(x)", parse_formula("FALSE <=> P(x)").simplify());
        assert_debug_string("~P(x)", parse_formula("P(x) <=> FALSE").simplify());
        assert_debug_string("P(x)", parse_formula("TRUE <=> P(x)").simplify());
        assert_debug_string("P(x) <=> Q(x)", parse_formula("P(x) <=> Q(x)").simplify());
        assert_debug_string("? y. P(y, z)", parse_formula("?x, y. P(y, z)").simplify());
        assert_debug_string("? x. P(x)", parse_formula("?x. P(x)").simplify());
        assert_debug_string("P(y)", parse_formula("?x. P(y)").simplify());
        assert_debug_string("! y. P(y, z)", parse_formula("!x, y. P(y, z)").simplify());
        assert_debug_string("! x. P(x)", parse_formula("!x. P(x)").simplify());
        assert_debug_string("P(y)", parse_formula("!x. P(y)").simplify());
        // random formulas
        assert_debug_string("P(x)", parse_formula("~~P(x)").simplify());
        assert_debug_string("~P(x)", parse_formula("~~~P(x)").simplify());
        assert_debug_string("TRUE", parse_formula("~(TRUE -> FALSE)").simplify());
        assert_debug_string("P(x)", parse_formula("FALSE | (P(x) & TRUE)").simplify());
        assert_debug_string("TRUE", parse_formula("?x. P(x) | TRUE").simplify());
        assert_debug_string("~P(x)", parse_formula("?y. (P(x) -> FALSE) & (FALSE -> Q(x))").simplify());
        assert_debug_string("TRUE", parse_formula("!x. ?y. P(x, y) | TRUE").simplify());
        assert_debug_string("x = y", parse_formula("(((x = y -> FALSE) -> FALSE) -> FALSE) -> FALSE").simplify());
        assert_debug_string("! x. (P(x) | (w = x))", parse_formula("!x, y, z. ?z. P(x) | w = x").simplify());
        assert_debug_string("TRUE", parse_formula("(P(x) | FALSE) | (P(x) | TRUE)").simplify());
        assert_debug_string("FALSE", parse_formula("(P(x) & FALSE) & (P(x) & TRUE)").simplify());
    }

    #[test]
    fn test_gnf() {
        assert_debug_strings("TRUE -> TRUE", parse_formula("TRUE").gnf());
        assert_debug_strings("TRUE -> FALSE", parse_formula("FALSE").gnf());
        assert_debug_strings("TRUE -> P(x)", parse_formula("P(x)").gnf());
        assert_debug_strings("TRUE -> (x = y)", parse_formula("x = y").gnf());
        assert_debug_strings("P(x) -> FALSE", parse_formula("~P(x)").gnf());
        assert_debug_strings("P(x) -> Q(x)", parse_formula("P(x) -> Q(x)").gnf());
        assert_debug_strings("TRUE -> P(x)\n\
        TRUE -> Q(x)", parse_formula("P(x) & Q(x)").gnf());
        assert_debug_strings("TRUE -> (P(x) | Q(x))", parse_formula("P(x) | Q(x)").gnf());
        assert_debug_strings("TRUE -> P(x)", parse_formula("! x. P(x)").gnf());
        assert_debug_strings("TRUE -> P('sk#0)", parse_formula("? x. P(x)").gnf());
        assert_debug_strings("(P(x) & Q(x)) -> (P(y) | Q(y))", parse_formula("P(x) & Q(x) -> P(y) | Q(y)").gnf());
        assert_debug_strings("P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)", parse_formula("P(x) | Q(x) -> P(y) & Q(y)").gnf());
        assert_debug_strings("P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)\n\
        (P(y) & Q(y)) -> (P(x) | Q(x))", parse_formula("P(x) | Q(x) <=> P(y) & Q(y)").gnf());
        assert_debug_strings("P(x) -> Q(x, sk#0(x))", parse_formula("!x. (P(x) -> ?y. Q(x,y))").gnf());
        assert_debug_strings("P(x) -> (Q(sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (Q(sk#0(x)) | S(x, sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | S(x, sk#1(x)))",
                             parse_formula("!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))").gnf());
        assert_debug_strings("((P(x) & Q(y)) & R(x, y)) -> S(x, y)",
                             parse_formula("!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))").gnf());
        assert_debug_strings("((P(x) & Q(y)) & R(x, y)) -> S(x, y)\n\
        ((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n\
        TRUE -> ((R(x, y) | S(x, y)) | P(x))\n\
        TRUE -> ((R(x, y) | S(x, y)) | Q(y))\n\
        R(x, y) -> (R(x, y) | P(x))\n\
        R(x, y) -> (R(x, y) | Q(y))\n\
        S(x, y) -> (S(x, y) | P(x))\n\
        S(x, y) -> (S(x, y) | Q(y))\n\
        (S(x, y) & R(x, y)) -> P(x)\n\
        (S(x, y) & R(x, y)) -> Q(y)", parse_formula("!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))").gnf());
        assert_debug_strings("P(x`) -> Q(x)",
                             parse_formula("? x. P(x) -> Q(x)").gnf());
        assert_debug_strings("P('sk#0) -> Q('sk#0)",
                             parse_formula("? x. (P(x) -> Q(x))").gnf());
        assert_debug_strings("TRUE -> TRUE",
                             parse_formula("FALSE -> P(x)").gnf());
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of heads works properly:
        assert_debug_strings("TRUE -> (P('a) & P('b))",
                             parse_theory_unsafe("P('a); P('b);").gnf().formulas);
        assert_debug_strings("TRUE -> P(x)\nTRUE -> P('a)",
                             parse_theory_unsafe("P('a); P(x);").gnf().formulas);
        assert_debug_strings("TRUE -> P(x)\nTRUE -> (P(\'a) & P(\'b))",
                             parse_theory_unsafe("P('a); P(x); P('b);").gnf().formulas);
        assert_debug_strings("TRUE -> ((T() & V()) | (U() & V()))",
                             parse_theory_unsafe("(T() and V()) or (U() and V());").gnf().formulas);
    }
}