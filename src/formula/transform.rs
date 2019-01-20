use super::syntax::*;
use super::syntax::Term::*;
use super::syntax::Formula::*;
use std::collections::HashMap;

/// ## Substitution
/// A *substitution* is a function from variables to terms. A *variable renaming* function is a
/// function from variables to variables as a special case of substitution.

/// A substitution map converts a map (collections::HashMap) from variables to terms to a Substitution.
fn substitution_map<'t>(sub: &'t HashMap<&V, Term>) -> impl Fn(&V) -> Term + 't {
    move |v: &V| {
        let lookup = sub.get(v);
        if let Some(t) = lookup { (*t).clone() } else { (*v).clone().var() }
    }
}

impl Term {
    /// Applies a variable renaming function on the term.
    pub fn rename_vars(&self, renaming: &impl Fn(&V) -> V) -> Term {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => Var { variable: renaming(v) },
            App { function, terms } => {
                let ts = terms.iter().map(|t| t.rename_vars(renaming)).collect();
                Term::App { function: function.clone(), terms: ts }
            }
        }
    }

    /// Applies a substitution function on the term.
    pub fn substitute(&self, substitution: &impl Fn(&V) -> Term) -> Term {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => substitution(v),
            App { function, terms } => {
                let ts = terms.iter().map(|t| t.substitute(substitution)).collect();
                Term::App { function: function.clone(), terms: ts }
            }
        }
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
    /// Applies a variable renaming function on **all** (free and bound) variables of the formula.
    pub fn rename_vars(&self, renaming: &impl Fn(&V) -> V) -> Formula {
        match self {
            Top | Bottom => self.clone(),
            Atom { predicate, terms } => {
                let ts = terms.iter().map(|t| t.rename_vars(renaming)).collect();
                Atom { predicate: predicate.clone(), terms: ts }
            }
            Equals { left, right } => Equals {
                left: left.rename_vars(renaming),
                right: right.rename_vars(renaming),
            },
            Not { formula } => Not { formula: Box::new(formula.rename_vars(renaming)) },
            And { left, right } => And {
                left: Box::new(left.rename_vars(renaming)),
                right: Box::new(right.rename_vars(renaming)),
            },
            Or { left, right } => Or {
                left: Box::new(left.rename_vars(renaming)),
                right: Box::new(right.rename_vars(renaming)),
            },
            Implies { left, right } => Implies {
                left: Box::new(left.rename_vars(renaming)),
                right: Box::new(right.rename_vars(renaming)),
            },
            Iff { left, right } => Iff {
                left: Box::new(left.rename_vars(renaming)),
                right: Box::new(right.rename_vars(renaming)),
            },
            Exists { variables, formula } => Exists {
                variables: variables.iter().map(renaming).collect(),
                formula: Box::new(formula.rename_vars(renaming)),
            },
            Forall { variables, formula } => Forall {
                variables: variables.iter().map(renaming).collect(),
                formula: Box::new(formula.rename_vars(renaming)),
            }
        }
    }

    /// Applies a substitution function on the **free** variables of the formula.
    pub fn substitute(&self, substitution: &impl Fn(&V) -> Term) -> Formula {
        match self {
            Top | Bottom => self.clone(),
            Atom { predicate, terms } => {
                let ts = terms.iter().map(|t| t.substitute(substitution)).collect();
                Atom { predicate: predicate.clone(), terms: ts }
            }
            Equals { left, right } => Equals {
                left: left.substitute(substitution),
                right: right.substitute(substitution),
            },
            Not { formula } => Not { formula: Box::new(formula.substitute(substitution)) },
            And { left, right } => And {
                left: Box::new(left.substitute(substitution)),
                right: Box::new(right.substitute(substitution)),
            },
            Or { left, right } => Or {
                left: Box::new(left.substitute(substitution)),
                right: Box::new(right.substitute(substitution)),
            },
            Implies { left, right } => Implies {
                left: Box::new(left.substitute(substitution)),
                right: Box::new(right.substitute(substitution)),
            },
            Iff { left, right } => Iff {
                left: Box::new(left.substitute(substitution)),
                right: Box::new(right.substitute(substitution)),
            },
            Exists { variables, formula } => Exists {
                variables: variables.to_vec(),
                formula: Box::new(formula.substitute(substitution)),
            },
            Forall { variables, formula } => Forall {
                variables: variables.to_vec(),
                formula: Box::new(formula.substitute(substitution)),
            }
        }
    }

    /// ## Prenex Normal Form (PNF)
    /// A Prenex Normal Form (PNF) is a formula with all quantifiers (existential and universal) and
    /// bound variables at the front, followed by a quantifier-free part.
    /// `Formula.pnf()` returns a PNF equivalent to the given formula.
    pub fn pnf(&self) -> Formula {
        use itertools::Itertools;
        // Renames the input variable until it's not in the list of input variables.
        fn rename(variable: &V, no_collision_variable_list: &Vec<&V>) -> V {
            let mut name = variable.0.clone();
            let names: Vec<String> = no_collision_variable_list.into_iter().map(|v| v.0.clone()).collect();
            // TODO: do not clone in map
            while names.contains(&name) {
                name.push_str("`")
            }
            return V::new(&name);
        }

        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { formula } => { // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
                let formula = formula.pnf();
                match formula {
                    Forall { variables, formula } => Exists {
                        variables,
                        formula: Box::new(Not { formula }.pnf()),
                    },
                    Exists { variables, formula } => Forall {
                        variables,
                        formula: Box::new(Not { formula }.pnf()),
                    },
                    _ => Not { formula: Box::new(formula) }
                }
            }
            And { left, right } => { // e.g. (Q x. F(x)) & G(y)) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = left {
                        Forall {
                            variables,
                            formula: Box::new(And { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = left {
                        Exists {
                            variables,
                            formula: Box::new(And { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Forall { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = right {
                        Forall {
                            variables,
                            formula: Box::new(And { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = right {
                        Exists {
                            variables,
                            formula: Box::new(And { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else {
                    And { left: Box::new(left), right: Box::new(right) }
                }
            }
            Or { left, right } => { // e.g. (Q x. F(x)) | G(y)) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = left {
                        Forall {
                            variables,
                            formula: Box::new(Or { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = left {
                        Exists {
                            variables,
                            formula: Box::new(Or { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Forall { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = right {
                        Forall {
                            variables,
                            formula: Box::new(Or { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = right {
                        Exists {
                            variables,
                            formula: Box::new(Or { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else {
                    Or { left: Box::new(left), right: Box::new(right) }
                }
            }
            Implies { left, right } => { // e.g. (Q x. F(x)) -> G(y)) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = left {
                        Exists {
                            variables,
                            formula: Box::new(Implies { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = left {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| right_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let left = left.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = left {
                        Forall {
                            variables,
                            formula: Box::new(Implies { left: formula, right: Box::new(right) }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Forall { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Forall { variables, formula } = right {
                        Forall {
                            variables,
                            formula: Box::new(Implies { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else if let Exists { ref variables, formula: _ } = right {
                    let shared_vars: Vec<&V> = variables.iter()
                        .filter(|v| left_free_variables.contains(v))
                        .collect();
                    let mut all_vars: Vec<&V> = variables.iter().unique().collect();
                    all_vars.append(&mut all_free_variables);
                    let right = right.rename_vars(&|v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    });
                    if let Exists { variables, formula } = right {
                        Exists {
                            variables,
                            formula: Box::new(Implies { left: Box::new(left), right: formula }),
                        }.pnf()
                    } else {
                        panic!("something went wrong!")
                    }
                } else {
                    Implies { left: Box::new(left), right: Box::new(right) }
                }
            }
            Iff { left, right } => {
                And {
                    left: Box::new(Implies { left: left.clone(), right: right.clone() }),
                    right: Box::new(Implies { left: right.clone(), right: left.clone() }),
                }.pnf()
            }
            Exists { variables, formula } => Exists {
                variables: variables.to_vec(),
                formula: Box::new(formula.pnf()),
            },
            Forall { variables, formula } => Forall {
                variables: variables.to_vec(),
                formula: Box::new(formula.pnf()),
            },
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
        fn helper(formula: Formula, skolem_vars: Vec<V>, generator: &mut SkolemGenerator) -> Formula {
            match formula {
                Forall { variables, formula } => {
                    let mut vars = skolem_vars.clone();
                    vars.append(&mut variables.clone());
                    Forall {
                        variables: variables.to_vec(),
                        formula: Box::new(helper(*formula, vars, generator)),
                    }
                }
                Exists { variables, formula } => {
                    let mut map: HashMap<&V, Term> = HashMap::new();
                    variables.iter().for_each(|v| {
                        if skolem_vars.is_empty() {
                            map.insert(&v, C::new(&generator.next()).r#const());
                        } else {
                            let vars: Vec<Term> = skolem_vars.iter().map(|v| v.clone().var()).collect();
                            map.insert(&v, Func::new(&generator.next()).app(vars));
                        }
                    });
                    let substituted = formula.substitute(&substitution_map(&map));
                    helper(substituted, skolem_vars, generator)
                }
                _ => formula
            }
        }

        // Skolemization only makes sense for PNF formulas.
        helper(self.pnf(), vec![], generator) // TODO: if we do substitution in place, helper doesn't have to create copies.
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
                    And { ref left, ref right } => Or {
                        left: Box::new(Not { formula: Box::new(*left.clone()) }.nnf()),
                        right: Box::new(Not { formula: Box::new(*right.clone()) }.nnf()),
                    },
                    Or { ref left, ref right } => And {
                        left: Box::new(Not { formula: Box::new(*left.clone()) }.nnf()),
                        right: Box::new(Not { formula: Box::new(*right.clone()) }.nnf()),
                    },
                    Implies { ref left, ref right } => And {
                        left: Box::new(left.nnf()),
                        right: Box::new(Not { formula: Box::new(*right.clone()) }.nnf()),
                    },
                    Iff { ref left, ref right } => Or {
                        left: Box::new(And {
                            left: Box::new(left.nnf()),
                            right: Box::new(Not { formula: Box::new(*right.clone()) }.nnf()),
                        }),
                        right: Box::new(And {
                            left: Box::new(Not { formula: Box::new(*left.clone()) }.nnf()),
                            right: Box::new(right.nnf()),
                        }),
                    },
                    Exists { ref variables, ref formula } => Forall {
                        variables: variables.to_vec(),
                        formula: Box::new(Not { formula: Box::new(*formula.clone()) }.nnf()),
                    },
                    Forall { ref variables, ref formula } => Exists {
                        variables: variables.to_vec(),
                        formula: Box::new(Not { formula: Box::new(*formula.clone()) }.nnf()),
                    }
                }
            }
            And { left, right } => And {
                left: Box::new(left.nnf()),
                right: Box::new(right.nnf()),
            },
            Or { left, right } => Or {
                left: Box::new(left.nnf()),
                right: Box::new(right.nnf()),
            },
            Implies { left, right } => Or {
                left: Box::new(Not { formula: Box::new(*left.clone()) }.nnf()),
                right: Box::new(right.nnf()),
            },
            Iff { left, right } => And {
                left: Box::new(Or {
                    left: Box::new(Not { formula: Box::new(*left.clone()) }.nnf()),
                    right: Box::new(right.nnf()),
                }),
                right: Box::new(Or {
                    left: Box::new(left.nnf()),
                    right: Box::new(Not { formula: Box::new(*right.clone()) }.nnf()),
                }),
            },
            Exists { variables, formula } => Exists {
                variables: variables.to_vec(),
                formula: Box::new(formula.nnf()),
            },
            Forall { variables, formula } => Forall {
                variables: variables.to_vec(),
                formula: Box::new(formula.nnf()),
            }
        }
    }

    /// ## Conjunctive Normal Form (SNF)
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
                Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(), // already NNF
                And { left, right } => And {
                    left: Box::new(distribute_or(left)),
                    right: Box::new(distribute_or(right)),
                },
                Or { left, right } => {
                    let left = distribute_or(left);
                    let right = distribute_or(right);
                    if let And { left: l, right: r } = left {
                        let l = distribute_or(&Or {
                            left: l,
                            right: Box::new(right.clone()),
                        });
                        let r = distribute_or(&Or {
                            left: r,
                            right: Box::new(right.clone()),
                        });
                        And {
                            left: Box::new(l),
                            right: Box::new(r),
                        }
                    } else if let And { left: l, right: r } = right {
                        let l = distribute_or(&Or {
                            left: Box::new(left.clone()),
                            right: l,
                        });
                        let r = distribute_or(&Or {
                            left: Box::new(left.clone()),
                            right: r,
                        });
                        And {
                            left: Box::new(l),
                            right: Box::new(r),
                        }
                    } else {
                        Or { left: Box::new(left), right: Box::new(right) }
                    }
                }
                Forall { variables, formula } => Forall {
                    variables: variables.to_vec(),
                    formula: Box::new(distribute_or(formula)),
                },
                _ => panic!("Internal Error: Expecting a formula in negation normal form.") // already NNF
            }
        }

        // The following eliminates the existential quantifiers of the input formula.
        fn remove_forall(formula: Formula) -> Formula {
            if let Forall { variables: _, formula } = formula {
                remove_forall(*formula)
            } else {
                formula
            }
        }

        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_or(&nnf))
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
                    _ => Not { formula: Box::new(formula) }
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
                    And { left: Box::new(left), right: Box::new(right) }
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
                    Or { left: Box::new(left), right: Box::new(right) }
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
                    Not { formula: Box::new(left) }.simplify()
                } else {
                    Implies { left: Box::new(left), right: Box::new(right) }
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
                    Not { formula: Box::new(right) }.simplify()
                } else if let Bottom = right {
                    Not { formula: Box::new(left) }.simplify()
                } else {
                    Iff { left: Box::new(left), right: Box::new(right) }
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
                    Exists { variables: vs, formula: Box::new(formula) }
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
                    Forall { variables: vs, formula: Box::new(formula) }
                }
            }
            _ => self.clone()
        }
    }

    /// ## Geometric Normal Form (GNF)
    /// `Formula.gnf()` returns a list of formulas in GNF, equivalent to the given formula.
    /// (see https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf)
    fn gnf(&self) -> Vec<Formula> {
        self.gnf_with(&mut SkolemGenerator::new())
    }

    /// `Formula.gnf_with(generator)` uses an existing `SkolemGenerator` to avoid collision in the
    /// names of the Skolem function (and constant) for formulas in the same theory.
    fn gnf_with(&self, generator: &mut SkolemGenerator) -> Vec<Formula> {
        use itertools::Itertools;
        // For any disjunct of the CNF, the negative literals form the body of the geometric form
        // and the positive literals form the head of the geometric form:
        fn split_sids(disjunct: Formula) -> (Vec<Formula>, Vec<Formula>) {
            match disjunct {
                Or { left, right } => {
                    let (mut left_body, mut left_head) = split_sids(*left);
                    let (mut right_body, mut right_head) = split_sids(*right);
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
            let (body, head) = split_sids(disjunct);
            let body = body.into_iter().fold(Top, |x, y| And {
                left: Box::new(x),
                right: Box::new(y),
            }).simplify();
            let head = head.into_iter().fold(Bottom, |x, y| Or {
                left: Box::new(x),
                right: Box::new(y),
            }).simplify();
            return Implies { left: Box::new(body), right: Box::new(head) };
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

        get_disjuncts(self.cnf_with(generator)).into_iter().map(to_implication).collect()
    }
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::test_prelude::*;
    use std::collections::HashMap;

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<&V, Term> = HashMap::new();
            assert_eq!(x(), x().substitute(&substitution_map(&map)));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &_x();
            let y_var = y();

            map.insert(x_v, y_var);
            assert_eq!(y(), x().substitute(&substitution_map(&map)));
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
                       f().app2(x(), y()).substitute(&substitution_map(&map)));
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
        assert_eq!(x(), x().substitute(&|v: &V| v.clone().var()));
        assert_eq!(a(), a().substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(y(), x().substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(a(), x().substitute(&|v: &V| {
            if *v == _x() {
                a()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app1(z()), x().substitute(&|v: &V| {
            if *v == _x() {
                f().app1(z())
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(x(), x().substitute(&|v: &V| {
            if *v == _y() {
                z()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app1(y()), f().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app1(g().app1(h().app2(y(), z()))), f().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                g().app1(h().app2(y(), z()))
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app1(x()), f().app1(x()).substitute(&|v: &V| {
            if *v == _y() {
                z()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app2(g().app1(z()), h().app2(z(), y())),
                   f().app2(x(), y()).substitute(&|v: &V| {
                       if *v == _x() {
                           g().app1(z())
                       } else if *v == _y() {
                           h().app2(z(), y())
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(f().app2(f().app1(f().app0()), g().app2(f().app1(f().app0()), h().app1(z()))),
                   f().app2(x(), g().app2(x(), h().app1(y()))).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(f().app0())
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(f().app2(f().app1(a()), g().app2(f().app1(a()), h().app1(z()))),
                   f().app2(x(), g().app2(x(), h().app1(y()))).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(a())
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().var()
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
        assert_eq!(exists2(_y(), _y(), P().app3(y(), y(), y())),
                   exists2(_x(), _y(), P().app3(x(), y(), z())).rename_vars(&|v: &V| {
                       if *v == _x() {
                           _y()
                       } else if *v == _z() {
                           _y()
                       } else {
                           v.clone()
                       }
                   }));
        assert_eq!(forall2(_y(), _y(), P().app3(y(), y(), y())),
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
            exists1(_y(),
                    forall1(_z(),
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
                v.clone().var()
            }
        }));
        assert_eq!(Bottom, Bottom.substitute(&|v: &V| {
            if *v == _x() {
                y()
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(f().app1(g().app1(z())).equals(g().app1(f().app1(z()))), x().equals(y()).substitute(&|v: &V| {
            if *v == _x() {
                f().app1(g().app1(z()))
            } else if *v == _y() {
                g().app1(f().app1(z()))
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(P().app1(h().app1(y())), P().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                h().app1(y())
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(P().app1(g().app1(g().app1(x()))), P().app1(x()).substitute(&|v: &V| {
            if *v == _x() {
                g().app1(g().app1(x()))
            } else {
                v.clone().var()
            }
        }));
        assert_eq!(P().app3(y(), f().app1(z()), y()),
                   P().app3(x(), y(), x()).substitute(&|v: &V| {
                       if *v == _x() {
                           y()
                       } else if *v == _y() {
                           f().app1(z())
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(not(P().app3(h().app0(), z(), h().app0())),
                   not(P().app3(x(), y(), x())).substitute(&|v: &V| {
                       if *v == _x() {
                           h().app0()
                       } else if *v == _y() {
                           z()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(f().app1(g().app0())).and(Q().app1(h().app1(z()))),
                   P().app1(x()).and(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app0())
                       } else if *v == _y() {
                           h().app1(z())
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(f().app1(g().app0())).or(Q().app1(h().app1(z()))),
                   P().app1(x()).or(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app0())
                       } else if *v == _y() {
                           h().app1(z())
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(f().app0()).implies(Q().app1(g().app0())),
                   P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app0()
                       } else if *v == _y() {
                           g().app0()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(a()).implies(Q().app1(b())),
                   P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           a()
                       } else if *v == _y() {
                           b()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(f().app0()).iff(Q().app1(g().app0())),
                   P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app0()
                       } else if *v == _y() {
                           g().app0()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(P().app1(a()).iff(Q().app1(b())),
                   P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                       if *v == _x() {
                           a()
                       } else if *v == _y() {
                           b()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(exists2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
                   exists2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app1(y()))
                       } else if *v == _z() {
                           y()
                       } else {
                           v.clone().var()
                       }
                   }));
        assert_eq!(forall2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
                   forall2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                       if *v == _x() {
                           f().app1(g().app1(y()))
                       } else if *v == _z() {
                           y()
                       } else {
                           v.clone().var()
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
                    v.clone().var()
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
        assert_debug_string("((~R(z)) | P('sk#0, x)) & (((~R(z)) | (~Q(u`, x`, y))) & ((~R(z)) | (~(w = f(u`)))))",
                            parse_formula("R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))").cnf());
        assert_debug_string("(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                            parse_formula("!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))").cnf());
        assert_debug_string("P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                            parse_formula("?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))").cnf());
        assert_debug_string("((~P(x)) | ((~P(y)) | P(f(x, y)))) & (((~P(x)) | Q(x, sk#0(x, y))) & ((~P(x)) | (~P(sk#0(x, y)))))",
                            parse_formula("!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))").cnf());
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
}