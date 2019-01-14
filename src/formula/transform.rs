use super::syntax::*;
use super::syntax::Term::*;
use super::syntax::Formula::*;
use std::collections::HashMap;

const EXPECTED_NNF_FORMULA: &str = "Internal Error: Expecting a formula in negation normal form.";

/// ## Substitution
/// A *substitution* is a function from variables to terms. A *variable renaming* function is a
/// function from variables to variables as a special case of substitution.

/// A substitution map converts a map (collections::HashMap) from variables to terms to a Substitution.
fn substitution_map<'t>(sub: &'t HashMap<V, Term>) -> impl Fn(&V) -> Term + 't {
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

                if let Forall { ref variables, ref formula } = left {
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
                } else if let Exists { ref variables, ref formula } = left {
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
                } else if let Forall { ref variables, ref formula } = right {
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
                } else if let Exists { ref variables, ref formula } = right {
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

                if let Forall { ref variables, ref formula } = left {
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
                } else if let Exists { ref variables, ref formula } = left {
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
                } else if let Forall { ref variables, ref formula } = right {
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
                } else if let Exists { ref variables, ref formula } = right {
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
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::test_prelude::*;
    use std::collections::HashMap;

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<V, Term> = HashMap::new();
            assert_eq!(x(), x().substitute(&substitution_map(&map)));
        }
        {
            let mut map: HashMap<V, Term> = HashMap::new();
            map.insert(_x(), y());
            assert_eq!(y(), x().substitute(&substitution_map(&map)));
        }
        {
            let mut map: HashMap<V, Term> = HashMap::new();
            map.insert(_x(), g().app1(z()));
            map.insert(_y(), h().app2(z(), y()));
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
        assert_debug_string("? x. (~(~P(x)))",parse_formula("~~?x.P(x)").pnf());
        assert_debug_string("! x. (~(~P(x)))",parse_formula("~~!x.P(x)").pnf());
        assert_debug_string("! x`. (P(x) & (Q(x`) & R(x)))",parse_formula("P(x) & ((! x. Q(x)) & R(x))").pnf());
        assert_debug_string("? x`. (P(x) & (Q(x`) & R(x)))",parse_formula("P(x) & ((? x. Q(x)) & R(x))").pnf());
        assert_debug_string("! x`. (P(x) | (Q(x`) | R(x)))",parse_formula("P(x) | ((! x. Q(x)) | R(x))").pnf());
        assert_debug_string("? x`. (P(x) | (Q(x`) | R(x)))",parse_formula("P(x) | ((? x. Q(x)) | R(x))").pnf());
        assert_debug_string("? x`. (P(x) -> (Q(x`) -> R(x)))",parse_formula("P(x) -> ((! x. Q(x)) -> R(x))").pnf());
        assert_debug_string("! x`. (P(x) -> (Q(x`) -> R(x)))",parse_formula("P(x) -> ((? x. Q(x)) -> R(x))").pnf());
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
}