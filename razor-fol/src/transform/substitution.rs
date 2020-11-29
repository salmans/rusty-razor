/*! Provides an interface and the implementation for term substitution and variable renaming.*/

use crate::syntax::{Term::*, *};
use std::collections::HashMap;

/// Is the trait of types that map variables to terms.
pub trait Substitution {
    /// Maps `v` to a [`Term`].
    ///
    /// [`Term`]: crate::syntax::Term
    fn apply(&self, v: &V) -> Term;
}

/// Any function from [`V`] to [`Term`] is a substitution.
///
/// [`V`]: crate::syntax::V
/// [`Term`]: crate::syntax::Term
impl<F> Substitution for F
where
    F: Fn(&V) -> Term,
{
    fn apply(&self, v: &V) -> Term {
        self(v)
    }
}

/// Any map from [`V`] to [`Term`] is a substitution.
///
/// [`V`]: crate::syntax::V
/// [`Term`]: crate::syntax::Term
impl Substitution for HashMap<&V, Term> {
    fn apply(&self, v: &V) -> Term {
        self.get(v).cloned().unwrap_or_else(|| v.clone().into())
    }
}

/// Is the trait of types that map variables to variables.
///
/// **Note**: A variable renaming may be regarded as a special case of [`Substitution`].
///
/// [`Substitution`]: crate::transform::Substitution
pub trait VariableRenaming {
    /// Maps `v` to another [`V`].
    ///
    /// [`V`]: crate::syntax::V
    fn apply(&self, v: &V) -> V;
}

/// Any function from [`V`] to [`Term`] is a variable renaming.
///
/// [`V`]: crate::syntax::V
/// [`Term`]: crate::syntax::Term
impl<F> VariableRenaming for F
where
    F: Fn(&V) -> V,
{
    fn apply(&self, v: &V) -> V {
        self(v)
    }
}

/// Any map from [`V`] to [`Term`] is a variable renaming.
///
/// [`V`]: crate::syntax::V
/// [`Term`]: crate::syntax::Term
impl VariableRenaming for HashMap<&V, V> {
    fn apply(&self, v: &V) -> V {
        self.get(v).cloned().unwrap_or_else(|| v.clone())
    }
}

/// Is the trait of objects constructed atop [`Term`]s.
///
/// [`Term`]: crate::syntax::Term
pub trait TermBased {
    /// Applies a transformation function `f` on the [`Term`]s of the receiver.
    ///
    /// [`Term`]: crate::syntax::Term
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self;

    /// Applies a [`VariableRenaming`] on the variable sub-terms of the receiver.
    ///
    /// [`VariableRenaming`]: crate::transform::VariableRenaming
    /// **Example**:
    /// ```rust
    /// # use razor_fol::{syntax::{V, C, F, Term}, term};
    /// use razor_fol::transform::TermBased;
    /// use std::collections::HashMap;
    ///
    /// // variable symbols:
    /// let x_sym = V::from("x");
    /// let y_sym = V::from("y");
    /// let z_sym = V::from("z");
    /// let a_sym = V::from("a");
    /// let b_sym = V::from("b");
    ///
    /// // A variable renaming map that renames variable `x` to `a` and variable `y` to `b`
    /// let mut renaming = HashMap::new();
    /// renaming.insert(&x_sym, a_sym);
    /// renaming.insert(&y_sym, b_sym);
    ///
    /// let x = Term::from(x_sym.clone());
    /// let y = Term::from(y_sym.clone());
    /// let z = Term::from(z_sym.clone());
    /// let f = F::from("f");
    /// let g = F::from("g");
    ///
    /// let t = term!(f(x, z, g(x, y, x)));
    ///
    /// let s = t.rename_vars(&renaming); // s = f(a, z, g(a, b, a))
    /// assert_eq!("f(a, z, g(a, b, a))", s.to_string())
    /// ```
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self;

    /// Applies a [`Substitution`] on the variable sub-terms of the receiver.
    ///
    /// [`Substitution`]: crate::transform::Substitution
    /// **Example**:
    /// ```rust
    /// # use razor_fol::{syntax::{V, C, F, Term}, term};
    /// use razor_fol::transform::TermBased;
    ///
    /// // A substitution function that maps all variable symbols `x` to a constant term `c`.
    /// // Otherwise, wraps the variable symbol in a variable term.
    /// fn x_to_c(v: &V) -> Term {
    ///     let x = V::from("x");
    ///     let c = C::from("c");
    ///
    ///     if v == &x {
    ///         Term::from(c)
    ///     } else {
    ///         Term::from(v.clone())
    ///     }
    /// }
    ///
    /// let x = Term::from(V::from("x"));
    /// let y = Term::from(V::from("y"));
    /// let f = F::from("f");
    /// let g = F::from("g");
    ///
    /// let t = term!(f(x, g(x, y, x)));
    ///
    /// let s = t.substitute(&x_to_c); // s = f('c, g('c, y, 'c))
    /// assert_eq!("f('c, g('c, y, 'c))", s.to_string())
    /// ```
    fn substitute(&self, sub: &impl Substitution) -> Self;
}

impl TermBased for Term {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        f(self)
    }

    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => Term::from(renaming.apply(v)),
            App { function, terms } => {
                let terms = terms.iter().map(|t| t.rename_vars(renaming)).collect();
                function.clone().app(terms)
            }
        }
    }

    fn substitute(&self, sub: &impl Substitution) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => sub.apply(v),
            App { function, terms } => {
                let terms = terms.iter().map(|t| t.substitute(sub)).collect();
                function.clone().app(terms)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::FOF::*;
    use super::*;
    use crate::{fof, term, v};

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<&V, Term> = HashMap::new();
            assert_eq!(term!(x), term!(x).substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &v!(x);
            let y_var = term!(y);

            map.insert(x_v, y_var);
            assert_eq!(term!(y), term!(x).substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &v!(x);
            let y_v = &v!(y);
            let term_1 = term!(g(z));
            let term_2 = term!(h(z, y));

            map.insert(x_v, term_1);
            map.insert(y_v, term_2);
            assert_eq!(term!(f(g(z), h(z, y))), term!(f(x, y)).substitute(&map));
        }
    }

    #[test]
    fn test_rename_term() {
        assert_eq!(term!(x), term!(x).rename_vars(&|v: &V| v.clone()));
        assert_eq!(
            term!(y),
            term!(x).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(x),
            term!(x).rename_vars(&|v: &V| {
                if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(y)),
            term!(f(x)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(x)),
            term!(f(x)).rename_vars(&|v: &V| {
                if *v == v!(z) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(z, z)),
            term!(f(x, y)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(y, g(y, h(z)))),
            term!(f(x, g(x, h(y)))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
    }

    #[test]
    fn test_substitute_term() {
        assert_eq!(term!(x), term!(x).substitute(&|v: &V| v.clone().into()));
        assert_eq!(
            term!(@a),
            term!(@a).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(y),
            term!(x).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(@a),
            term!(x).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(@a)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(z)),
            term!(x).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(z))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(x),
            term!(x).substitute(&|v: &V| {
                if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(y)),
            term!(f(x)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(g(h(y, z)))),
            term!(f(x)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(g(h(y, z)))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(x)),
            term!(f(x)).substitute(&|v: &V| {
                if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(g(z), h(z, y))),
            term!(f(x, y)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(g(z))
                } else if *v == v!(y) {
                    term!(h(z, y))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(f(f()), g(f(f()), h(z)))),
            term!(f(x, g(x, h(y)))).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(f()))
                } else if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(f(@a), g(f(@a), h(z)))),
            term!(f(x, g(x, h(y)))).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(@a))
                } else if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
    }

    #[test]
    fn test_rename_formula() {
        assert_eq!(
            Top,
            Top.rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            Bottom,
            Bottom.rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((z) = (z)),
            fof!((x) = (y)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(P(x)),
            fof!(P(x)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(x)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(P(y)),
            fof!(P(x)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(P(y, z, y)),
            fof!(P(x, y, x)).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(~(P(y, z, y))),
            fof!(~(P(x, y, x))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((P(z)) & (Q(z))),
            fof!((P(x)) & (Q(y))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((P(z)) | (Q(z))),
            fof!((P(x)) | (Q(y))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((P(z)) -> (Q(z))),
            fof!((P(x)) -> (Q(y))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((P(z)) <=> (Q(z))),
            fof!((P(x)) <=> (Q(y))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(z)
                } else if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(? x, y. (P(y, y, y))),
            fof!(? x, y. (P(x, y, z))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else if *v == v!(z) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(! x, y. (P(y, y, y))),
            fof!(! x, y. (P(x, y, z))).rename_vars(&|v: &V| {
                if *v == v!(x) {
                    v!(y)
                } else if *v == v!(z) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(? x. ((!y. ((P(y)) | ((Q(z)) & (R(z))))) & (~((z) = (z))))),
            fof!(? x. ((!y. ((P(x)) | ((Q(y)) & (R(z))))) & (~((y) = (y))))).rename_vars(
                &|v: &V| {
                    if *v == v!(x) {
                        v!(y)
                    } else if *v == v!(y) {
                        v!(z)
                    } else {
                        v.clone()
                    }
                }
            )
        );
    }

    #[test]
    fn test_substitute_formula() {
        assert_eq!(
            Top,
            Top.substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            Bottom,
            Bottom.substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({ f(g(z)) } = { g(f(z)) }),
            fof!((x) = (y)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(g(z)))
                } else if *v == v!(y) {
                    term!(g(f(z)))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(P(h(y))),
            fof!(P(x)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(h(y))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(P(g(g(x)))),
            fof!(P(x)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(g(g(x)))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(P(y, f(z), y)),
            fof!(P(x, y, x)).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else if *v == v!(y) {
                    term!(f(z))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(~{P(h(), z, h())}),
            fof!(~{P(x, y, x)}).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(h())
                } else if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({ P(f(g())) } & { Q(h(z)) }),
            fof!({ P(x) } & { Q(y) }).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(g()))
                } else if *v == v!(y) {
                    term!(h(z))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({ P(f(g())) } | { Q(h(z)) }),
            fof!({ P(x) } | { Q(y) }).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(g()))
                } else if *v == v!(y) {
                    term!(h(z))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({ P(f()) } -> { Q(g()) }),
            fof!({ P(x) } -> { Q(y) }).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f())
                } else if *v == v!(y) {
                    term!(g())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({P(@a)} -> {Q(@b)}),
            fof!({P(x)} -> {Q(y)}).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(@a)
                } else if *v == v!(y) {
                    term!(@b)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({P(f())} <=> {Q(g())}),
            fof!({P(x)} <=> {Q(y)}).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f())
                } else if *v == v!(y) {
                    term!(g())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({P(@a)} <=> {Q(@b)}),
            fof!({P(x)} <=> {Q(y)}).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(@a)
                } else if *v == v!(y) {
                    term!(@b)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(? x, y. (P(f(g(y)), y, y))),
            fof!(? x, y. (P(x, y, z))).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(g(y)))
                } else if *v == v!(z) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(!x, y. (P(f(g(y)), y, y))),
            fof!(!x, y. (P(x, y, z))).substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(f(g(y)))
                } else if *v == v!(z) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(
                ? x. (
                    (!y. (
                        (P(y)) | ((Q(z)) & (R(z))))
                    ) & (~((z) = (z)))
                )
            ),
            fof!(
                ? x. (
                    (!y. (
                        (P(x)) | ((Q(y)) & (R(z))))
                    ) & (~((y) = (z)))
                )
            )
            .substitute(&|v: &V| {
                if *v == v!(x) {
                    term!(y)
                } else if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
    }
}
