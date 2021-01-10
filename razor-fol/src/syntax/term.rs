/*! Defines the syntax for first-order terms. */
use super::{formula::Equals, signature::FSig, Const, Error, Func, Sig, Var, FOF};
use std::{collections::HashMap, fmt};

/// Is the trait of types that act as terms.
pub trait Term {
    /// Returns the signature on which the term is defined. It returns an error if
    /// the underlying signature is inconsistent.
    fn signature(&self) -> Result<Sig, Error>;

    /// Returns a list of variable symbols in the receiver.
    ///
    /// **Note**: In the list of free variables, each variable symbol appears only once
    /// even if it is present at multiple positions of the receiver.
    ///
    /// **Example**:
    /// ```rust
    /// use razor_fol::{term, syntax::{Var, Term}};
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = Var::from("x");
    /// let y = Var::from("y");
    /// let z = Var::from("z");
    ///
    /// let term = term!(f(g(f(x, y), @c, z), x));
    ///
    /// assert_eq!(vec![&x, &y, &z], term.vars());
    /// ```
    fn vars(&self) -> Vec<&Var>;

    /// Applies a transformation function `f` on recursively the subterms of the receiver.
    ///
    /// [`Term`]: crate::syntax::Term
    fn transform(&self, f: &impl Fn(&Self) -> Self) -> Self;

    /// Applies a [`Renaming`] recursively on the variable terms of the receiver.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::{syntax::{Var, Const, Func}, term};
    /// use razor_fol::syntax::{Formula, Term, term::Complex};
    /// use std::collections::HashMap;
    ///
    /// // variable symbols:
    /// let x_sym = Var::from("x");
    /// let y_sym = Var::from("y");
    /// let z_sym = Var::from("z");
    /// let a_sym = Var::from("a");
    /// let b_sym = Var::from("b");
    ///
    /// // A variable renaming map that renames variable `x` to `a` and variable `y` to `b`
    /// let mut renaming = HashMap::new();
    /// renaming.insert(&x_sym, a_sym);
    /// renaming.insert(&y_sym, b_sym);
    ///
    /// let x = Complex::from(x_sym.clone());
    /// let y = Complex::from(y_sym.clone());
    /// let z = Complex::from(z_sym.clone());
    /// let f = Func::from("f");
    /// let g = Func::from("g");
    ///
    /// let t = term!(f(x, z, g(x, y, x)));
    ///
    /// let s = t.rename_vars(&renaming); // s = f(a, z, g(a, b, a))
    /// assert_eq!("f(a, z, g(a, b, a))", s.to_string())
    /// ```
    fn rename_vars(&self, renaming: &impl Renaming) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self| t.rename_vars(renaming))
    }

    /// Applies a [`Substitution`] recursively on the variable subterms of the receiver.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::{syntax::{Var, Const, Func, term::Complex}, term};
    /// use razor_fol::syntax::Term;
    ///
    /// // A substitution function that maps all variable symbols `x` to a constant term `c`.
    /// // Otherwise, wraps the variable symbol in a variable term.
    /// fn x_to_c(v: &Var) -> Complex {
    ///     let x = Var::from("x");
    ///     let c = Const::from("c");
    ///
    ///     if v == &x {
    ///         Complex::from(c)
    ///     } else {
    ///         Complex::from(v.clone())
    ///     }
    /// }
    ///
    /// let x = Complex::from(Var::from("x"));
    /// let y = Complex::from(Var::from("y"));
    /// let f = Func::from("f");
    /// let g = Func::from("g");
    ///
    /// let t = term!(f(x, g(x, y, x)));
    ///
    /// let s = t.substitute(&x_to_c); // s = f('c, g('c, y, 'c))
    /// assert_eq!("f('c, g('c, y, 'c))", s.to_string())
    /// ```
    fn substitute(&self, sub: &impl Substitution<Self>) -> Self
    where
        Self: Sized,
    {
        self.transform(&|t: &Self| t.substitute(sub))
    }
}

/// Is the trait of types that map variables to terms.
pub trait Substitution<T: Term> {
    /// Maps `v` to a [`Term`].
    ///
    /// [`Term`]: crate::syntax::Term
    fn apply(&self, v: &Var) -> T;
}

/// Any function from [`Var`] to [`Term`] is a substitution.
///
/// [`Var`]: crate::syntax::Var
/// [`Term`]: crate::syntax::Term
impl<F, T> Substitution<T> for F
where
    T: Term,
    F: Fn(&Var) -> T,
{
    fn apply(&self, v: &Var) -> T {
        self(v)
    }
}

/// Any map from [`Var`] to [`Term`] is a substitution.
///
/// [`Var`]: crate::syntax::Var
/// [`Term`]: crate::syntax::Term
impl<T> Substitution<T> for HashMap<&Var, T>
where
    T: Term + Clone + From<Var>,
{
    fn apply(&self, v: &Var) -> T {
        self.get(v).cloned().unwrap_or_else(|| v.clone().into())
    }
}

/// Is the trait of types that map variables to variables.
///
/// **Note**: A variable renaming may be regarded as a special case of [`Substitution`].
pub trait Renaming {
    /// Maps `v` to another [`Var`].
    ///
    /// [`Var`]: crate::syntax::Var
    fn apply(&self, v: &Var) -> Var;
}

/// Any function from [`Var`] to [`Term`] is a variable renaming.
///
/// [`Var`]: crate::syntax::Var
/// [`Term`]: crate::syntax::Term
impl<F> Renaming for F
where
    F: Fn(&Var) -> Var,
{
    fn apply(&self, v: &Var) -> Var {
        self(v)
    }
}

/// Any map from [`Var`] to [`Term`] is a variable renaming.
///
/// [`Var`]: crate::syntax::Var
/// [`Term`]: crate::syntax::Term
impl Renaming for HashMap<&Var, Var> {
    fn apply(&self, v: &Var) -> Var {
        self.get(v).cloned().unwrap_or_else(|| v.clone())
    }
}

/// Represents a (complex) first-order term and consists of variables, constants and function applications.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Complex {
    /// Is a variable term, wrapping a [variable symbol].
    ///
    /// [variable symbol]: crate::syntax::Var
    Var { variable: Var },

    /// Is a constant term, wrapping a [constant symbol].
    ///
    /// [constant symbol]: crate::syntax::Const
    Const { constant: Const },

    /// Recursively defines a term by applying a `function` on a list of `terms`.
    App { function: Func, terms: Vec<Complex> },
}

impl Complex {
    /// Returns an [equation] (formula) between the receiver and `term`.
    ///
    /// [equation]: crate::syntax::FOF::Equals
    ///
    pub fn equals(self, term: Self) -> FOF {
        Equals {
            left: self,
            right: term,
        }
        .into()
    }

    /// Builds a term by applying `function` on `args` as arguments.
    pub fn apply(function: Func, terms: Vec<Self>) -> Self {
        Self::App { function, terms }
    }
}

impl Term for Complex {
    fn signature(&self) -> Result<Sig, Error> {
        let mut sig = Sig::new();
        match self {
            Complex::Var { .. } => {}
            Complex::Const { constant } => sig.add_constant(constant.clone()),
            Complex::App { function, terms } => {
                for t in terms {
                    sig = sig.merge(t.signature()?)?;
                }

                sig.add_function(FSig {
                    symbol: function.clone(),
                    arity: terms.len() as u8,
                })?;
            }
        }

        Ok(sig)
    }

    fn vars(&self) -> Vec<&Var> {
        use itertools::Itertools;

        match self {
            Complex::Var { variable } => vec![variable],
            Complex::Const { constant: _ } => vec![],
            Complex::App { function: _, terms } => terms
                .iter()
                .flat_map(|t| t.vars())
                .into_iter()
                .unique()
                .collect(),
        }
    }

    fn transform(&self, f: &impl Fn(&Self) -> Self) -> Self {
        f(self)
    }

    fn rename_vars(&self, renaming: &impl Renaming) -> Self {
        match self {
            Self::Const { .. } => self.clone(),
            Self::Var { variable: v } => Complex::from(renaming.apply(v)),
            Self::App { function, terms } => {
                let terms = terms.iter().map(|t| t.rename_vars(renaming)).collect();
                function.clone().app(terms)
            }
        }
    }

    fn substitute(&self, sub: &impl Substitution<Self>) -> Self {
        match self {
            Self::Const { .. } => self.clone(),
            Self::Var { variable: v } => sub.apply(v),
            Self::App { function, terms } => {
                let terms = terms.iter().map(|t| t.substitute(sub)).collect();
                function.clone().app(terms)
            }
        }
    }
}

impl From<Var> for Complex {
    fn from(variable: Var) -> Self {
        Self::Var { variable }
    }
}

impl From<&Var> for Complex {
    fn from(variable: &Var) -> Self {
        variable.clone().into()
    }
}

impl From<Const> for Complex {
    fn from(constant: Const) -> Self {
        Self::Const { constant }
    }
}

impl fmt::Display for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Var { variable } => write!(f, "{}", variable),
            Self::Const { constant } => write!(f, "{}", constant),
            Self::App { function, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", function, ts.join(", "))
            }
        }
    }
}

impl fmt::Debug for Complex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Formula;
    use crate::{assert_eq_sorted_vecs, fof, term, v};

    #[test]
    fn test_var_vars() {
        let term = term!(x);
        let x = v!(x);
        assert_eq_sorted_vecs!(vec![&x], term.vars());
    }

    #[test]
    fn test_const_vars() {
        let expected: Vec<&Var> = Vec::new();
        let fmla = term!(@a);
        assert_eq_sorted_vecs!(expected, fmla.vars());
    }

    #[test]
    fn test_app_to_string() {
        assert_eq!("f()", term!(f()).to_string());
        assert_eq!("f(x, y)", term!(f(x, y)).to_string());
        assert_eq!("f(g(x), y)", term!(f(g(x), y)).to_string());
        assert_eq!(
            "f(f(f(f(f(f(f(x)))))))",
            term!(f(f(f(f(f(f(f(x)))))))).to_string(),
        );
    }

    #[test]
    fn test_app_vars() {
        {
            let expected: Vec<&Var> = vec![];
            let fmla = term!(f());
            assert_eq_sorted_vecs!(expected, fmla.vars());
        }
        {
            let expected: Vec<&Var> = vec![];
            let fmla = term!(f(g(h(), g())));
            assert_eq_sorted_vecs!(expected, fmla.vars());
        }
        {
            let expected = vec![v!(x)];
            let term = term!(f(x));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.vars());
        }
        {
            let expected = [v!(x), v!(y), v!(z)];
            let term = term!(f(x, y, z));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.vars());
        }
        {
            let expected = vec![v!(x), v!(y)];
            let term = term!(f(x, y, x));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            let term = term!(f(g(x), h(y, f(g(z)))));
            assert_eq_sorted_vecs!(expected.iter().collect::<Vec<_>>(), term.vars(),);
        }
    }

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<&Var, Complex> = HashMap::new();
            assert_eq!(term!(x), term!(x).substitute(&map));
        }
        {
            let mut map: HashMap<&Var, Complex> = HashMap::new();
            let x_v = &v!(x);
            let y_var = term!(y);

            map.insert(x_v, y_var);
            assert_eq!(term!(y), term!(x).substitute(&map));
        }
        {
            let mut map: HashMap<&Var, Complex> = HashMap::new();
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
        assert_eq!(term!(x), term!(x).rename_vars(&|v: &Var| v.clone()));
        assert_eq!(
            term!(y),
            term!(x).rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(x),
            term!(x).rename_vars(&|v: &Var| {
                if *v == v!(y) {
                    v!(z)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(y)),
            term!(f(x)).rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(x)),
            term!(f(x)).rename_vars(&|v: &Var| {
                if *v == v!(z) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            term!(f(z, z)),
            term!(f(x, y)).rename_vars(&|v: &Var| {
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
            term!(f(x, g(x, h(y)))).rename_vars(&|v: &Var| {
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
        assert_eq!(term!(x), term!(x).substitute(&|v: &Var| v.clone().into()));
        assert_eq!(
            term!(@a),
            term!(@a).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(y),
            term!(x).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(@a),
            term!(x).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(@a)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(z)),
            term!(x).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(f(z))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(x),
            term!(x).substitute(&|v: &Var| {
                if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(y)),
            term!(f(x)).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(g(h(y, z)))),
            term!(f(x)).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(g(h(y, z)))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(x)),
            term!(f(x)).substitute(&|v: &Var| {
                if *v == v!(y) {
                    term!(z)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            term!(f(g(z), h(z, y))),
            term!(f(x, y)).substitute(&|v: &Var| {
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
            term!(f(x, g(x, h(y)))).substitute(&|v: &Var| {
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
            term!(f(x, g(x, h(y)))).substitute(&|v: &Var| {
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
            FOF::Top,
            FOF::Top.rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            FOF::Bottom,
            FOF::Bottom.rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!((z) = (z)),
            fof!((x) = (y)).rename_vars(&|v: &Var| {
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
            fof!(P(x)).rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(x)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(P(y)),
            fof!(P(x)).rename_vars(&|v: &Var| {
                if *v == v!(x) {
                    v!(y)
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            fof!(P(y, z, y)),
            fof!(P(x, y, x)).rename_vars(&|v: &Var| {
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
            fof!(~(P(x, y, x))).rename_vars(&|v: &Var| {
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
            fof!((P(x)) & (Q(y))).rename_vars(&|v: &Var| {
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
            fof!((P(x)) | (Q(y))).rename_vars(&|v: &Var| {
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
            fof!((P(x)) -> (Q(y))).rename_vars(&|v: &Var| {
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
            fof!((P(x)) <=> (Q(y))).rename_vars(&|v: &Var| {
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
            fof!(? x, y. (P(x, y, z))).rename_vars(&|v: &Var| {
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
            fof!(! x, y. (P(x, y, z))).rename_vars(&|v: &Var| {
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
                &|v: &Var| {
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
            FOF::Top,
            FOF::Top.substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            FOF::Bottom,
            FOF::Bottom.substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(y)
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!({ f(g(z)) } = { g(f(z)) }),
            fof!((x) = (y)).substitute(&|v: &Var| {
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
            fof!(P(x)).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(h(y))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(P(g(g(x)))),
            fof!(P(x)).substitute(&|v: &Var| {
                if *v == v!(x) {
                    term!(g(g(x)))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            fof!(P(y, f(z), y)),
            fof!(P(x, y, x)).substitute(&|v: &Var| {
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
            fof!(~{P(x, y, x)}).substitute(&|v: &Var| {
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
            fof!({ P(x) } & { Q(y) }).substitute(&|v: &Var| {
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
            fof!({ P(x) } | { Q(y) }).substitute(&|v: &Var| {
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
            fof!({ P(x) } -> { Q(y) }).substitute(&|v: &Var| {
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
            fof!({P(x)} -> {Q(y)}).substitute(&|v: &Var| {
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
            fof!({P(x)} <=> {Q(y)}).substitute(&|v: &Var| {
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
            fof!({P(x)} <=> {Q(y)}).substitute(&|v: &Var| {
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
            fof!(? x, y. (P(x, y, z))).substitute(&|v: &Var| {
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
            fof!(!x, y. (P(x, y, z))).substitute(&|v: &Var| {
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
            .substitute(&|v: &Var| {
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
