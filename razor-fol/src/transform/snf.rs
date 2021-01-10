/*! Defines formulae in Skolem Normal Form (PNF) and implements an algorithm for converting
[`PNF`] to [`SNF`].

[`PNF`]: crate::transform::PNF
*/
use super::PNF;
use crate::syntax::{formula::*, qff::QFF, term::Complex, C, F, FOF, V};
use std::collections::HashMap;

/// Represents a formula in Skolem Normal Form (SNF).
///
/// **Hint**: An SNF is a [PNF] with only universal quantifiers
/// (see: <https://en.wikipedia.org/wiki/Skolem_normal_form>).
///
/// [PNF]: crate::transform::PNF
#[derive(Clone, Debug)]
pub enum SNF {
    /// Is the quantifier-free sub-formula of an [`SNF`].
    QFF(QFF),

    /// Is a universally quantified formula, wrapping a [`Forall`].
    Forall(Box<Forall<SNF>>),
}

impl From<Atom<Complex>> for SNF {
    fn from(value: Atom<Complex>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Equals<Complex>> for SNF {
    fn from(value: Equals<Complex>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Not<QFF>> for SNF {
    fn from(value: Not<QFF>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<And<QFF>> for SNF {
    fn from(value: And<QFF>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Or<QFF>> for SNF {
    fn from(value: Or<QFF>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Implies<QFF>> for SNF {
    fn from(value: Implies<QFF>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Iff<QFF>> for SNF {
    fn from(value: Iff<QFF>) -> Self {
        Self::QFF(value.into())
    }
}

impl From<Forall<SNF>> for SNF {
    fn from(value: Forall<SNF>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<QFF> for SNF {
    fn from(value: QFF) -> Self {
        Self::QFF(value)
    }
}

impl From<&PNF> for SNF {
    fn from(value: &PNF) -> Self {
        value.snf()
    }
}

impl SNF {
    /// Creates a new formula in SNF from a [`PNF`], a list of skolem variables, and
    /// a `generator` function for creating fresh skolem functions.
    fn new<CG, FG>(
        pnf: PNF,
        mut skolem_vars: Vec<V>,
        const_generator: &mut CG,
        fn_generator: &mut FG,
    ) -> Self
    where
        CG: FnMut() -> C,
        FG: FnMut() -> F,
    {
        match pnf {
            PNF::Forall(this) => {
                let variables = this.variables;
                skolem_vars.append(&mut variables.to_vec());
                SNF::forall(
                    variables.to_vec(),
                    Self::new(this.formula, skolem_vars, const_generator, fn_generator),
                )
            }
            PNF::Exists(this) => {
                let variables = this.variables;
                let mut map: HashMap<&V, Complex> = HashMap::new();

                variables.iter().for_each(|v| {
                    if skolem_vars.is_empty() {
                        map.insert(&v, const_generator().into());
                    } else {
                        let vars: Vec<Complex> =
                            skolem_vars.iter().map(|v| v.clone().into()).collect();
                        map.insert(&v, fn_generator().app(vars));
                    }
                });

                let substituted = this.formula.substitute(&map);
                Self::new(substituted, skolem_vars, const_generator, fn_generator)
            }
            PNF::QFF(this) => this.into(),
        }
    }

    /// Creates a universally quantified [`SNF`].
    #[inline(always)]
    fn forall(variables: Vec<V>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }
}

impl Formula for SNF {
    type Term = Complex;

    fn signature(&self) -> Result<crate::syntax::Sig, crate::syntax::Error> {
        match self {
            SNF::QFF(this) => this.signature(),
            SNF::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            SNF::QFF(this) => this.free_vars(),
            SNF::Forall(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            SNF::QFF(this) => this.transform(f).into(),
            SNF::Forall(this) => Forall {
                variables: this.variables.clone(),
                formula: this.formula.transform(f),
            }
            .into(),
        }
    }
}

impl std::fmt::Display for SNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        FOF::from(self).fmt(f)
    }
}

impl From<SNF> for FOF {
    fn from(value: SNF) -> Self {
        match value {
            SNF::QFF(this) => this.into(),
            SNF::Forall(this) => FOF::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&SNF> for FOF {
    fn from(value: &SNF) -> Self {
        value.clone().into()
    }
}

impl PNF {
    /// Transforms the receiver PNF to a Skolem Normal Form (SNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let formula: FOF = "∃ y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let snf = pnf.snf();
    ///
    /// assert_eq!("P(x, f#0(x))", snf.to_string());
    /// ```
    pub fn snf(&self) -> SNF {
        let mut c_counter = 0;
        let mut f_counter = 0;
        let mut const_generator = || {
            let name = format!("c#{}", c_counter);
            c_counter += 1;
            name.into()
        };
        let mut fn_generator = || {
            let name = format!("f#{}", f_counter);
            f_counter += 1;
            name.into()
        };

        self.snf_with(&mut const_generator, &mut fn_generator)
    }

    /// Is similar to [`PNF::snf`] but uses an existing [`Generator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    ///
    /// [`PNF::snf`]: crate::transform::PNF::snf()
    /// [`Generator`]: crate::syntax::symbol::Generator
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let mut c_counter = 0;
    /// let mut f_counter = 0;
    /// let mut const_generator = || {
    ///     let c = c_counter;
    ///     c_counter += 1;
    ///     format!("skolem_const{}", c).into()
    /// };
    /// let mut fn_generator = || {
    ///     let c = f_counter;
    ///     f_counter += 1;
    ///     format!("skolem_fn{}", c).into()
    /// };    
    /// let formula: FOF = "∃ y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let snf = pnf.snf_with(&mut const_generator, &mut fn_generator);
    ///
    /// assert_eq!("P(x, skolem_fn0(x))", snf.to_string());
    /// ```
    pub fn snf_with<CG, FG>(&self, const_generator: &mut CG, fn_generator: &mut FG) -> SNF
    where
        CG: FnMut() -> C,
        FG: FnMut() -> F,
    {
        let free_vars = self.free_vars().into_iter().cloned().collect();
        SNF::new(self.clone(), free_vars, const_generator, fn_generator)
    }
}

impl FOF {
    /// Transforms the receiver FOF to a Skolem Normal Form (SNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    ///
    /// let fof: FOF = "∃ y. P(x, y)".parse().unwrap();
    ///
    /// assert_eq!("P(x, f#0(x))", fof.snf().to_string());
    /// ```
    pub fn snf(&self) -> SNF {
        self.pnf().snf()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, fof};

    fn snf(formula: &FOF) -> FOF {
        formula.pnf().snf().into()
    }
    fn snf_with<CG, FG>(formula: &FOF, const_generator: &mut CG, fn_generator: &mut FG) -> FOF
    where
        CG: FnMut() -> C,
        FG: FnMut() -> F,
    {
        formula.pnf().snf_with(const_generator, fn_generator).into()
    }

    #[test]
    fn test_snf() {
        assert_debug_string!("P('c#0)", snf(&fof!(? x. (P(x)))));

        assert_debug_string!("! x. P(x, f#0(x))", snf(&fof!(!x. (?y. (P(x, y))))));
        assert_debug_string!("P(x, f#0(x))", snf(&fof!(?y. (P(x, y)))));
        assert_debug_string!(
            "! x. P(x, f(g(f#0(x)), h(f#0(x))))",
            snf(&fof!(!x. (? y. (P(x, f(g(y), h(y))))))),
        );
        assert_debug_string!(
            "('c#0 = 'c#1) & ('c#1 = 'c#2)",
            snf(&fof!(? x, y, z. (((x) = (y)) & ((y) = (z))))),
        );
        assert_debug_string!(
            "! y. (Q('c#0, y) | P(f#0(y), y, f#1(y)))",
            snf(&fof!(? x. (! y. ((Q(x, y)) | (? x, z. (P(x, y, z))))))),
        );
        assert_debug_string!(
            "! x. (! z. P(x, f#0(x), z))",
            snf(&fof!(! x. (? y.( ! z. (P(x, y, z)))))),
        );
        assert_debug_string!(
            "! x. (R(g(x)) | R(x, f#0(x)))",
            snf(&fof!(! x. ((R(g(x))) | (? y. (R(x, y)))))),
        );
        assert_debug_string!(
            "! y. (! z. (! v. P('c#0, y, z, f#0(y, z), v, f#1(y, z, v))))",
            snf(&fof!(? x. (! y. (! z. (? u. (! v. (? w. (P(x, y, z, u, v, w))))))))),
        );
        {
            let mut c_counter = 0;
            let mut f_counter = 0;

            let mut const_generator = || {
                let c_name = format!("c#{}", c_counter);
                c_counter += 1;
                c_name.into()
            };
            let mut fn_generator = || {
                let f_name = format!("f#{}", f_counter);
                f_counter += 1;
                f_name.into()
            };

            assert_debug_string!(
                "P('c#0)",
                snf_with(&fof!(? x. (P(x))), &mut const_generator, &mut fn_generator)
            );
            assert_debug_string!(
                "Q('c#1)",
                snf_with(&fof!(? x. (Q(x))), &mut const_generator, &mut fn_generator)
            );
        }
    }
}
