/*! Defines formulae in Skolem Normal Form (PNF) and implements an algorithm for converting
[`PNF`] to [`SNF`].

[`PNF`]: crate::transform::PNF
*/
use super::{TermBased, PNF};
use crate::syntax::{formula::*, symbol::Generator, Term, C, F, FOF, V};
use std::collections::HashMap;

/// Represents a formula in Skolem Normal Form (SNF).
///
/// **Hint**: An SNF is a [PNF] with only universal quantifiers
/// (see: <https://en.wikipedia.org/wiki/Skolem_normal_form>).
///
/// [PNF]: crate::transform::PNF
#[derive(Clone, Debug)]
pub enum SNF {
    /// Is the quantifier-free portion of an [`SNF`].
    QuantifierFree(QFF),

    /// Is a universally quantified formula, wrapping a [`Forall`].
    Forall(Box<Forall<SNF>>),
}

impl From<Atom> for SNF {
    fn from(value: Atom) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Equals> for SNF {
    fn from(value: Equals) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Not<QFF>> for SNF {
    fn from(value: Not<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<And<QFF>> for SNF {
    fn from(value: And<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Or<QFF>> for SNF {
    fn from(value: Or<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Implies<QFF>> for SNF {
    fn from(value: Implies<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Iff<QFF>> for SNF {
    fn from(value: Iff<QFF>) -> Self {
        Self::QuantifierFree(value.into())
    }
}

impl From<Forall<SNF>> for SNF {
    fn from(value: Forall<SNF>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<QFF> for SNF {
    fn from(value: QFF) -> Self {
        Self::QuantifierFree(value)
    }
}

impl From<&PNF> for SNF {
    fn from(value: &PNF) -> Self {
        value.snf()
    }
}

impl SNF {
    /// Creates a new formula in SNF from a [`PNF`], a list of skolem variables and
    /// [`Generator`] for creating fresh skolem function names.
    fn new(pnf: PNF, mut skolem_vars: Vec<V>, generator: &mut Generator) -> Self {
        match pnf {
            PNF::Forall(this) => {
                let variables = this.variables;
                skolem_vars.append(&mut variables.to_vec());
                SNF::forall(
                    variables.to_vec(),
                    Self::new(this.formula, skolem_vars, generator),
                )
            }
            PNF::Exists(this) => {
                let variables = this.variables;
                let mut map: HashMap<&V, Term> = HashMap::new();

                variables.iter().for_each(|v| {
                    if skolem_vars.is_empty() {
                        map.insert(&v, C::from(&generator.generate_next()).into());
                    } else {
                        let vars: Vec<Term> =
                            skolem_vars.iter().map(|v| v.clone().into()).collect();
                        map.insert(&v, F::from(&generator.generate_next()).app(vars));
                    }
                });

                let substituted = this.formula.substitute(&map);
                Self::new(substituted, skolem_vars, generator)
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

impl TermBased for SNF {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            SNF::QuantifierFree(this) => this.free_vars(),
            SNF::Forall(this) => this.free_vars(),
        }
    }

    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        match self {
            SNF::QuantifierFree(this) => this.transform(f).into(),
            SNF::Forall(this) => Forall {
                variables: this.variables.clone(),
                formula: this.formula.transform(f),
            }
            .into(),
        }
    }
}

impl Formula for SNF {
    fn signature(&self) -> Result<crate::syntax::Sig, crate::syntax::Error> {
        match self {
            SNF::QuantifierFree(this) => this.signature(),
            SNF::Forall(this) => this.signature(),
        }
    }
}

impl From<SNF> for FOF {
    fn from(value: SNF) -> Self {
        match value {
            SNF::QuantifierFree(this) => this.into(),
            SNF::Forall(this) => FOF::forall(this.variables, this.formula.into()),
        }
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
    /// assert_eq!("P(x, sk#0(x))", FOF::from(snf).to_string());
    /// ```
    pub fn snf(&self) -> SNF {
        self.snf_with(&mut Generator::new().set_prefix("sk#"))
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
    /// # use razor_fol::syntax::{FOF, symbol::Generator};
    ///
    /// let mut generator = Generator::new().set_prefix("skolem");
    /// let formula: FOF = "∃ y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let snf = pnf.snf_with(&mut generator);
    ///
    /// assert_eq!("P(x, skolem0(x))", FOF::from(snf).to_string());
    /// ```
    pub fn snf_with(&self, generator: &mut Generator) -> SNF {
        let free_vars = self.free_vars().into_iter().cloned().collect();
        SNF::new(self.clone(), free_vars, generator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, fof};

    fn snf(formula: &FOF) -> FOF {
        formula.pnf().snf().into()
    }
    fn snf_with(formula: &FOF, generator: &mut Generator) -> FOF {
        formula.pnf().snf_with(generator).into()
    }

    #[test]
    fn test_snf() {
        assert_debug_string!("P('sk#0)", snf(&fof!(? x. (P(x)))));

        assert_debug_string!("! x. P(x, sk#0(x))", snf(&fof!(!x. (?y. (P(x, y))))));
        assert_debug_string!("P(x, sk#0(x))", snf(&fof!(?y. (P(x, y)))));
        assert_debug_string!(
            "! x. P(x, f(g(sk#0(x)), h(sk#0(x))))",
            snf(&fof!(!x. (? y. (P(x, f(g(y), h(y))))))),
        );
        assert_debug_string!(
            "('sk#0 = 'sk#1) & ('sk#1 = 'sk#2)",
            snf(&fof!(? x, y, z. (((x) = (y)) & ((y) = (z))))),
        );
        assert_debug_string!(
            "! y. (Q('sk#0, y) | P(sk#1(y), y, sk#2(y)))",
            snf(&fof!(? x. (! y. ((Q(x, y)) | (? x, z. (P(x, y, z))))))),
        );
        assert_debug_string!(
            "! x. (! z. P(x, sk#0(x), z))",
            snf(&fof!(! x. (? y.( ! z. (P(x, y, z)))))),
        );
        assert_debug_string!(
            "! x. (R(g(x)) | R(x, sk#0(x)))",
            snf(&fof!(! x. ((R(g(x))) | (? y. (R(x, y)))))),
        );
        assert_debug_string!(
            "! y. (! z. (! v. P('sk#0, y, z, sk#1(y, z), v, sk#2(y, z, v))))",
            snf(&fof!(? x. (! y. (! z. (? u. (! v. (? w. (P(x, y, z, u, v, w))))))))),
        );
        {
            let mut generator = Generator::new().set_prefix("sk#");
            assert_debug_string!("P('sk#0)", snf_with(&fof!(? x. (P(x))), &mut generator));
            assert_debug_string!("Q('sk#1)", snf_with(&fof!(? x. (Q(x))), &mut generator));
        }
    }
}
