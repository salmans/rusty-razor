/*! Implements conversion to Skolem Normal Form (SNF) for formulae.*/
use super::{TermBased, PNF};
use crate::syntax::{symbol::Generator, FOF::*, *};
use std::collections::HashMap;

/// Is a wrapper around [`FOF`] that represents a formula in Skolem Normal Form (SNF).
///
/// **Hint**: An SNF is a [PNF] with only universal quantifiers
/// (see: <https://en.wikipedia.org/wiki/Skolem_normal_form>).
///
/// [PNF]: crate::transform::PNF
/// [`FOF`]: crate::syntax::FOF
#[derive(Clone, Debug)]
pub struct SNF(FOF);

impl SNF {
    /// Returns a reference to the first-order formula wrapped in the receiver SNF.
    #[inline(always)]
    pub fn formula(&self) -> &FOF {
        &self.0
    }
}

impl From<SNF> for FOF {
    fn from(snf: SNF) -> Self {
        snf.0
    }
}

fn helper(formula: FOF, mut skolem_vars: Vec<V>, generator: &mut Generator) -> FOF {
    match formula {
        Forall { variables, formula } => {
            skolem_vars.append(&mut variables.clone());
            forall(variables, helper(*formula, skolem_vars, generator))
        }
        Exists { variables, formula } => {
            let mut map: HashMap<&V, Term> = HashMap::new();

            variables.iter().for_each(|v| {
                if skolem_vars.is_empty() {
                    map.insert(&v, C::from(&generator.generate_next()).into());
                } else {
                    let vars: Vec<Term> = skolem_vars.iter().map(|v| v.clone().into()).collect();
                    map.insert(&v, F::from(&generator.generate_next()).app(vars));
                }
            });

            let substituted = formula.substitute(&map);
            helper(substituted, skolem_vars, generator)
        }
        _ => formula,
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
        let free_vars = self.formula().free_vars().into_iter().cloned().collect();
        SNF(helper(self.clone().into(), free_vars, generator))
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
