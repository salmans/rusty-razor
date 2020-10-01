/*! Implements conversion to Skolem Normal Form (SNF) for formulae.*/
use super::{TermBased, PNF};
use crate::syntax::{symbol::Generator, Formula::*, *};
use std::collections::HashMap;

/// Is a wrapper around [`Formula`] that represents a formula in Skolem Normal Form (SNF).
///
/// **Hint**: An SNF is a [PNF] with only universal quantifiers
/// (see: <https://en.wikipedia.org/wiki/Skolem_normal_form>).
///
/// [PNF]: ./enum.Formula.html#method.pnf
///
/// [`Formula`]: ../syntax/enum.Formula.html
#[derive(Clone, Debug)]
pub struct SNF(Formula);

impl SNF {
    /// Returns a reference to the formula wrapped in the receiver SNF.
    pub fn formula(&self) -> &Formula {
        &self.0
    }
}

impl From<SNF> for Formula {
    fn from(snf: SNF) -> Self {
        snf.0
    }
}

fn helper(formula: Formula, mut skolem_vars: Vec<V>, generator: &mut Generator) -> Formula {
    match formula {
        Forall { variables, formula } => {
            skolem_vars.append(&mut variables.clone());
            forall(variables, helper(*formula, skolem_vars, generator))
        }
        Exists { variables, formula } => {
            let mut map: HashMap<&V, Term> = HashMap::new();

            variables.iter().for_each(|v| {
                if skolem_vars.is_empty() {
                    map.insert(&v, C::from(&generator.next()).into());
                } else {
                    let vars: Vec<Term> = skolem_vars.iter().map(|v| v.clone().into()).collect();
                    map.insert(&v, F::from(&generator.next()).app(vars));
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
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "∃ y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let snf = pnf.snf();
    ///
    /// assert_eq!("P(x, sk#0(x))", Formula::from(snf).to_string());
    /// ```
    pub fn snf(&self) -> Formula {
        self.snf_with(&mut Generator::new().set_prefix("sk#"))
    }

    /// Is similar to [`Formula::snf`] but uses an existing [`Generator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    ///
    /// [`Formula::snf`]: ./enum.Formula.html#method.snf
    /// [`Generator`]: ../syntax/symbol/struct.Generator.html
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{Formula, symbol::Generator};
    ///
    /// let mut generator = Generator::new().set_prefix("skolem");
    /// let formula: Formula = "∃ y. P(x, y)".parse().unwrap();
    /// let pnf = formula.pnf();
    /// let snf = pnf.snf_with(&mut generator);
    ///
    /// assert_eq!("P(x, skolem0(x))", Formula::from(snf).to_string());
    /// ```
    pub fn snf_with(&self, generator: &mut Generator) -> SNF {
        let free_vars = self.formula().free_vars().into_iter().cloned().collect();
        SNF(helper(self.clone().into(), free_vars, generator))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, formula};

    #[test]
    fn snf(formula: &Formula) -> Formula {
        formula.pnf().snf().into()
    }
    fn snf_with(formula: &Formula, generator: &mut SkolemGenerator) -> Formula {
        formula.pnf().snf_with(generator).into()
    }

    #[test]
    fn test_snf() {
        assert_debug_string!("P('sk#0)", snf(&formula!(? x. (P(x)))));

        assert_debug_string!("! x. P(x, sk#0(x))", snf(&formula!(!x. (?y. (P(x, y))))));
        assert_debug_string!("P(x, sk#0(x))", snf(&formula!(?y. (P(x, y)))));
        assert_debug_string!(
            "! x. P(x, f(g(sk#0(x)), h(sk#0(x))))",
            snf(&formula!(!x. (? y. (P(x, f(g(y), h(y))))))),
        );
        assert_debug_string!(
            "('sk#0 = 'sk#1) & ('sk#1 = 'sk#2)",
            snf(&formula!(? x, y, z. (((x) = (y)) & ((y) = (z))))),
        );
        assert_debug_string!(
            "! y. (Q('sk#0, y) | P(sk#1(y), y, sk#2(y)))",
            snf(&formula!(? x. (! y. ((Q(x, y)) | (? x, z. (P(x, y, z))))))),
        );
        assert_debug_string!(
            "! x. (! z. P(x, sk#0(x), z))",
            snf(&formula!(! x. (? y.( ! z. (P(x, y, z)))))),
        );
        assert_debug_string!(
            "! x. (R(g(x)) | R(x, sk#0(x)))",
            snf(&formula!(! x. ((R(g(x))) | (? y. (R(x, y)))))),
        );
        assert_debug_string!(
            "! y. (! z. (! v. P('sk#0, y, z, sk#1(y, z), v, sk#2(y, z, v))))",
            snf(&formula!(? x. (! y. (! z. (? u. (! v. (? w. (P(x, y, z, u, v, w))))))))),
        );
        {
            let mut generator = Generator::new().set_prefix("sk#");
            assert_debug_string!("P('sk#0)", snf_with(&formula!(? x. (P(x))), &mut generator));
            assert_debug_string!("Q('sk#1)", snf_with(&formula!(? x. (Q(x))), &mut generator));
        }
    }
}
