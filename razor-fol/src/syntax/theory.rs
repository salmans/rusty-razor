/*! Defines first-order theories. */

use std::{convert::TryFrom, fmt};

use super::{Error, Formula, Sig};

/// is a first-order theory, containing a set of first-order formulae.
pub struct Theory {
    /// is the signature of the theory, containing constants, function symbols, and predicates.
    pub signature: Sig,

    /// is the list of first-order formulae in this theory.
    pub formulae: Vec<Formula>,
}

impl TryFrom<Vec<Formula>> for Theory {
    type Error = Error;

    fn try_from(formulae: Vec<Formula>) -> Result<Self, Error> {
        let signature = Sig::try_from(&formulae)?;

        Ok(Theory {
            signature,
            formulae,
        })
    }
}

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let fs: Vec<String> = self.formulae.iter().map(|t| t.to_string()).collect();
        write!(f, "{}", fs.join("\n"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula;

    #[test]
    fn test_formula_to_string() {
        let formulae = vec![
            formula!(!x. ((x) = (x))),
            formula!(!x, y. (((x) = (y)) -> ((y) = (x)))),
            formula!(!x, y, z. ((((x) = (y)) & ((y) = (z))) -> ((x) = (z)))),
        ];

        let expected_sig = Sig::try_from(&formulae).unwrap();
        let expected = "∀ x. (x = x)\n\
            ∀ x, y. ((x = y) → (y = x))\n\
            ∀ x, y, z. (((x = y) ∧ (y = z)) → (x = z))";

        let theory = Theory::try_from(formulae).unwrap();
        assert_eq!(expected, &theory.to_string());
        assert_eq!(&expected_sig, &theory.signature);
    }
}
