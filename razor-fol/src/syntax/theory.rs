/*! Defines theories of formulae. */

use super::{Error, Formula, Sig};
use std::{convert::TryFrom, fmt};

/// is a first-order theory, containing a set of first-order formulae.
#[derive(Clone)]
pub struct Theory<T: Formula> {
    /// is the signature of the theory, containing constants, function symbols, and predicates.
    signature: Sig,

    /// is the list of first-order formulae in this theory.
    formulae: Vec<T>,
}

impl<T: Formula> Theory<T> {
    /// Returns a reference to the signature of this theory.
    pub fn signature(&self) -> &Sig {
        &self.signature
    }

    /// Returns the formulae of this theory.
    pub fn formulae(&self) -> &[T] {
        &self.formulae
    }

    /// Extends this theory with additional formulae. It fails if the signature of the
    /// new formulae is inconsistent with the signature of this theory.
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) -> Result<(), Error> {
        self.formulae.extend(iter);

        // recalculating the signature:
        self.signature = Sig::new_from_signatures(
            self.formulae()
                .iter()
                .map(|f| f.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        Ok(())
    }
}

impl<T: Formula> TryFrom<Vec<T>> for Theory<T> {
    type Error = Error;

    fn try_from(formulae: Vec<T>) -> Result<Self, Error> {
        let signature = Sig::new_from_signatures(
            formulae
                .iter()
                .map(|f| f.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )?;

        Ok(Theory {
            signature,
            formulae,
        })
    }
}

impl<T: Formula + fmt::Display> fmt::Display for Theory<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let fs: Vec<String> = self.formulae.iter().map(|t| t.to_string()).collect();
        write!(f, "{}", fs.join("\n"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fof;

    #[test]
    fn theory_to_string() {
        let formulae = vec![
            fof!(!x. ((x) = (x))),
            fof!(!x, y. (((x) = (y)) -> ((y) = (x)))),
            fof!(!x, y, z. ((((x) = (y)) & ((y) = (z))) -> ((x) = (z)))),
        ];

        let expected_sig = Sig::new_from_signatures(
            formulae
                .iter()
                .map(|f| f.signature())
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        )
        .unwrap();
        let expected = "∀ x. (x = x)\n\
            ∀ x, y. ((x = y) → (y = x))\n\
            ∀ x, y, z. (((x = y) ∧ (y = z)) → (x = z))";

        let theory = Theory::try_from(formulae).unwrap();
        assert_eq!(expected, &theory.to_string());
        assert_eq!(&expected_sig, &theory.signature);
    }

    #[test]
    fn theory_extend() {
        {
            let mut theory = Theory::try_from(vec![fof!(P(f(@c)))]).unwrap();
            let formulae = vec![fof!(Q(x))];

            assert!(theory.extend(formulae).is_ok());

            assert_eq!(
                "P(f(\'c))\n\
                 Q(x)",
                &theory.to_string()
            );
            assert_eq!(1, theory.signature().constants().len());
            assert_eq!(1, theory.signature().functions().len());
            assert_eq!(2, theory.signature().predicates().len());
        }
        {
            let mut theory = Theory::try_from(vec![fof!(P(f(@c)))]).unwrap();
            let formulae = vec![fof!(P(x))];

            assert!(theory.extend(formulae).is_ok());

            assert_eq!(
                "P(f(\'c))\n\
                 P(x)",
                &theory.to_string()
            );
            assert_eq!(1, theory.signature().constants().len());
            assert_eq!(1, theory.signature().functions().len());
            assert_eq!(1, theory.signature().predicates().len());
        }
        {
            let mut theory = Theory::try_from(vec![fof!(P(f(@c)))]).unwrap();
            let formulae = vec![fof!(P(x, y))];

            assert!(theory.extend(formulae).is_err());
        }
    }
}
