/*! Defines theories of formulae. */

use super::{Error, Formula, Sig};
use std::{fmt, iter::FromIterator, ops::Deref};

/// is a first-order theory, containing a set of first-order formulae.
#[derive(Clone)]
pub struct Theory<T: Formula>(Vec<T>);

impl<T: Formula> Theory<T> {
    /// Returns the formulae of this theory.
    pub fn formulae(&self) -> &[T] {
        &self.0
    }

    /// Extends this theory with additional formulae. It fails if the signature of the
    /// new formulae is inconsistent with the signature of this theory.
    pub fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter);
    }
}

impl<T: Formula> FromIterator<T> for Theory<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<T: Formula> Deref for Theory<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Formula> IntoIterator for Theory<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: Formula> Formula for Theory<T> {
    type Term = T::Term;

    fn signature(&self) -> Result<Sig, Error> {
        Sig::from_signatures(
            self.iter()
                .map(|c| c.signature())
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn free_vars(&self) -> Vec<&super::Var> {
        use itertools::Itertools;

        self.iter()
            .flat_map(|lit| lit.free_vars())
            .unique()
            .collect()
    }

    fn transform_term(&self, f: &impl Fn(&Self::Term) -> Self::Term) -> Self {
        Self(self.iter().map(|lit| lit.transform_term(f)).collect())
    }
}

impl<T: Formula + fmt::Display> fmt::Display for Theory<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let fs: Vec<String> = self.iter().map(|t| t.to_string()).collect();
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

        let expected_sig = Sig::from_signatures(
            formulae
                .iter()
                .map(|f| f.signature())
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        )
        .unwrap();
        let expected = "∀ x. x = x\n\
            ∀ x, y. (x = y → y = x)\n\
            ∀ x, y, z. ((x = y ∧ y = z) → x = z)";

        let theory: Theory<_> = formulae.into_iter().collect();
        assert_eq!(expected, &theory.to_string());
        assert_eq!(expected_sig, theory.signature().unwrap());
    }

    #[test]
    fn theory_extend() {
        {
            let mut theory: Theory<_> = vec![fof!(P(f(@c)))].into_iter().collect();
            let formulae = vec![fof!(Q(x))];
            theory.extend(formulae);

            assert_eq!(
                "P(f(\'c))\n\
                 Q(x)",
                &theory.to_string()
            );
            let signature = theory.signature().unwrap();
            assert_eq!(1, signature.constants().len());
            assert_eq!(1, signature.functions().len());
            assert_eq!(2, signature.predicates().len());
        }
        {
            let mut theory: Theory<_> = vec![fof!(P(f(@c)))].into_iter().collect();
            let formulae = vec![fof!(P(x))];
            theory.extend(formulae);

            assert_eq!(
                "P(f(\'c))\n\
                 P(x)",
                &theory.to_string()
            );
            let signature = theory.signature().unwrap();
            assert_eq!(1, signature.constants().len());
            assert_eq!(1, signature.functions().len());
            assert_eq!(1, signature.predicates().len());
        }
        {
            let mut theory: Theory<_> = vec![fof!(P(f(@c)))].into_iter().collect();
            let formulae = vec![fof!(P(x, y))];
            theory.extend(formulae);

            assert!(theory.signature().is_err());
        }
    }
}
