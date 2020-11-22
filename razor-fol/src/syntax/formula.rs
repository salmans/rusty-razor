/*! Defines the syntax for first-order formulae with equality.*/
use super::{Pred, Term, V};
use std::fmt;

pub trait Formula {
    /// Returns a list of free variable symbols in the receiver formula.
    ///
    /// **Note**: In the list of free variables, each variable symbol appears only once
    /// even if it is present at multiple positions of the receiver formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{V, FOF};
    /// # use itertools::Itertools;
    /// use razor_fol::syntax::Formula;
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = V::from("x");
    /// let y = V::from("y");
    /// let z = V::from("z");
    ///
    /// // (P(x) ∧ Q(x, f(g(x), y))) ∨ ('c = g(z))
    /// let formula: FOF = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// // ∀ x. P(x, y)
    /// let formula: FOF = "forall x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars()); // FOF is a Formula
    ///
    /// // ∃ x. P(x, y)
    /// let formula: FOF = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```    
    fn free_vars(&self) -> Vec<&V>;
}

/// Is an abstract syntax tree (AST) for first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FOF {
    /// Is logical Top (⊤) or Truth
    Top,

    /// Is logical Bottom (⟘) or Falsehood
    Bottom,

    /// Is an atomic first-order formula, made by applying `predicate` on a list of `terms`.
    Atom { predicate: Pred, terms: Vec<Term> },

    /// Represents an equality between two terms.
    ///
    /// **Note**: Equality is a special type of atomic first-order formula.
    Equals { left: Term, right: Term },

    /// Makes the negation of the `formula` that it holds.
    Not { formula: Box<FOF> },

    /// Makes a conjunction of the `left` and `right` formulae that it holds.
    And { left: Box<FOF>, right: Box<FOF> },

    /// Makes a disjunction of `left` and `right` formulae that it holds.
    Or { left: Box<FOF>, right: Box<FOF> },

    /// Makes an implication between `left` and `right` formulae that it holds.
    Implies { left: Box<FOF>, right: Box<FOF> },

    /// Makes a bi-implication between `left` and `right` formulae that it holds.
    Iff { left: Box<FOF>, right: Box<FOF> },

    /// Makes an existentially quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Exists {
        variables: Vec<V>,
        formula: Box<FOF>,
    },

    /// Makes a universally quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Forall {
        variables: Vec<V>,
        formula: Box<FOF>,
    },
}

/// Returns the negation of `formula`.
pub fn not(formula: FOF) -> FOF {
    FOF::Not {
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified first-order formula with the given
/// `variables` and `formula`.
pub fn exists(variables: Vec<V>, formula: FOF) -> FOF {
    FOF::Exists {
        variables,
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified first-order formula with the given
/// `variables` and `formula`.
pub fn forall(variables: Vec<V>, formula: FOF) -> FOF {
    FOF::Forall {
        variables,
        formula: Box::new(formula),
    }
}

impl FOF {
    /// Returns a conjunction of the receiver and `formula`.
    pub fn and(self, formula: Self) -> Self {
        Self::And {
            left: Box::new(self),
            right: Box::new(formula),
        }
    }

    /// Returns a disjunction of the receiver and `formula`.
    pub fn or(self, formula: Self) -> Self {
        Self::Or {
            left: Box::new(self),
            right: Box::new(formula),
        }
    }

    /// Returns an implication between the receiver and `formula`.
    pub fn implies(self, formula: Self) -> Self {
        Self::Implies {
            left: Box::new(self),
            right: Box::new(formula),
        }
    }

    /// Returns a bi-implication between the receiver and `formula`.
    pub fn iff(self, formula: Self) -> Self {
        Self::Iff {
            left: Box::new(self),
            right: Box::new(formula),
        }
    }
}

impl Formula for FOF {
    fn free_vars(&self) -> Vec<&V> {
        use itertools::Itertools;
        match self {
            Self::Top => vec![],
            Self::Bottom => vec![],
            Self::Atom {
                predicate: _,
                terms,
            } => terms.iter().flat_map(|t| t.free_vars()).unique().collect(),
            Self::Equals { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Not { formula } => formula.free_vars(),
            Self::And { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Or { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Implies { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Iff { left, right } => {
                let mut vs = left.free_vars();
                vs.extend(right.free_vars());
                vs.into_iter().unique().collect()
            }
            Self::Exists { variables, formula } => formula
                .free_vars()
                .into_iter()
                .filter(|v| !variables.contains(v))
                .collect(),
            Self::Forall { variables, formula } => formula
                .free_vars()
                .into_iter()
                .filter(|v| !variables.contains(v))
                .collect(),
        }
    }
}

// used for pretty printing a formula
impl fmt::Display for FOF {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fn parens(formula: &FOF) -> String {
            match formula {
                FOF::Top => formula.to_string(),
                FOF::Bottom => formula.to_string(),
                FOF::Atom { .. } => formula.to_string(),
                _ => format!("({})", formula),
            }
        }
        match self {
            Self::Top => write!(f, "⊤"),
            Self::Bottom => write!(f, "⟘"),
            Self::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Self::Equals { left, right } => write!(f, "{} = {}", left, right),
            Self::Not { formula } => write!(f, "¬{}", parens(formula)),
            Self::And { left, right } => write!(f, "{} ∧ {}", parens(left), parens(right)),
            Self::Or { left, right } => write!(f, "{} ∨ {}", parens(left), parens(right)),
            Self::Implies { left, right } => write!(f, "{} → {}", parens(left), parens(right)),
            Self::Iff { left, right } => write!(f, "{} ⇔ {}", parens(left), parens(right)),
            Self::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∃ {}. {}", vs.join(", "), parens(formula))
            }
            Self::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                write!(f, "∀ {}. {}", vs.join(", "), parens(formula))
            }
        }
    }
}

// contains no non-ascii characters
impl fmt::Debug for FOF {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // a helper for writing binary formulae:
        fn write_binary(
            left: &FOF,
            right: &FOF,
            symbol: &str,
            f: &mut fmt::Formatter,
        ) -> Result<(), fmt::Error> {
            match left {
                FOF::Top | FOF::Bottom | FOF::Atom { .. } => match right {
                    FOF::Top | FOF::Bottom | FOF::Atom { .. } => {
                        write!(f, "{:?} {} {:?}", left, symbol, right)
                    }
                    _ => write!(f, "{:?} {} ({:?})", left, symbol, right),
                },
                _ => match right {
                    FOF::Top | FOF::Bottom | FOF::Atom { .. } => {
                        write!(f, "({:?}) {} {:?}", left, symbol, right)
                    }
                    _ => write!(f, "({:?}) {} ({:?})", left, symbol, right),
                },
            }
        }

        match self {
            Self::Top => write!(f, "true"),
            Self::Bottom => write!(f, "false"),
            Self::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Self::Equals { left, right } => write!(f, "{} = {}", left, right),
            Self::Not { formula } => match formula.as_ref() {
                Self::Top | Self::Bottom | Self::Atom { .. } => write!(f, "~{}", formula),
                _ => write!(f, "~({:?})", formula),
            },
            Self::And { left, right } => write_binary(left, right, "&", f),
            Self::Or { left, right } => write_binary(left, right, "|", f),
            Self::Implies { left, right } => write_binary(left, right, "->", f),
            Self::Iff { left, right } => write_binary(left, right, "<=>", f),
            Self::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match formula.as_ref() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "? {}. {:?}", vs.join(", "), formula)
                    }
                    _ => write!(f, "? {}. ({:?})", vs.join(", "), formula),
                }
            }
            Self::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match formula.as_ref() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "! {}. {:?}", vs.join(", "), formula)
                    }
                    _ => write!(f, "! {}. ({:?})", vs.join(", "), formula),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{FOF::*, *};
    use crate::{assert_eq_sorted_vecs, fof, v};

    #[test]
    fn print_top() {
        assert_eq!("⊤", Top.to_string());
    }

    #[test]
    fn free_vars_top() {
        let expected: Vec<&V> = vec![];
        assert_eq!(expected, Top.free_vars());
    }

    #[test]
    fn print_bottom() {
        assert_eq!("⟘", Bottom.to_string());
    }

    #[test]
    fn free_vars_bottom() {
        let expected: Vec<&V> = vec![];
        assert_eq_sorted_vecs!(&expected, &Bottom.free_vars());
    }

    #[test]
    fn test_atom_to_string() {
        assert_eq!("R()", fof!(R()).to_string());
        assert_eq!("R(x, y)", fof!(R(x, y)).to_string());
        assert_eq!("R(g(x, y))", fof!(R(g(x, y))).to_string());
        {
            assert_eq!(
                "R(f(f(f(f(f(f(x)))))))",
                fof!(R(f(f(f(f(f(f(x)))))))).to_string()
            );
        }
    }

    #[test]
    fn test_atom_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(R()).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(R(x, y)).free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(R(y, g(x, z))).free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(R(z, f(f(f(f(f(f(x)))))))).free_vars()
            );
        }
    }

    #[test]
    fn test_equals_to_string() {
        assert_eq!("x = y", fof!((x) = (y)).to_string());
    }

    #[test]
    fn test_equals_free_vars() {
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!((x) = (y)).free_vars()
            );
        }
        {
            let expected = vec![v!(x)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!((x) = (g())).free_vars()
            );
        }
    }

    #[test]
    fn test_not_to_string() {
        assert_eq!("¬R()", fof!(~(R())).to_string());
        assert_eq!("¬(¬R())", fof!(~(~(R()))).to_string());
        assert_eq!("¬(x = y)", fof!(~((x) = (y))).to_string());
        assert_eq!("¬R(x, y)", fof!(~(R(x, y))).to_string());
        assert_eq!("¬(R(x, y) ∧ Q(z))", fof!(~{(R(x, y)) & (Q(z))}).to_string());
        assert_eq!("¬(R(x, y) ∨ Q(z))", fof!(~{(R(x, y)) | (Q(z))}).to_string(),);
        assert_eq!(
            "¬(R(x, y) ∨ (¬Q(z)))",
            fof!(~{(R(x, y)) | (~(Q(z)))}).to_string(),
        );
        assert_eq!(
            "¬(R(x, y) → Q(z))",
            fof!(~{(R(x, y)) -> (Q(z))}).to_string(),
        );
        assert_eq!(
            "¬(R(x, y) ⇔ Q(z))",
            fof!(~{(R(x, y)) <=> (Q(z))}).to_string(),
        );
    }

    #[test]
    fn test_not_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(~(R())).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(~(~(R()))).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(~{(x) = (y)}).free_vars()
            );
        }
        {
            let expected = vec![v!(x), v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(~(R(x, y))).free_vars()
            );
        }
    }

    #[test]
    fn test_and_to_string() {
        assert_eq!("P() ∧ Q()", fof!((P()) & (Q())).to_string());
        assert_eq!("P() ∧ (x = y)", fof!({ P() } & { (x) = (y) }).to_string());
        assert_eq!("P() ∧ (¬Q())", fof!({P()} & {~(Q())}).to_string());
        assert_eq!(
            "P() ∧ (Q() ∧ R())",
            fof!({ P() } & { (Q()) & (R()) }).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() ∨ R())",
            fof!({ P() } & { (Q()) | (R()) }).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() → R())",
            fof!({ P() } & { (Q()) -> (R()) }).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() ⇔ R())",
            fof!({ P() } & { (Q()) <=> (R()) }).to_string()
        );
    }

    #[test]
    fn test_and_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!((P()) & (Q())).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!({ P(z, y) } & { (x) = (y) }).free_vars(),
            );
        }
    }

    #[test]
    fn test_or_to_string() {
        assert_eq!("P() ∨ Q()", fof!((P()) | (Q())).to_string());
        assert_eq!("P() ∨ (x = y)", fof!({ P() } | { (x) = (y) }).to_string());
        assert_eq!("P() ∨ (¬Q())", fof!({P()} | {~(Q())}).to_string());
        assert_eq!(
            "P() ∨ (Q() ∧ R())",
            fof!({ P() } | { (Q()) & (R()) }).to_string(),
        );
        assert_eq!(
            "P() ∨ (Q() ∨ R())",
            fof!({ P() } | { (Q()) | (R()) }).to_string(),
        );
        assert_eq!(
            "P() ∨ (Q() → R())",
            fof!({P()} | {(Q()) -> (R())}).to_string(),
        );
        assert_eq!(
            "P() ∨ (Q() ⇔ R())",
            fof!({P()} | {(Q()) <=> (R())}).to_string(),
        );
    }

    #[test]
    fn test_or_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!((P()) | (Q())).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!({ P(z, y) } | { (x) = (y) }).free_vars(),
            );
        }
    }

    #[test]
    fn test_implies_to_string() {
        assert_eq!("P() → Q()", fof!((P()) -> (Q())).to_string());
        assert_eq!("P() → (x = y)", fof!({P()} -> {(x) = (y)}).to_string());
        assert_eq!("P() → (¬Q())", fof!({P()} -> {~(Q())}).to_string());
        assert_eq!(
            "P() → (Q() ∧ R())",
            fof!({P()} -> {(Q()) & (R())}).to_string(),
        );
        assert_eq!(
            "P() → (Q() ∨ R())",
            fof!({P()} -> {(Q()) | (R())}).to_string(),
        );
        assert_eq!(
            "P() → (Q() → R())",
            fof!({P()} -> {(Q()) -> (R())}).to_string(),
        );
        assert_eq!(
            "P() → (Q() ⇔ R())",
            fof!({P()} -> {(Q()) <=> (R())}).to_string(),
        );
    }

    #[test]
    fn test_implies_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!((P()) -> (Q())).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!({P(z, y)} -> {(x) = (y)}).free_vars(),
            );
        }
    }

    #[test]
    fn test_iff_to_string() {
        assert_eq!("P() ⇔ Q()", fof!((P()) <=> (Q())).to_string());
        assert_eq!("P() ⇔ (x = y)", fof!({P()} <=> {(x) = (y)}).to_string());
        assert_eq!("P() ⇔ (¬Q())", fof!({P()} <=> {~(Q())}).to_string());
        assert_eq!(
            "P() ⇔ (Q() ∧ R())",
            fof!({P()} <=> {(Q()) & (R())}).to_string(),
        );
        assert_eq!(
            "P() ⇔ (Q() ∨ R())",
            fof!({P()} <=> {(Q()) | (R())}).to_string(),
        );
        assert_eq!(
            "P() ⇔ (Q() → R())",
            fof!({P()} <=> {(Q()) -> (R())}).to_string(),
        );
        assert_eq!(
            "P() ⇔ (Q() ⇔ R())",
            fof!({P()} <=> {(Q()) <=> (R())}).to_string(),
        );
    }

    #[test]
    fn test_iff_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!((P()) <=> (Q())).free_vars());
        }
        {
            let expected = vec![v!(x), v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!({P(z, y)} <=> {(x) = (y)}).free_vars(),
            );
        }
    }

    #[test]
    fn test_exists_to_string() {
        assert_eq!("∃ x. P(x)", fof!(? x. (P(x))).to_string());
        assert_eq!("∃ x, y. P(x, y)", fof!(? x, y. (P(x, y))).to_string());
        assert_eq!("∃ x, y. (x = y)", fof!(? x, y. ((x) = (y))).to_string());
        assert_eq!("∃ x. (¬Q(x))", fof!(? x. (~(Q(x)))).to_string());
        assert_eq!(
            "∃ x. (Q(x) ∧ R(x))",
            fof!(? x. ((Q(x)) & (R(x)))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) ∨ R(x))",
            fof!(? x. ((Q(x)) | (R(x)))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) → R(x))",
            fof!(? x. ((Q(x)) -> (R(x)))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) ⇔ R(x))",
            fof!(? x. ((Q(x)) <=> (R(x)))).to_string()
        );
    }

    #[test]
    fn test_exists_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(? x. (P(x))).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(? x, y. (P(x, y))).free_vars());
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(? x. ((x) = (y))).free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(? x. ((Q(x)) & (R(y)))).free_vars()
            );
        }
        {
            let expected = vec![v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(? x. ((Q(x, z)) & (R(x, y)))).free_vars(),
            );
        }
    }

    #[test]
    fn test_forall_to_string() {
        assert_eq!("∀ x. P(x)", fof!(! x. (P(x))).to_string());
        assert_eq!("∀ x, y. P(x, y)", fof!(! x, y. (P(x, y))).to_string());
        assert_eq!("∀ x, y. (x = y)", fof!(! x, y. ((x) = (y))).to_string());
        assert_eq!("∀ x. (¬Q(x))", fof!(! x. (~(Q(x)))).to_string());
        assert_eq!(
            "∀ x. (Q(x) ∧ R(x))",
            fof!(! x. ((Q(x)) & (R(x)))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) ∨ R(x))",
            fof!(! x. ((Q(x)) | (R(x)))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) → R(x))",
            fof!(! x. ((Q(x)) -> (R(x)))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) ⇔ R(x))",
            fof!(! x. ((Q(x)) <=> (R(x)))).to_string()
        );
    }

    #[test]
    fn test_forall_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(! x. (P(x))).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(! x, y. (P(x, y))).free_vars());
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(! x. ((x) = (y))).free_vars()
            );
        }
        {
            let expected = vec![v!(y)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(! x. ((Q(x)) & (R(y)))).free_vars()
            );
        }
        {
            let expected = vec![v!(y), v!(z)];
            assert_eq_sorted_vecs!(
                expected.iter().collect::<Vec<_>>(),
                fof!(! x. ((Q(x, z)) & (R(x, y)))).free_vars()
            );
        }
    }
}
