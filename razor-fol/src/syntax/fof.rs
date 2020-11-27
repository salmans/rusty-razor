/*! Defines the syntax of first-order formulae with equality.*/
use super::formula::*;
use super::V;
use itertools::Itertools;
use std::fmt;

/// Is an abstract syntax tree (AST) for first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FOF {
    /// Is logical top (⊤) or truth.
    Top,

    /// Is logical bottom (⟘) or falsehood.
    Bottom,

    /// Is an atomic first-order formula, wrapping an [`Atom`].
    Atom(Atom),

    /// Is a first-order equality, wrapping an [`Equals`].
    ///
    /// **Note**: Equality is a special type of atomic first-order formula.
    Equals(Equals),

    /// Is the negation of the first-order formula, wrapping a [`Not`].
    Not(Box<Not<FOF>>),

    /// Is a conjunction of two first-order formulae, wrapping an [`And`].
    And(Box<And<FOF>>),

    /// Is a disjunction of two first-order formulae, wrapping an [`Or`].
    Or(Box<Or<FOF>>),

    /// Is an implication between two first-order formulae, wrapping an [`Implies`].
    Implies(Box<Implies<FOF>>),

    /// Is an bi-implication between two first-order formulae, wrapping an [`Iff`].    
    Iff(Box<Iff<FOF>>),

    /// Is an existentially quantified formula, wrapping an [`Exists`].
    Exists(Box<Exists<FOF>>),

    /// Is a universally quantified formula, wrapping a [`Forall`].    
    Forall(Box<Forall<FOF>>),
}

impl From<Atom> for FOF {
    fn from(value: Atom) -> Self {
        Self::Atom(value)
    }
}

impl From<Equals> for FOF {
    fn from(value: Equals) -> Self {
        Self::Equals(value)
    }
}

impl From<Not<FOF>> for FOF {
    fn from(value: Not<FOF>) -> Self {
        Self::Not(Box::new(value))
    }
}

impl From<And<FOF>> for FOF {
    fn from(value: And<FOF>) -> Self {
        Self::And(Box::new(value))
    }
}

impl From<Or<FOF>> for FOF {
    fn from(value: Or<FOF>) -> Self {
        Self::Or(Box::new(value))
    }
}

impl From<Implies<FOF>> for FOF {
    fn from(value: Implies<FOF>) -> Self {
        Self::Implies(Box::new(value))
    }
}

impl From<Iff<FOF>> for FOF {
    fn from(value: Iff<FOF>) -> Self {
        Self::Iff(Box::new(value))
    }
}

impl From<Exists<FOF>> for FOF {
    fn from(value: Exists<FOF>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<FOF>> for FOF {
    fn from(value: Forall<FOF>) -> Self {
        Self::Forall(Box::new(value))
    }
}

/// Returns the negation of `formula`.
pub fn not(formula: FOF) -> FOF {
    Not::new(formula).into()
}

/// Returns an existentially quantified first-order formula with the given
/// `variables` and `formula`.
pub fn exists(variables: Vec<V>, formula: FOF) -> FOF {
    Exists::new(variables, formula).into()
}

/// Returns a universally quantified first-order formula with the given
/// `variables` and `formula`.
pub fn forall(variables: Vec<V>, formula: FOF) -> FOF {
    Forall::new(variables, formula).into()
}

impl FOF {
    /// Returns a conjunction of the receiver and `formula`.
    pub fn and(self, formula: Self) -> Self {
        And::new(self, formula).into()
    }

    /// Returns a disjunction of the receiver and `formula`.
    pub fn or(self, formula: Self) -> Self {
        Or::new(self, formula).into()
    }

    /// Returns an implication between the receiver and `formula`.
    pub fn implies(self, formula: Self) -> Self {
        Implies::new(self, formula).into()
    }

    /// Returns a bi-implication between the receiver and `formula`.
    pub fn iff(self, formula: Self) -> Self {
        Iff::new(self, formula).into()
    }
}

impl Formula for FOF {
    fn free_vars(&self) -> Vec<&V> {
        match self {
            Self::Top => Vec::new(),
            Self::Bottom => Vec::new(),
            Self::Atom(this) => this.free_vars(),
            Self::Equals(this) => this.free_vars(),
            Self::Not(this) => this.free_vars(),
            Self::And(this) => this.free_vars(),
            Self::Or(this) => this.free_vars(),
            Self::Implies(this) => this.free_vars(),
            Self::Iff(this) => this.free_vars(),
            Self::Exists(this) => this.free_vars(),
            Self::Forall(this) => this.free_vars(),
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
            Self::Atom(this) => {
                let ts = this.terms().iter().map(|t| t.to_string()).collect_vec();
                write!(f, "{}({})", this.predicate().to_string(), ts.join(", "))
            }
            Self::Equals(this) => write!(f, "{} = {}", this.left(), this.right()),
            Self::Not(this) => write!(f, "¬{}", parens(this.formula())),
            Self::And(this) => write!(f, "{} ∧ {}", parens(this.left()), parens(this.right())),
            Self::Or(this) => write!(f, "{} ∨ {}", parens(this.left()), parens(this.right())),
            Self::Implies(this) => {
                write!(
                    f,
                    "{} → {}",
                    parens(this.premise()),
                    parens(this.consequence())
                )
            }
            Self::Iff(this) => write!(f, "{} ⇔ {}", parens(this.left()), parens(this.right())),
            Self::Exists(this) => {
                let vs = this.variables().iter().map(|t| t.to_string()).collect_vec();
                write!(f, "∃ {}. {}", vs.join(", "), parens(this.formula()))
            }
            Self::Forall(this) => {
                let vs: Vec<_> = this.variables().iter().map(|t| t.to_string()).collect();
                write!(f, "∀ {}. {}", vs.join(", "), parens(this.formula()))
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
            Self::Atom(this) => {
                let ts = this.terms().iter().map(|t| t.to_string()).collect_vec();
                write!(f, "{}({})", this.predicate().to_string(), ts.join(", "))
            }
            Self::Equals(this) => write!(f, "{} = {}", this.left(), this.right()),
            Self::Not(this) => match this.formula() {
                Self::Top | Self::Bottom | Self::Atom { .. } => write!(f, "~{}", this.formula()),
                _ => write!(f, "~({:?})", this.formula()),
            },
            Self::And(this) => write_binary(this.left(), this.right(), "&", f),
            Self::Or(this) => write_binary(this.left(), this.right(), "|", f),
            Self::Implies(this) => write_binary(this.premise(), this.consequence(), "->", f),
            Self::Iff(this) => write_binary(this.left(), this.right(), "<=>", f),
            Self::Exists(this) => {
                let vs = this.variables().iter().map(|t| t.to_string()).collect_vec();
                match this.formula() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "? {}. {:?}", vs.join(", "), this.formula())
                    }
                    _ => write!(f, "? {}. ({:?})", vs.join(", "), this.formula()),
                }
            }
            Self::Forall(this) => {
                let vs = this.variables().iter().map(|t| t.to_string()).collect_vec();
                match this.formula() {
                    Self::Top | Self::Bottom | Self::Atom { .. } => {
                        write!(f, "! {}. {:?}", vs.join(", "), this.formula())
                    }
                    _ => write!(f, "! {}. ({:?})", vs.join(", "), this.formula()),
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