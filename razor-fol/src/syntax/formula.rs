/*! Defines the syntax for first-order formulae with equality.*/

use super::{Pred, Term, V};
use std::fmt;

/// Is an abstract syntax tree (AST) for first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    /// Is logical Top (⊤) or Truth
    Top,

    /// Is logical Bottom (⟘) or Falsehood
    Bottom,

    /// Is an atomic formula, made by applying `predicate` on a list of `terms`.
    Atom { predicate: Pred, terms: Vec<Term> },

    /// Represents an equality between two terms.
    ///
    /// **Note**: Equality is a special type of atomic formula.
    Equals { left: Term, right: Term },

    /// Makes the negation of the `formula` that it holds.
    Not { formula: Box<Formula> },

    /// Makes a conjunction of the `left` and `right` formulae that it holds.
    And {
        left: Box<Formula>,
        right: Box<Formula>,
    },

    /// Makes a disjunction of `left` and `right` formulae that it holds.
    Or {
        left: Box<Formula>,
        right: Box<Formula>,
    },

    /// Makes an implication between `left` and `right` formulae that it holds.
    Implies {
        left: Box<Formula>,
        right: Box<Formula>,
    },

    /// Makes a bi-implication between `left` and `right` formulae that it holds.
    Iff {
        left: Box<Formula>,
        right: Box<Formula>,
    },

    /// Makes an existentially quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Exists {
        variables: Vec<V>,
        formula: Box<Formula>,
    },

    /// Makes a universally quantified formula with the bound `variables` and the `formula` that
    /// it holds.
    Forall {
        variables: Vec<V>,
        formula: Box<Formula>,
    },
}

/// Returns the negation of `formula`.
pub fn not(formula: Formula) -> Formula {
    Formula::Not {
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula with the given `variables` and `formula`.
pub fn exists(variables: Vec<V>, formula: Formula) -> Formula {
    Formula::Exists {
        variables,
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula on one variable.
pub fn exists1(first: V, formula: Formula) -> Formula {
    Formula::Exists {
        variables: vec![first],
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula on two variables.
pub fn exists2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Exists {
        variables: vec![first, second],
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula on three variables.
pub fn exists3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Exists {
        variables: vec![first, second, third],
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula on four variables.
pub fn exists4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Exists {
        variables: vec![first, second, third, fourth],
        formula: Box::new(formula),
    }
}

/// Returns an existentially quantified formula on five variables.
pub fn exists5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Exists {
        variables: vec![first, second, third, fourth, fifth],
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula with the given `variables` and `formula`.
pub fn forall(variables: Vec<V>, formula: Formula) -> Formula {
    Formula::Forall {
        variables,
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula on one variable.
pub fn forall1(first: V, formula: Formula) -> Formula {
    Formula::Forall {
        variables: vec![first],
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula on two variables.
pub fn forall2(first: V, second: V, formula: Formula) -> Formula {
    Formula::Forall {
        variables: vec![first, second],
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula on three variables.
pub fn forall3(first: V, second: V, third: V, formula: Formula) -> Formula {
    Formula::Forall {
        variables: vec![first, second, third],
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula on four variables.
pub fn forall4(first: V, second: V, third: V, fourth: V, formula: Formula) -> Formula {
    Formula::Forall {
        variables: vec![first, second, third, fourth],
        formula: Box::new(formula),
    }
}

/// Returns a universally quantified formula on five variables.
pub fn forall5(first: V, second: V, third: V, fourth: V, fifth: V, formula: Formula) -> Formula {
    Formula::Forall {
        variables: vec![first, second, third, fourth, fifth],
        formula: Box::new(formula),
    }
}

impl Formula {
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

    /// Returns a list of free variable symbols in the receiver formula.
    ///
    /// **Note**: In the list of free variables, each variable symbol appears only once even if it
    /// is present at multiple positions of the receiver formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{V, Formula};
    /// # use itertools::Itertools;
    ///
    /// // `x`, `y` and `z` are variable symbols:
    /// let x = V::from("x");
    /// let y = V::from("y");
    /// let z = V::from("z");
    ///
    /// // (P(x) ∧ Q(x, f(g(x), y))) ∨ ('c = g(z))
    /// let formula: Formula = "(P(x) & Q(x, f(g(x), y))) |  'c = g(z)".parse().unwrap();
    /// assert_eq!(vec![&x, &y, &z].iter().sorted(), formula.free_vars().iter().sorted());
    ///
    /// // ∀ x. P(x, y)
    /// let formula: Formula = "forall x. P(x, y)".parse().unwrap();
    /// // notice that the bound variable `x` is not in the list of free variables of `formula`
    /// assert_eq!(vec![&y], formula.free_vars());
    ///
    /// // ∃ x. P(x, y)
    /// let formula: Formula = "exists x. P(x, y)".parse().unwrap();
    /// assert_eq!(vec![&y], formula.free_vars());
    /// ```
    pub fn free_vars(&self) -> Vec<&V> {
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
impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fn parens(formula: &Formula) -> String {
            match formula {
                Formula::Top => formula.to_string(),
                Formula::Bottom => formula.to_string(),
                Formula::Atom { .. } => formula.to_string(),
                _ => format!("({})", formula),
            }
        }
        match self {
            Self::Top => write!(f, "{}", "⊤"),
            Self::Bottom => write!(f, "{}", "⟘"),
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
impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // a helper for writing binary formulae:
        fn write_binary(
            left: &Formula,
            right: &Formula,
            symbol: &str,
            f: &mut fmt::Formatter,
        ) -> Result<(), fmt::Error> {
            match left {
                Formula::Top | Formula::Bottom | Formula::Atom { .. } => match right {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        write!(f, "{:?} {} {:?}", left, symbol, right)
                    }
                    _ => write!(f, "{:?} {} ({:?})", left, symbol, right),
                },
                _ => match right {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        write!(f, "({:?}) {} {:?}", left, symbol, right)
                    }
                    _ => write!(f, "({:?}) {} ({:?})", left, symbol, right),
                },
            }
        }

        match self {
            Self::Top => write!(f, "{}", "true"),
            Self::Bottom => write!(f, "{}", "false"),
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
    use super::{Formula::*, *};
    use crate::test_prelude::*;

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
        assert_eq_vectors(&expected, &Bottom.free_vars());
    }

    #[test]
    fn test_atom_to_string() {
        assert_eq!("R()", R().app0().to_string());
        assert_eq!("R(x, y)", R().app2(x(), y()).to_string());
        assert_eq!("R(g(x, y))", R().app1(g().app2(x(), y())).to_string());
        {
            assert_eq!(
                "R(f(f(f(f(f(f(x)))))))",
                R().app1(f().app1(f().app1(f().app1(f().app1(f().app1(f().app1(x())))))))
                    .to_string()
            );
        }
    }

    #[test]
    fn test_atom_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &R().app0().free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &R().app2(x(), y()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &R().app2(y(), g().app2(x(), z())).free_vars());
        }
        {
            let vars = vec![_x(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &R().app2(
                    z(),
                    f().app1(f().app1(f().app1(f().app1(f().app1(f().app1(x())))))),
                )
                .free_vars(),
            );
        }
    }

    #[test]
    fn test_equals_to_string() {
        assert_eq!("x = y", x().equals(y()).to_string());
    }

    #[test]
    fn test_equals_free_vars() {
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &x().equals(y()).free_vars());
        }
        {
            let vars = vec![_x()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &x().equals(g().app0()).free_vars());
        }
    }

    #[test]
    fn test_not_to_string() {
        assert_eq!("¬R()", not(R().app0()).to_string());
        assert_eq!("¬(¬R())", not(not(R().app0())).to_string());
        assert_eq!("¬(x = y)", not(x().equals(y())).to_string());
        assert_eq!("¬R(x, y)", not(R().app2(x(), y())).to_string());
        assert_eq!(
            "¬(R(x, y) ∧ Q(z))",
            not(R().app2(x(), y()).and(Q().app1(z()))).to_string()
        );
        assert_eq!(
            "¬(R(x, y) ∨ Q(z))",
            not(R().app2(x(), y()).or(Q().app1(z()))).to_string()
        );
        assert_eq!(
            "¬(R(x, y) ∧ (¬Q(z)))",
            not(R().app2(x(), y()).and(not(Q().app1(z())))).to_string()
        );
        assert_eq!(
            "¬(R(x, y) → Q(z))",
            not(R().app2(x(), y()).implies(Q().app1(z()))).to_string()
        );
        assert_eq!(
            "¬(R(x, y) ⇔ Q(z))",
            not(R().app2(x(), y()).iff(Q().app1(z()))).to_string()
        );
    }

    #[test]
    fn test_not_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &not(R().app0()).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &not(not(R().app0())).free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &not(x().equals(y())).free_vars());
        }
        {
            let vars = vec![_x(), _y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &not(R().app2(x(), y())).free_vars());
        }
    }

    #[test]
    fn test_and_to_string() {
        assert_eq!("P() ∧ Q()", P().app0().and(Q().app0()).to_string());
        assert_eq!("P() ∧ (x = y)", P().app0().and(x().equals(y())).to_string());
        assert_eq!("P() ∧ (¬Q())", P().app0().and(not(Q().app0())).to_string());
        assert_eq!(
            "P() ∧ (Q() ∧ R())",
            P().app0().and(Q().app0().and(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() ∨ R())",
            P().app0().and(Q().app0().or(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() → R())",
            P().app0().and(Q().app0().implies(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∧ (Q() ⇔ R())",
            P().app0().and(Q().app0().iff(R().app0())).to_string()
        );
    }

    #[test]
    fn test_and_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().and(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &P().app2(z(), y()).and(x().equals(y())).free_vars(),
            );
        }
    }

    #[test]
    fn test_or_to_string() {
        assert_eq!("P() ∨ Q()", P().app0().or(Q().app0()).to_string());
        assert_eq!("P() ∨ (x = y)", P().app0().or(x().equals(y())).to_string());
        assert_eq!("P() ∨ (¬Q())", P().app0().or(not(Q().app0())).to_string());
        assert_eq!(
            "P() ∨ (Q() ∧ R())",
            P().app0().or(Q().app0().and(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∨ (Q() ∨ R())",
            P().app0().or(Q().app0().or(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∨ (Q() → R())",
            P().app0().or(Q().app0().implies(R().app0())).to_string()
        );
        assert_eq!(
            "P() ∨ (Q() ⇔ R())",
            P().app0().or(Q().app0().iff(R().app0())).to_string()
        );
    }

    #[test]
    fn test_or_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().or(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &P().app2(z(), y()).or(x().equals(y())).free_vars(),
            );
        }
    }

    #[test]
    fn test_implies_to_string() {
        assert_eq!("P() → Q()", P().app0().implies(Q().app0()).to_string());
        assert_eq!(
            "P() → (x = y)",
            P().app0().implies(x().equals(y())).to_string()
        );
        assert_eq!(
            "P() → (¬Q())",
            P().app0().implies(not(Q().app0())).to_string()
        );
        assert_eq!(
            "P() → (Q() ∧ R())",
            P().app0().implies(Q().app0().and(R().app0())).to_string()
        );
        assert_eq!(
            "P() → (Q() ∨ R())",
            P().app0().implies(Q().app0().or(R().app0())).to_string()
        );
        assert_eq!(
            "P() → (Q() → R())",
            P().app0()
                .implies(Q().app0().implies(R().app0()))
                .to_string()
        );
        assert_eq!(
            "P() → (Q() ⇔ R())",
            P().app0().implies(Q().app0().iff(R().app0())).to_string()
        );
    }

    #[test]
    fn test_implies_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().implies(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &P().app2(z(), y()).implies(x().equals(y())).free_vars(),
            );
        }
    }

    #[test]
    fn test_iff_to_string() {
        assert_eq!("P() ⇔ Q()", P().app0().iff(Q().app0()).to_string());
        assert_eq!("P() ⇔ (x = y)", P().app0().iff(x().equals(y())).to_string());
        assert_eq!("P() ⇔ (¬Q())", P().app0().iff(not(Q().app0())).to_string());
        assert_eq!(
            "P() ⇔ (Q() ∧ R())",
            P().app0().iff(Q().app0().and(R().app0())).to_string()
        );
        assert_eq!(
            "P() ⇔ (Q() ∨ R())",
            P().app0().iff(Q().app0().or(R().app0())).to_string()
        );
        assert_eq!(
            "P() ⇔ (Q() → R())",
            P().app0().iff(Q().app0().implies(R().app0())).to_string()
        );
        assert_eq!(
            "P() ⇔ (Q() ⇔ R())",
            P().app0().iff(Q().app0().iff(R().app0())).to_string()
        );
    }

    #[test]
    fn test_iff_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &P().app0().iff(Q().app0()).free_vars());
        }
        {
            let vars = vec![_x(), _y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &P().app2(z(), y()).iff(x().equals(y())).free_vars(),
            );
        }
    }

    #[test]
    fn test_exists_to_string() {
        assert_eq!("∃ x. P(x)", exists1(_x(), P().app1(x())).to_string());
        assert_eq!(
            "∃ x, y. P(x, y)",
            exists2(_x(), _y(), P().app2(x(), y())).to_string()
        );
        assert_eq!(
            "∃ x, y. (x = y)",
            exists2(_x(), _y(), x().equals(y())).to_string()
        );
        assert_eq!(
            "∃ x. (¬Q(x))",
            exists1(_x(), not(Q().app1(x()))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) ∧ R(x))",
            exists1(_x(), Q().app1(x()).and(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) ∨ R(x))",
            exists1(_x(), Q().app1(x()).or(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) → R(x))",
            exists1(_x(), Q().app1(x()).implies(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∃ x. (Q(x) ⇔ R(x))",
            exists1(_x(), Q().app1(x()).iff(R().app1(x()))).to_string()
        );
    }

    #[test]
    fn test_exists_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &exists1(_x(), P().app1(x())).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(
                &expected,
                &exists2(_x(), _y(), P().app2(x(), y())).free_vars(),
            );
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &exists1(_x(), x().equals(y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &exists1(_x(), Q().app1(x()).and(R().app1(y()))).free_vars(),
            );
        }
        {
            let vars = vec![_y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &exists1(_x(), Q().app2(x(), z()).and(R().app2(x(), y()))).free_vars(),
            );
        }
    }

    #[test]
    fn test_forall_to_string() {
        assert_eq!("∀ x. P(x)", forall1(_x(), P().app1(x())).to_string());
        assert_eq!(
            "∀ x, y. P(x, y)",
            forall2(_x(), _y(), P().app2(x(), y())).to_string()
        );
        assert_eq!(
            "∀ x, y. (x = y)",
            forall2(_x(), _y(), x().equals(y())).to_string()
        );
        assert_eq!(
            "∀ x. (¬Q(x))",
            forall1(_x(), not(Q().app1(x()))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) ∧ R(x))",
            forall1(_x(), Q().app1(x()).and(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) ∨ R(x))",
            forall1(_x(), Q().app1(x()).or(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) → R(x))",
            forall1(_x(), Q().app1(x()).implies(R().app1(x()))).to_string()
        );
        assert_eq!(
            "∀ x. (Q(x) ⇔ R(x))",
            forall1(_x(), Q().app1(x()).iff(R().app1(x()))).to_string()
        );
    }

    #[test]
    fn test_forall_free_vars() {
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(&expected, &forall1(_x(), P().app1(x())).free_vars());
        }
        {
            let expected: Vec<&V> = vec![];
            assert_eq_vectors(
                &expected,
                &forall2(_x(), _y(), P().app2(x(), y())).free_vars(),
            );
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(&expected, &forall1(_x(), x().equals(y())).free_vars());
        }
        {
            let vars = vec![_y()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &forall1(_x(), Q().app1(x()).and(R().app1(y()))).free_vars(),
            );
        }
        {
            let vars = vec![_y(), _z()];
            let expected: Vec<&V> = vars.iter().map(|x| x).collect();
            assert_eq_vectors(
                &expected,
                &forall1(_x(), Q().app2(x(), z()).and(R().app2(x(), y()))).free_vars(),
            );
        }
    }
}
