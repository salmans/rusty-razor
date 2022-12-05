/*! Defines the syntax of first-order formulae with equality.*/
use super::{qff::Qff, Sig, Var, *};
use crate::syntax::term::Complex;
use std::fmt;

/// Is an abstract syntax tree (AST) for first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fof {
    /// Is logical top (⊤) or truth.
    Top,

    /// Is logical bottom (⟘) or falsehood.
    Bottom,

    /// Is an atomic first-order formula, wrapping an [`Atom`].
    Atom(Atom<Complex>),

    /// Is a first-order equality, wrapping an [`Equals`].
    ///
    /// **Note**: Equality is a special type of atomic first-order formula.
    Equals(Equals<Complex>),

    /// Is the negation of a first-order formula, wrapping a [`Not`].
    Not(Box<Not<Fof>>),

    /// Is a conjunction of two first-order formulae, wrapping an [`And`].
    And(Box<And<Fof>>),

    /// Is a disjunction of two first-order formulae, wrapping an [`Or`].
    Or(Box<Or<Fof>>),

    /// Is an implication between two first-order formulae, wrapping an [`Implies`].
    Implies(Box<Implies<Fof>>),

    /// Is an bi-implication between two first-order formulae, wrapping an [`Iff`].    
    Iff(Box<Iff<Fof>>),

    /// Is an existentially quantified first-order formula, wrapping an [`Exists`].
    Exists(Box<Exists<Fof>>),

    /// Is a universally quantified first-order formula, wrapping a [`Forall`].
    Forall(Box<Forall<Fof>>),
}

impl From<Atom<Complex>> for Fof {
    fn from(value: Atom<Complex>) -> Self {
        Self::Atom(value)
    }
}

impl From<Equals<Complex>> for Fof {
    fn from(value: Equals<Complex>) -> Self {
        Self::Equals(value)
    }
}

impl From<Not<Fof>> for Fof {
    fn from(value: Not<Fof>) -> Self {
        Self::Not(Box::new(value))
    }
}

impl From<And<Fof>> for Fof {
    fn from(value: And<Fof>) -> Self {
        Self::And(Box::new(value))
    }
}

impl From<Or<Fof>> for Fof {
    fn from(value: Or<Fof>) -> Self {
        Self::Or(Box::new(value))
    }
}

impl From<Implies<Fof>> for Fof {
    fn from(value: Implies<Fof>) -> Self {
        Self::Implies(Box::new(value))
    }
}

impl From<Iff<Fof>> for Fof {
    fn from(value: Iff<Fof>) -> Self {
        Self::Iff(Box::new(value))
    }
}

impl From<Exists<Fof>> for Fof {
    fn from(value: Exists<Fof>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<Fof>> for Fof {
    fn from(value: Forall<Fof>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<Qff> for Fof {
    fn from(value: Qff) -> Self {
        match value {
            Qff::Top => Self::Top,
            Qff::Bottom => Self::Bottom,
            Qff::Atom(this) => Self::Atom(this),
            Qff::Equals(this) => Self::Equals(this),
            Qff::Not(this) => Fof::not(this.formula.into()),
            Qff::And(this) => {
                let left: Fof = this.left.into();
                let right: Fof = this.right.into();
                left.and(right)
            }
            Qff::Or(this) => {
                let left: Fof = this.left.into();
                let right: Fof = this.right.into();
                left.or(right)
            }
            Qff::Implies(this) => {
                let pre: Fof = this.premise.into();
                let cons: Fof = this.consequence.into();
                pre.implies(cons)
            }
            Qff::Iff(this) => {
                let left: Fof = this.left.into();
                let right: Fof = this.right.into();
                left.iff(right)
            }
        }
    }
}

impl Fof {
    /// Returns the negation of `formula`.
    #[allow(clippy::should_implement_trait)]
    // Disallow `formula.not()` intentionally:
    #[inline(always)]
    pub fn not(formula: Self) -> Self {
        Not { formula }.into()
    }

    /// Returns an existentially quantified first-order formula with the given
    /// `variables` and `formula`.
    #[inline(always)]
    pub fn exists(variables: Vec<Var>, formula: Self) -> Self {
        Exists { variables, formula }.into()
    }

    /// Returns a universally quantified first-order formula with the given
    /// `variables` and `formula`.
    #[inline(always)]
    pub fn forall(variables: Vec<Var>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }

    /// Returns a conjunction of `self` and `other`.
    #[inline(always)]
    pub fn and(self, other: Self) -> Self {
        And {
            left: self,
            right: other,
        }
        .into()
    }

    /// Returns a disjunction of `self` and `other`.
    #[inline(always)]
    pub fn or(self, other: Self) -> Self {
        Or {
            left: self,
            right: other,
        }
        .into()
    }

    /// Returns an implication between `self` and `other`.
    #[inline(always)]
    pub fn implies(self, other: Self) -> Self {
        Implies {
            premise: self,
            consequence: other,
        }
        .into()
    }

    /// Returns a bi-implication between `self` and `other`.
    #[inline(always)]
    pub fn iff(self, other: Self) -> Self {
        Iff {
            left: self,
            right: other,
        }
        .into()
    }
}

impl Formula for Fof {
    type Term = Complex;

    fn signature(&self) -> Result<super::Sig, super::Error> {
        match self {
            Fof::Top => Ok(Sig::new()),
            Fof::Bottom => Ok(Sig::new()),
            Fof::Atom(this) => this.signature(),
            Fof::Equals(this) => this.signature(),
            Fof::Not(this) => this.signature(),
            Fof::And(this) => this.signature(),
            Fof::Or(this) => this.signature(),
            Fof::Implies(this) => this.signature(),
            Fof::Iff(this) => this.signature(),
            Fof::Exists(this) => this.signature(),
            Fof::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
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

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Fof::Top | Fof::Bottom => self.clone(),
            Fof::Atom(this) => this.transform_term(f).into(),
            Fof::Equals(this) => this.transform_term(f).into(),
            Fof::Not(this) => this.transform_term(f).into(),
            Fof::And(this) => this.transform_term(f).into(),
            Fof::Or(this) => this.transform_term(f).into(),
            Fof::Implies(this) => this.transform_term(f).into(),
            Fof::Iff(this) => this.transform_term(f).into(),
            Fof::Exists(this) => this.transform_term(f).into(),
            Fof::Forall(this) => this.transform_term(f).into(),
        }
    }
}

impl FormulaEx for Fof {
    fn precedence(&self) -> u8 {
        match self {
            Fof::Top => PRECEDENCE_ATOM,
            Fof::Bottom => PRECEDENCE_ATOM,
            Fof::Atom(this) => this.precedence(),
            Fof::Equals(this) => this.precedence(),
            Fof::Not(this) => this.precedence(),
            Fof::And(this) => this.precedence(),
            Fof::Or(this) => this.precedence(),
            Fof::Implies(this) => this.precedence(),
            Fof::Iff(this) => this.precedence(),
            Fof::Exists(this) => this.precedence(),
            Fof::Forall(this) => this.precedence(),
        }
    }
}

impl fmt::Display for Fof {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Top => write!(f, "⊤"),
            Self::Bottom => write!(f, "⟘"),
            Self::Atom(this) => this.fmt(f),
            Self::Equals(this) => this.fmt(f),
            Self::Not(this) => this.fmt(f),
            Self::And(this) => this.fmt(f),
            Self::Or(this) => this.fmt(f),
            Self::Implies(this) => this.fmt(f),
            Self::Iff(this) => this.fmt(f),
            Self::Exists(this) => this.fmt(f),
            Self::Forall(this) => this.fmt(f),
        }
    }
}

impl fmt::Debug for Fof {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Top => write!(f, "true"),
            Self::Bottom => write!(f, "false"),
            Self::Atom(this) => this.fmt(f),
            Self::Equals(this) => this.fmt(f),
            Self::Not(this) => this.fmt(f),
            Self::And(this) => this.fmt(f),
            Self::Or(this) => this.fmt(f),
            Self::Implies(this) => this.fmt(f),
            Self::Iff(this) => this.fmt(f),
            Self::Exists(this) => this.fmt(f),
            Self::Forall(this) => this.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Fof::*, *};
    use crate::{
        assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            Const, Func, Pred, EQ_SYM,
        },
        v,
    };

    #[test]
    fn top_to_string() {
        assert_eq!("⊤", Top.to_string());
    }

    #[test]
    fn top_free_vars() {
        let expected: Vec<&Var> = vec![];
        assert_eq!(expected, Top.free_vars());
    }

    #[test]
    fn top_signature() {
        let expected = Sig::new();
        assert_eq!(expected, Top.signature().unwrap());
    }

    #[test]
    fn bottom_to_string() {
        assert_eq!("⟘", Bottom.to_string());
    }

    #[test]
    fn bottom_free_vars() {
        let expected: Vec<&Var> = vec![];
        assert_eq_sorted_vecs!(&expected, &Bottom.free_vars());
    }

    #[test]
    fn bottom_signature() {
        let expected = Sig::new();
        assert_eq!(expected, Top.signature().unwrap());
    }

    #[test]
    fn atom_to_string() {
        assert_eq!("R()", fof!(R()).to_string());
        assert_eq!("R(x, y)", fof!(R(x, y)).to_string());
        assert_eq!("R(g(x, y))", fof!(R(g(x, y))).to_string());
        assert_eq!(
            "R(f(f(f(f(f(f(x)))))))",
            fof!(R(f(f(f(f(f(f(x)))))))).to_string()
        );
    }

    #[test]
    fn atom_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
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
    fn atom_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!(P(@c));
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!(P(f(x, @c)));
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 3,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("g"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            sig.add_constant(Const::from("d"));
            let formula = fof!(P(f(x, @c), @d, f(g(x), y)));
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!(P(f(x), f(x, y)));
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn equals_to_string() {
        assert_eq!("x = y", fof!((x) = (y)).to_string());
    }

    #[test]
    fn equals_free_vars() {
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
    fn equals_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from(EQ_SYM),
                arity: 2,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!((@c) = (@c));
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!([f(x)] = [f(x, y)]);
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn not_to_string() {
        assert_eq!("¬R()", fof!(~(R())).to_string());
        assert_eq!("¬(¬R())", fof!(~(~(R()))).to_string());
        assert_eq!("¬(x = y)", fof!(~((x) = (y))).to_string());
        assert_eq!("¬R(x, y)", fof!(~(R(x, y))).to_string());
        assert_eq!("¬(R(x, y) ∧ Q(z))", fof!(~{(R(x, y)) & (Q(z))}).to_string());
        assert_eq!("¬(R(x, y) ∨ Q(z))", fof!(~{(R(x, y)) | (Q(z))}).to_string(),);
        assert_eq!(
            "¬(R(x, y) ∨ ¬Q(z))",
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
    fn not_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(~(R())).free_vars());
        }
        {
            let expected: Vec<&Var> = vec![];
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
    fn not_signature() {
        let mut sig = Sig::new();
        sig.add_predicate(PredSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FuncSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula = fof!(~[P(f(@c), y)]);
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn and_to_string() {
        assert_eq!("P() ∧ Q()", fof!((P()) & (Q())).to_string());
        assert_eq!("P() ∧ x = y", fof!({ P() } & { (x) = (y) }).to_string());
        assert_eq!("P() ∧ ¬Q()", fof!({P()} & {~(Q())}).to_string());
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
    fn and_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
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
    fn and_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!([P(f(x), y)] & [Q(@c)]);
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!([P(x)] & [P(x, y)]);
            assert!(formula.signature().is_err());
        }
        {
            let formula = fof!([P(f(x))] & [P(f(x, y))]);
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn or_to_string() {
        assert_eq!("P() ∨ Q()", fof!((P()) | (Q())).to_string());
        assert_eq!("P() ∨ x = y", fof!({ P() } | { (x) = (y) }).to_string());
        assert_eq!("P() ∨ ¬Q()", fof!({P()} | {~(Q())}).to_string());
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
    fn or_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
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
    fn or_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!([P(f(x), y)] | [Q(@c)]);
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!([P(x)] | [P(x, y)]);
            assert!(formula.signature().is_err());
        }
        {
            let formula = fof!([P(f(x))] | [P(f(x, y))]);
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn implies_to_string() {
        assert_eq!("P() → Q()", fof!((P()) -> (Q())).to_string());
        assert_eq!("P() → x = y", fof!({P()} -> {(x) = (y)}).to_string());
        assert_eq!("P() → ¬Q()", fof!({P()} -> {~(Q())}).to_string());
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
    fn implies_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
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
    fn implies_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!([P(f(x), y)] -> [Q(@c)]);
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!([P(x)] -> [P(x, y)]);
            assert!(formula.signature().is_err());
        }
        {
            let formula = fof!([P(f(x))] -> [P(f(x, y))]);
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn iff_to_string() {
        assert_eq!("P() ⇔ Q()", fof!((P()) <=> (Q())).to_string());
        assert_eq!("P() ⇔ x = y", fof!({P()} <=> {(x) = (y)}).to_string());
        assert_eq!("P() ⇔ ¬Q()", fof!({P()} <=> {~(Q())}).to_string());
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
    fn iff_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
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
    fn iff_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: Func::from("f"),
                arity: 1,
            })
            .unwrap();
            sig.add_constant(Const::from("c"));
            let formula = fof!([P(f(x), y)] <=> [Q(@c)]);
            assert_eq!(sig, formula.signature().unwrap());
        }
        {
            let formula = fof!([P(x)] <=> [P(x, y)]);
            assert!(formula.signature().is_err());
        }
        {
            let formula = fof!([P(f(x))] <=> [P(f(x, y))]);
            assert!(formula.signature().is_err());
        }
    }

    #[test]
    fn exists_to_string() {
        assert_eq!("∃ x. P(x)", fof!(? x. (P(x))).to_string());
        assert_eq!("∃ x, y. P(x, y)", fof!(? x, y. (P(x, y))).to_string());
        assert_eq!("∃ x, y. x = y", fof!(? x, y. ((x) = (y))).to_string());
        assert_eq!("∃ x. ¬Q(x)", fof!(? x. (~(Q(x)))).to_string());
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
    fn exists_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(? x. (P(x))).free_vars());
        }
        {
            let expected: Vec<&Var> = vec![];
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
    fn exists_signature() {
        let mut sig = Sig::new();
        sig.add_predicate(PredSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FuncSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula = fof!(?x . [P(f(@c), y)]);
        assert_eq!(sig, formula.signature().unwrap());
    }

    #[test]
    fn forall_to_string() {
        assert_eq!("∀ x. P(x)", fof!(! x. (P(x))).to_string());
        assert_eq!("∀ x, y. P(x, y)", fof!(! x, y. (P(x, y))).to_string());
        assert_eq!("∀ x, y. x = y", fof!(! x, y. ((x) = (y))).to_string());
        assert_eq!("∀ x. ¬Q(x)", fof!(! x. (~(Q(x)))).to_string());
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
    fn forall_free_vars() {
        {
            let expected: Vec<&Var> = vec![];
            assert_eq_sorted_vecs!(expected, fof!(! x. (P(x))).free_vars());
        }
        {
            let expected: Vec<&Var> = vec![];
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

    #[test]
    fn forall_signature() {
        let mut sig = Sig::new();
        sig.add_predicate(PredSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FuncSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula = fof!(!x . [P(f(@c), y)]);
        assert_eq!(sig, formula.signature().unwrap());
    }
}
