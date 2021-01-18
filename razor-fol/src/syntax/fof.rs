/*! Defines the syntax of first-order formulae with equality.*/
use super::Var;
use super::{formula::*, qff::QFF, term::Complex, Sig};
use std::fmt;

/// Is an abstract syntax tree (AST) for first-order formulae.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FOF {
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

impl From<Atom<Complex>> for FOF {
    fn from(value: Atom<Complex>) -> Self {
        Self::Atom(value)
    }
}

impl From<Equals<Complex>> for FOF {
    fn from(value: Equals<Complex>) -> Self {
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

impl From<QFF> for FOF {
    fn from(value: QFF) -> Self {
        match value {
            QFF::Top => Self::Top,
            QFF::Bottom => Self::Bottom,
            QFF::Atom(this) => Self::Atom(this),
            QFF::Equals(this) => Self::Equals(this),
            QFF::Not(this) => FOF::not(this.formula.into()),
            QFF::And(this) => {
                let left: FOF = this.left.into();
                let right: FOF = this.right.into();
                left.and(right)
            }
            QFF::Or(this) => {
                let left: FOF = this.left.into();
                let right: FOF = this.right.into();
                left.or(right)
            }
            QFF::Implies(this) => {
                let pre: FOF = this.premise.into();
                let cons: FOF = this.consequence.into();
                pre.implies(cons)
            }
            QFF::Iff(this) => {
                let left: FOF = this.left.into();
                let right: FOF = this.right.into();
                left.iff(right)
            }
        }
    }
}

impl FOF {
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

    /// Returns a conjunction of the receiver and `formula`.
    #[inline(always)]
    pub fn and(self, formula: Self) -> Self {
        And {
            left: self,
            right: formula,
        }
        .into()
    }

    /// Returns a disjunction of the receiver and `formula`.
    #[inline(always)]
    pub fn or(self, formula: Self) -> Self {
        Or {
            left: self,
            right: formula,
        }
        .into()
    }

    /// Returns an implication between the receiver and `formula`.
    #[inline(always)]
    pub fn implies(self, formula: Self) -> Self {
        Implies {
            premise: self,
            consequence: formula,
        }
        .into()
    }

    /// Returns a bi-implication between the receiver and `formula`.
    #[inline(always)]
    pub fn iff(self, formula: Self) -> Self {
        Iff {
            left: self,
            right: formula,
        }
        .into()
    }
}

impl Formula for FOF {
    type Term = Complex;

    fn signature(&self) -> Result<super::Sig, super::Error> {
        match self {
            FOF::Top => Ok(Sig::new()),
            FOF::Bottom => Ok(Sig::new()),
            FOF::Atom(this) => this.signature(),
            FOF::Equals(this) => this.signature(),
            FOF::Not(this) => this.signature(),
            FOF::And(this) => this.signature(),
            FOF::Or(this) => this.signature(),
            FOF::Implies(this) => this.signature(),
            FOF::Iff(this) => this.signature(),
            FOF::Exists(this) => this.signature(),
            FOF::Forall(this) => this.signature(),
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

    fn transform(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            FOF::Top | FOF::Bottom => self.clone(),
            FOF::Atom(this) => this
                .predicate
                .clone()
                .app(this.terms.iter().map(f).collect()),
            FOF::Equals(this) => f(&this.left).equals(f(&this.right)),
            FOF::Not(this) => FOF::not(this.formula.transform(f)),
            FOF::And(this) => this.left.transform(f).and(this.right.transform(f)),
            FOF::Or(this) => this.left.transform(f).or(this.right.transform(f)),
            FOF::Implies(this) => this
                .premise
                .transform(f)
                .implies(this.consequence.transform(f)),
            FOF::Iff(this) => this.left.transform(f).iff(this.right.transform(f)),
            FOF::Exists(this) => FOF::exists(this.variables.clone(), this.formula.transform(f)),
            FOF::Forall(this) => FOF::forall(this.variables.clone(), this.formula.transform(f)),
        }
    }
}

impl FormulaEx for FOF {
    fn precedence(&self) -> u8 {
        match self {
            FOF::Top => PRECEDENCE_ATOM,
            FOF::Bottom => PRECEDENCE_ATOM,
            FOF::Atom(this) => this.precedence(),
            FOF::Equals(this) => this.precedence(),
            FOF::Not(this) => this.precedence(),
            FOF::And(this) => this.precedence(),
            FOF::Or(this) => this.precedence(),
            FOF::Implies(this) => this.precedence(),
            FOF::Iff(this) => this.precedence(),
            FOF::Exists(this) => this.precedence(),
            FOF::Forall(this) => this.precedence(),
        }
    }
}

impl fmt::Display for FOF {
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

impl fmt::Debug for FOF {
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
    use super::{FOF::*, *};
    use crate::{
        assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FSig, PSig},
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
            sig.add_predicate(PSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 3,
            })
            .unwrap();
            sig.add_function(FSig {
                symbol: Func::from("f"),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FSig {
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
            sig.add_predicate(PSig {
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
        sig.add_predicate(PSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
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
            sig.add_predicate(PSig {
                symbol: Pred::from("P"),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PSig {
                symbol: Pred::from("Q"),
                arity: 1,
            })
            .unwrap();
            sig.add_function(FSig {
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
        sig.add_predicate(PSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FSig {
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
        sig.add_predicate(PSig {
            symbol: Pred::from("P"),
            arity: 2,
        })
        .unwrap();
        sig.add_function(FSig {
            symbol: Func::from("f"),
            arity: 1,
        })
        .unwrap();
        sig.add_constant(Const::from("c"));
        let formula = fof!(!x . [P(f(@c), y)]);
        assert_eq!(sig, formula.signature().unwrap());
    }
}
