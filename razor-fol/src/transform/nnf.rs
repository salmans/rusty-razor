/*! Defines formulae in Negation Normal Form (NNF) and implements an algorithm for
transforming an [`Fof`] to an [`Nnf`].

[`Fof`]: crate::syntax::Fof
*/
use crate::syntax::{
    formula::{clause::Literal, *},
    term::Complex,
    Error, Fof, Sig, Var,
};

/// Represents a formula in Negation Normal Form (NNF).
///
/// **Hint**: An NNF is a formula where negation is applied only to its atomic (including
/// equations) sub-formulae.
#[derive(PartialEq, Clone)]
pub enum Nnf {
    /// Is the logical top (⊤) or truth.
    Top,

    /// Is the logical bottom (⟘) or falsehood.    
    Bottom,

    /// Is a literal, wrapping a [`Literal`].
    Literal(Literal<Complex>),

    /// Is a conjunction of two formulae, wrapping an [`And`].    
    And(Box<And<Nnf>>),

    /// Is a disjunction of two formulae, wrapping an [`Or`].
    Or(Box<Or<Nnf>>),

    /// Is an existentially quantified NNF, wrapping an [`Exists`].
    Exists(Box<Exists<Nnf>>),

    /// Is a universally quantified NNF, wrapping a [`Forall`].    
    Forall(Box<Forall<Nnf>>),
}

impl From<Atom<Complex>> for Nnf {
    fn from(value: Atom<Complex>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Equals<Complex>> for Nnf {
    fn from(value: Equals<Complex>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Atom<Complex>>> for Nnf {
    fn from(value: Not<Atom<Complex>>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<Not<Equals<Complex>>> for Nnf {
    fn from(value: Not<Equals<Complex>>) -> Self {
        Self::Literal(value.into())
    }
}

impl From<And<Nnf>> for Nnf {
    fn from(value: And<Nnf>) -> Self {
        Self::And(value.into())
    }
}

impl From<Or<Nnf>> for Nnf {
    fn from(value: Or<Nnf>) -> Self {
        Self::Or(value.into())
    }
}

impl From<Exists<Nnf>> for Nnf {
    fn from(value: Exists<Nnf>) -> Self {
        Self::Exists(Box::new(value))
    }
}

impl From<Forall<Nnf>> for Nnf {
    fn from(value: Forall<Nnf>) -> Self {
        Self::Forall(Box::new(value))
    }
}

impl From<Literal<Complex>> for Nnf {
    fn from(value: Literal<Complex>) -> Self {
        Self::Literal(value)
    }
}

/// Is the trait of [`Formula`] types that can be transformed to [`Nnf`].
pub trait ToNnf: Formula {
    /// Transforms `self` to a Negation Normal Form (NNF).
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// use razor_fol::transform::ToNnf;
    ///
    /// let formula: Fof = "not (P(x) iff Q(y))".parse().unwrap();
    /// let nnf = formula.nnf();
    ///
    /// assert_eq!("(P(x) ∧ ¬Q(y)) ∨ (¬P(x) ∧ Q(y))", nnf.to_string());
    /// ```
    fn nnf(&self) -> Nnf;
}

impl ToNnf for Fof {
    fn nnf(&self) -> Nnf {
        nnf(self)
    }
}

impl<T: ToNnf> From<T> for Nnf {
    fn from(value: T) -> Self {
        value.nnf()
    }
}

impl Nnf {
    #[inline(always)]
    fn neg(atom: Atomic<Complex>) -> Self {
        Literal::Neg(atom).into()
    }

    #[inline(always)]
    fn and(self, formula: Self) -> Self {
        And {
            left: self,
            right: formula,
        }
        .into()
    }

    #[inline(always)]
    fn or(self, formula: Self) -> Self {
        Or {
            left: self,
            right: formula,
        }
        .into()
    }

    #[inline(always)]
    fn exists(variables: Vec<Var>, formula: Self) -> Self {
        Exists { variables, formula }.into()
    }

    #[inline(always)]
    fn forall(variables: Vec<Var>, formula: Self) -> Self {
        Forall { variables, formula }.into()
    }
}

impl Formula for Nnf {
    type Term = Complex;

    fn signature(&self) -> Result<Sig, Error> {
        match self {
            Nnf::Top | Nnf::Bottom => Ok(Sig::default()),
            Nnf::Literal(this) => this.signature(),
            Nnf::And(this) => this.signature(),
            Nnf::Or(this) => this.signature(),
            Nnf::Exists(this) => this.signature(),
            Nnf::Forall(this) => this.signature(),
        }
    }

    fn free_vars(&self) -> Vec<&Var> {
        match self {
            Self::Top => Vec::new(),
            Self::Bottom => Vec::new(),
            Self::Literal(this) => this.free_vars(),
            Self::And(this) => this.free_vars(),
            Self::Or(this) => this.free_vars(),
            Self::Exists(this) => this.free_vars(),
            Self::Forall(this) => this.free_vars(),
        }
    }

    fn transform_term(&self, f: &impl Fn(&Complex) -> Complex) -> Self {
        match self {
            Self::Top | Self::Bottom => self.clone(),
            Self::Literal(this) => this.transform_term(f).into(),
            Self::And(this) => this.transform_term(f).into(),
            Self::Or(this) => this.transform_term(f).into(),
            Self::Exists(this) => this.transform_term(f).into(),
            Self::Forall(this) => this.transform_term(f).into(),
        }
    }
}

impl std::fmt::Display for Nnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Fof::from(self).fmt(f)
    }
}

impl FormulaEx for Nnf {
    fn precedence(&self) -> u8 {
        match self {
            Nnf::Top | Nnf::Bottom => PRECEDENCE_ATOM,
            Nnf::Literal(this) => this.precedence(),
            Nnf::And(this) => this.precedence(),
            Nnf::Or(this) => this.precedence(),
            Nnf::Exists(this) => this.precedence(),
            Nnf::Forall(this) => this.precedence(),
        }
    }
}

impl From<Nnf> for Fof {
    fn from(value: Nnf) -> Self {
        match value {
            Nnf::Top => Self::Top,
            Nnf::Bottom => Self::Bottom,
            Nnf::Literal(lit) => match lit {
                Literal::Pos(pos) => match pos {
                    Atomic::Atom(this) => this.into(),
                    Atomic::Equals(this) => this.into(),
                },
                Literal::Neg(neg) => match neg {
                    Atomic::Atom(this) => Self::not(this.into()),
                    Atomic::Equals(this) => Self::not(this.into()),
                },
            },
            Nnf::And(this) => Self::from(this.left).and(this.right.into()),
            Nnf::Or(this) => Self::from(this.left).or(this.right.into()),
            Nnf::Exists(this) => Self::exists(this.variables, this.formula.into()),
            Nnf::Forall(this) => Self::forall(this.variables, this.formula.into()),
        }
    }
}

impl From<&Nnf> for Fof {
    fn from(value: &Nnf) -> Self {
        value.clone().into()
    }
}

// Recursively pushes negation in the formula.
#[inline]
fn push_not(formula: &Fof) -> Nnf {
    match formula {
        Fof::Top => Nnf::Bottom,
        Fof::Bottom => Nnf::Top,
        Fof::Atom(this) => Nnf::neg(this.clone().into()),
        Fof::Equals(this) => Nnf::neg(this.clone().into()),
        Fof::Not(this) => nnf(&this.formula),
        Fof::And(this) => nnf(&Fof::not(this.left.clone())).or(nnf(&Fof::not(this.right.clone()))),
        Fof::Or(this) => nnf(&Fof::not(this.left.clone())).and(nnf(&Fof::not(this.right.clone()))),
        Fof::Implies(this) => nnf(&this.premise).and(nnf(&Fof::not(this.consequence.clone()))),
        Fof::Iff(this) => {
            let left_and_not_right = nnf(&this.left).and(nnf(&Fof::not(this.right.clone())));
            let not_left_and_right = nnf(&Fof::not(this.left.clone())).and(nnf(&this.right));
            left_and_not_right.or(not_left_and_right)
        }
        Fof::Exists(this) => {
            Nnf::forall(this.variables.clone(), nnf(&Fof::not(this.formula.clone())))
        }
        Fof::Forall(this) => {
            Nnf::exists(this.variables.clone(), nnf(&Fof::not(this.formula.clone())))
        }
    }
}

fn nnf(fmla: &Fof) -> Nnf {
    match fmla {
        Fof::Top => Nnf::Top,
        Fof::Bottom => Nnf::Bottom,
        Fof::Atom(this) => this.clone().into(),
        Fof::Equals(this) => this.clone().into(),
        Fof::Not(this) => push_not(&this.formula),
        Fof::And(this) => nnf(&this.left).and(nnf(&this.right)),
        Fof::Or(this) => nnf(&this.left).or(nnf(&this.right)),
        Fof::Implies(this) => nnf(&Fof::not(this.premise.clone())).or(nnf(&this.consequence)),
        Fof::Iff(this) => {
            let not_left_or_right = nnf(&Fof::not(this.left.clone())).or(nnf(&this.right));
            let left_or_not_right = nnf(&this.left).or(nnf(&Fof::not(this.right.clone())));
            not_left_or_right.and(left_or_not_right)
        }
        Fof::Exists(this) => Nnf::exists(this.variables.clone(), nnf(&this.formula)),
        Fof::Forall(this) => Nnf::forall(this.variables.clone(), nnf(&this.formula)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assert_debug_string, assert_eq_sorted_vecs, fof,
        syntax::{
            signature::{FuncSig, PredSig},
            EQ_SYM,
        },
        term, v,
    };

    fn nnf(formula: &Fof) -> Fof {
        formula.nnf().into()
    }

    #[test]
    fn test_nnf() {
        {
            let formula: Fof = "true".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: Fof = "false".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: Fof = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: Fof = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("~P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x) | Q(y)) & (P(x) | ~Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "?x. P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "!x. P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        // sanity checking
        {
            let formula: Fof = "~true".parse().unwrap();
            assert_debug_string!("false", nnf(&formula));
        }
        {
            let formula: Fof = "~false".parse().unwrap();
            assert_debug_string!("true", nnf(&formula));
        }
        {
            let formula: Fof = "~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~~~~P(x)".parse().unwrap();
            assert_debug_string!("P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~~x = y".parse().unwrap();
            assert_debug_string!("x = y", nnf(&formula));
        }
        {
            let formula: Fof = "~(P(x) & Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) | ~Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) & ~Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & ~Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string!("(P(x) & ~Q(y)) | (~P(x) & Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string!("(~P(x) & ~Q(y)) | R(z)", nnf(&formula));
        }
        {
            let formula: Fof = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string!(
                "((~P(x) & ~Q(y)) | R(z)) & ((P(x) | Q(y)) | ~R(z))",
                nnf(&formula),
            );
        }
        {
            let formula: Fof = "~?x. P(x)".parse().unwrap();
            assert_debug_string!("! x. ~P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~!x. P(x)".parse().unwrap();
            assert_debug_string!("? x. ~P(x)", nnf(&formula));
        }
        // recursive application
        {
            let formula: Fof = "~~P(x) & ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~~P(x) | ~~Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~~P(x) -> ~~Q(y)".parse().unwrap();
            assert_debug_string!("~P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string!("(~P(x) | Q(y)) & (P(x) | ~Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "?x. ~~P(x)".parse().unwrap();
            assert_debug_string!("? x. P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "!x. ~~P(x)".parse().unwrap();
            assert_debug_string!("! x. P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~~~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", nnf(&formula));
        }
        {
            let formula: Fof = "~(~P(x) & ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(~P(x) | ~Q(y))".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(~P(x) -> ~Q(y))".parse().unwrap();
            assert_debug_string!("~P(x) & Q(y)", nnf(&formula));
        }
        {
            let formula: Fof = "~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) | (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(P(x) & Q(x)) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!("(~P(x) | ~Q(x)) & (P(y) & Q(y))", nnf(&formula));
        }
        {
            let formula: Fof = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string!(
                "((~P(x) | ~Q(x)) & (P(y) & Q(y))) | ((P(x) & Q(x)) & (~P(y) | ~Q(y)))",
                nnf(&formula),
            );
        }
        {
            let formula: Fof = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) & ~Q(y)))", nnf(&formula));
        }
        {
            let formula: Fof = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string!("(! x. ~P(x)) | (? y. ~Q(y))", nnf(&formula));
        }
    }

    #[test]
    fn nnf_free_vars() {
        {
            let nnf = fof!('|').nnf();
            assert_eq!(Vec::<&Var>::new(), nnf.free_vars());
        }
        {
            let nnf = fof!({!x. {? y. {[P(x, y)] | [~(Q(z))]}}} & {[~(R(x, z))] | [R(@c)]}).nnf();
            assert_eq_sorted_vecs!(
                vec![v!(x), v!(z)].iter().collect::<Vec<_>>(),
                nnf.free_vars()
            );
        }
    }

    #[test]
    fn nnf_transform() {
        let nnf = fof!({!x. {? y. {[P(f(x), y)] | [~(Q(z))]}}} & {[~(R(f(x), z))] | [R(@c)]}).nnf();
        let f = |t: &Complex| {
            {
                if t == &term!(f(x)) {
                    term!(z)
                } else {
                    t.clone()
                }
            }
            .into()
        };
        assert_eq!(
            fof!({!x. {? y. {[P(z, y)] | [~(Q(z))]}}} & {[~(R(z, z))] | [R(@c)]}),
            Fof::from(nnf.transform_term(&f))
        );
    }

    #[test]
    fn nnf_signature() {
        {
            let mut sig = Sig::new();
            sig.add_predicate(PredSig {
                symbol: "P".into(),
                arity: 1,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: "Q".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_predicate(PredSig {
                symbol: EQ_SYM.into(),
                arity: 2,
            })
            .unwrap();
            sig.add_function(FuncSig {
                symbol: "f".into(),
                arity: 2,
            })
            .unwrap();
            sig.add_constant("c".into());

            let nnf =
                fof!({!x. {? y. {[P(f(x, y))] | [~(Q(z, z))]}}} & {[~(Q(f(x, y), @c))] | [(x) = (@c)]})
                    .nnf();
            assert_eq!(sig, nnf.signature().unwrap());
        }
        {
            let nnf = fof!({ P(x, x) } & { ~(P(x)) }).nnf();
            assert!(nnf.signature().is_err());
        }
    }
}
