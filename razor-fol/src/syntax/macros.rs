/*! Implements macros for creating syntactic objects. */

/// Creates a [variable] from a given identifier.
///
/// [variable]: crate::syntax::V
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::V;
/// use razor_fol::v;
///
/// let var = v!(v);
///
/// assert_eq!(V::from("v"), var);
/// ```
#[macro_export]
macro_rules! v {
    ($v:ident) => {
        $crate::syntax::V::from(stringify!($v))
    };
}

/// Creates a [function symbol] from a given identifier.
///
/// [function symbol]: crate::syntax::F
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::F;
/// use razor_fol::f;
///
/// let func = f!(f);
///
/// assert_eq!(F::from("f"), func);
/// ```
#[macro_export]
macro_rules! f {
    ($f:ident) => {
        $crate::syntax::F::from(stringify!($f))
    };
}

/// Creates a [constant] from a given identifier.
///
/// [constant]: crate::syntax::C
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::C;
/// use razor_fol::c;
///
/// let constant = c!(c);
///
/// assert_eq!(C::from("c"), constant);
/// ```
#[macro_export]
macro_rules! c {
    ($c:ident) => {
        $crate::syntax::C::from(stringify!($c))
    };
}

/// Creates a [predicate symbol] from a given identifier.
///
/// [predicate symbol]: crate::syntax::Pred
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::Pred;
/// use razor_fol::pred;
///
/// let pred = pred!(P);
///
/// assert_eq!(Pred::from("P"), pred);
/// ```
#[macro_export]
macro_rules! pred {
    ($p:ident) => {
        $crate::syntax::Pred::from(stringify!($p))
    };
}

/// Parses the input tokens into a [term].
///
/// [term]: crate::syntax::Term
/// **Example**:
/// ```rust
/// # use razor_fol::{syntax::term::Complex, f, v, c};
/// use razor_fol::term;
///
/// // variable term:
/// let v = term!(v);
///
/// assert_eq!(Complex::from(v!(v)), v);
///
/// // constant term (preceded by `@`):
/// let c = term!(@c);
///
/// assert_eq!(Complex::from(c!(c)), c);
///
/// // complex term:
/// let t = term!(f(x, g(@c, y)));
///
/// assert_eq!(
///     f!(f).app(
///         vec![v!(x).into(),
///         f!(g).app(vec![c!(c).into(), v!(y).into()])]),
///     t,
/// );
/// ```
#[macro_export]
macro_rules! term {
    ($v:ident) => {
        $crate::syntax::term::Complex::Var {
            variable: $crate::v!($v),
        }
    };
    (@$c:ident) => {
        $crate::syntax::term::Complex::Const {
            constant: $crate::c!($c),
        }
    };
    ($func:ident ($($t:tt)*)) => {
        {
            let ts = $crate::terms!($($t)*);
            $crate::f!($func).app(ts)
        }
    };
}

/// Parses the input tokens into a list of [terms].
/// This macro is primarily used by [`fof!`] to parse term tuples.
///
/// [terms]: crate::syntax::Term
/// [`fof!`]: crate::fof!
/// **Example**:
/// ```rust
/// # use razor_fol::term;
/// use razor_fol::terms;
///
/// let terms = terms!(v, @c, f(x));
///
/// assert_eq!(
///     vec![term!(v), term!(@c), term!(f(x))],
///     terms,
/// );
/// ```
#[macro_export]
macro_rules! terms {
    (@acc () -> ($($result:tt)*)) => {
        vec![$($result)*]
    };
    (@acc ($v:ident $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* $crate::term!($v),))
    };
    (@acc (@$c:ident $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* $crate::term!(@$c),))
    };
    (@acc ($func:ident ($($t:tt)*) $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        {
            let term = $crate::term!($func ($($t)*));
            $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* term,))
        }
    };
    () => {
        Vec::<$crate::syntax::term::Complex>::new()
    };
    ($($tail:tt)*) => {
        $crate::terms!(@acc ($($tail)*) -> ())
    };
}

/// Parses the input tokens as a [first-order formula].
///
/// **Note:**
/// The syntax of the input to this macro resembles the [compact] variation of Razor's texual
/// input with two differeces:
///
/// 1. This macro requires subformulae at the same level of a complex formula to be wrapped
/// in one of `(...)`, `[...]`, or `{...}`. This requirement also applies to the
/// terms on the two sides of `=` in equalities. For example:
/// `(<LEFT>) & (<RIGHT>)`, `[<LEFT>] | [<RIGHT>]`, and `{<LEFT>} = {<RIGHT>}` are
/// all valid inputs. But `<LEFT> | <RIGHT>`, `?x . <FORMULA>`, and `(<LEFT>) & [<RIGHT>]`
/// are invalid.
/// 2. Unlike the textual form where constants are preceded by `'`, in the macro input,
/// constants are preceded by `@`.
///
/// [first-order formula]: crate::syntax::FOF
/// [compact]: https://salmans.github.io/rusty-razor/syntax/variations.html
/// **Example**:
/// ```rust
/// use razor_fol::fof;
///
/// // truth:
/// let f_top = fof!('|');
/// assert_eq!(r"⊤", f_top.to_string());
///
/// // falsehood:
/// let f_bot = fof!(_|_);
/// assert_eq!(r"⟘", f_bot.to_string());
///
/// // atomic first-order formula:
/// let f_atom = fof!(P(@c, f(x)));
/// assert_eq!(r"P('c, f(x))", f_atom.to_string());
///
/// // equality:
/// let f_eq = fof!((f(x)) = (y));
/// assert_eq!(r"f(x) = y", f_eq.to_string());
///
/// // negation:
/// let f_neg = fof!(~[P(f(x))]);
/// assert_eq!(r"¬P(f(x))", f_neg.to_string());
///
/// // conjunction:
/// let f_and = fof!([P(x)] & [Q(f(x))]);
/// assert_eq!(r"P(x) ∧ Q(f(x))", f_and.to_string());
///
/// // disjunction:
/// let f_or = fof!({(x) = (y)} | {P(@a)});
/// assert_eq!(r"(x = y) ∨ P('a)", f_or.to_string());
///
/// // implication:
/// let f_impl = fof!([P(x)] -> [_|_]);
/// assert_eq!(r"P(x) → ⟘", f_impl.to_string());
///
/// // bi-implication:
/// let f_iff = fof!({P(x, y)} <=> {(x) = (y)});
/// assert_eq!(r"P(x, y) ⇔ (x = y)", f_iff.to_string());
///
/// // existential quantifier:
/// let f_ex = fof!(?x, y. (P(x, y)));
/// assert_eq!(r"∃ x, y. P(x, y)", f_ex.to_string());
///
/// // existential quantifier:
/// let f_for = fof!(!x. [Q(x, @b)]);
/// assert_eq!(r"∀ x. Q(x, 'b)", f_for.to_string());
///
/// // complex first-order formula:
/// let fmla = fof!(!x, y. {[(P(x)) & (Q(y))] -> [R(x, y)]});
/// assert_eq!(r"∀ x, y. ((P(x) ∧ Q(y)) → R(x, y))", fmla.to_string());
/// ```
#[macro_export]
macro_rules! fof {
    // Top
    ('|') => {
        $crate::syntax::FOF::Top
    };
    // Bottom
    (_|_) => {
        $crate::syntax::FOF::Bottom
    };
    // Atom
    ($pred:ident ($($t:tt)*)) => {
        {
            let ts = $crate::terms!($($t)*);
            $crate::syntax::Pred::from(stringify!($pred)).app(ts)
        }
    };
    // Equality
    (($($left:tt)*) = ($($right:tt)*)) => {
        $crate::fof!(@equals ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] = [$($right:tt)*]) => {
        $crate::fof!(@equals ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} = {$($right:tt)*}) => {
        $crate::fof!(@equals ($($left)*) ($($right)*))
    };
    // Negation
    (~($($fmla:tt)*)) => {
        $crate::fof!(@not ($($fmla)*))
    };
    (~[$($fmla:tt)*]) => {
        $crate::fof!(@not ($($fmla)*))
    };
    (~{$($fmla:tt)*}) => {
        $crate::fof!(@not ($($fmla)*))
    };
    // Conjunction
    (($($left:tt)*) & ($($right:tt)*)) => {
        fof!(@and ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] & [$($right:tt)*]) => {
        fof!(@and ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} & {$($right:tt)*}) => {
        fof!(@and ($($left)*) ($($right)*))
    };
    //Disjunction
    (($($left:tt)*) | ($($right:tt)*)) => {
        fof!(@or ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] | [$($right:tt)*]) => {
        fof!(@or ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} | {$($right:tt)*}) => {
        fof!(@or ($($left)*) ($($right)*))
    };
    // Implication
    (($($left:tt)*) -> ($($right:tt)*)) => {
        fof!(@implies ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] -> [$($right:tt)*]) => {
        fof!(@implies ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} -> {$($right:tt)*}) => {
        fof!(@implies ($($left)*) ($($right)*))
    };
    // Bi-implication
    (($($left:tt)*) <=> ($($right:tt)*)) => {
        fof!(@iff ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] <=> [$($right:tt)*]) => {
        fof!(@iff ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} <=> {$($right:tt)*}) => {
        fof!(@iff ($($left)*) ($($right)*))
    };
    // Universally Quantified
    (! $($v:ident),+ . ($($fmla:tt)*)) => {
        fof!(@forall ($($v),+) ($($fmla)*))
    };
    (! $($v:ident),+ . [$($fmla:tt)*]) => {
        fof!(@forall ($($v),+) ($($fmla)*))
    };
    (! $($v:ident),+ . {$($fmla:tt)*}) => {
        fof!(@forall ($($v),+) ($($fmla)*))
    };
    // Existentially Quantified
    (? $($v:ident),+ . ($($fmla:tt)*)) => {
        fof!(@exists ($($v),+) ($($fmla)*))
    };
    (? $($v:ident),+ . [$($fmla:tt)*]) => {
        fof!(@exists ($($v),+) ($($fmla)*))
    };
    (? $($v:ident),+ . {$($fmla:tt)*}) => {
        fof!(@exists ($($v),+) ($($fmla)*))
    };
    // Construction rules
    (@equals ($($left:tt)*) ($($right:tt)*)) => {
        {
            let left = $crate::term!($($left)*);
            let right = $crate::term!($($right)*);
            $crate::syntax::FOF::from($crate::syntax::formula::Equals{left, right})
        }
    };
    (@not ($($fmla:tt)*)) => {
        $crate::syntax::FOF::from($crate::syntax::formula::Not{ formula: fof!($($fmla)*) })
    };
    (@and ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::FOF::from(
            $crate::syntax::formula::And {
                left: fof!($($left)*),
                right: fof!($($right)*),
            }
        )
    };
    (@or ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::FOF::from(
            $crate::syntax::formula::Or {
                left: fof!($($left)*),
                right: fof!($($right)*),
            }
        )
    };
    (@implies ($($premise:tt)*) ($($consequence:tt)*)) => {
        $crate::syntax::FOF::from(
            $crate::syntax::formula::Implies {
                premise: fof!($($premise)*),
                consequence: fof!($($consequence)*),
            }
        )
    };
    (@iff ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::FOF::from(
            $crate::syntax::formula::Iff {
                left: fof!($($left)*),
                right: fof!($($right)*),
            }
        )
    };
    (@forall ($($v:ident),+) ($($fmla:tt)*)) => {
        {
            let vs = vec![$($crate::syntax::V::from(stringify!($v)),)+];
            $crate::syntax::FOF::from(
                $crate::syntax::formula::Forall {
                    variables: vs,
                    formula: fof!($($fmla)*),
                }
            )
        }
    };
    (@exists ($($v:ident),+) ($($fmla:tt)*)) => {
        {
            let vs = vec![$($crate::syntax::V::from(stringify!($v)),)+];
            $crate::syntax::FOF::from(
                $crate::syntax::formula::Exists {
                    variables: vs,
                    formula: fof!($($fmla)*),
                }
            )
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_macro() {
        assert_eq!("⊤", fof!('|').to_string());
        assert_eq!("⟘", fof!(_|_).to_string());

        assert_eq!("P()", fof!(P()).to_string());
        assert_eq!("P(x)", fof!(P(x)).to_string());
        assert_eq!("P(x, 'c)", fof!(P(x, @c)).to_string());
        assert_eq!("P(x, 'c, y, 'd)", fof!(P(x, @c, y, @d)).to_string());
        assert_eq!("P(f(x))", fof!(P(f(x))).to_string());
        assert_eq!("P(g(z), f(x, g(y)))", fof!(P(g(z), f(x, g(y)))).to_string());

        assert_eq!("x = y", fof!((x) = (y)).to_string());
        assert_eq!("'c = y", fof!((@c) = (y)).to_string());
        assert_eq!(
            "h() = f(x, g(y, 'c))",
            fof!((h()) = (f(x, g(y, @c)))).to_string()
        );
        assert_eq!("x = y", fof!([x] = [y]).to_string());
        assert_eq!("x = y", fof!({ x } = { y }).to_string());

        assert_eq!("¬P(x, 'c)", fof!(~(P(x, @c))).to_string());
        assert_eq!("¬P(x, 'c)", fof!(~[P(x, @c)]).to_string());
        assert_eq!("¬P(x, 'c)", fof!(~{P(x, @c)}).to_string());

        assert_eq!("P(x, 'c) ∧ ⊤", fof!((P(x, @c)) & ('|')).to_string());
        assert_eq!("P(x, 'c) ∧ ⟘", fof!((P(x, @c)) & (_|_)).to_string());

        assert_eq!("P(x, 'c) ∧ Q(z)", fof!((P(x, @c)) & (Q(z))).to_string());
        assert_eq!("P(x, 'c) ∧ Q(z)", fof!([P(x, @c)] & [Q(z)]).to_string());
        assert_eq!("P(x, 'c) ∧ Q(z)", fof!({P(x, @c)} & {Q(z)}).to_string());

        assert_eq!("P(x, 'c) ∨ Q(z)", fof!((P(x, @c)) | (Q(z))).to_string());
        assert_eq!("P(x, 'c) ∨ Q(z)", fof!([P(x, @c)] | [Q(z)]).to_string());
        assert_eq!("P(x, 'c) ∨ Q(z)", fof!({P(x, @c)} | {Q(z)}).to_string());

        assert_eq!("P(x, 'c) → Q(z)", fof!((P(x, @c)) -> (Q(z))).to_string());
        assert_eq!("P(x, 'c) → Q(z)", fof!([P(x, @c)] -> [Q(z)]).to_string());
        assert_eq!("P(x, 'c) → Q(z)", fof!({P(x, @c)} -> {Q(z)}).to_string());

        assert_eq!("P(x, 'c) ⇔ Q(z)", fof!((P(x, @c)) <=> (Q(z))).to_string());
        assert_eq!("P(x, 'c) ⇔ Q(z)", fof!([P(x, @c)] <=> [Q(z)]).to_string());
        assert_eq!("P(x, 'c) ⇔ Q(z)", fof!({P(x, @c)} <=> {Q(z)}).to_string());

        assert_eq!("∀ x. P(x, \'c)", fof!(!x . (P(x, @c))).to_string());
        assert_eq!("∀ x. P(x, \'c)", fof!(!x . [P(x, @c)]).to_string());
        assert_eq!("∀ x. P(x, \'c)", fof!(!x . {P(x, @c)}).to_string());
        assert_eq!("∀ x, y. P(x, \'c)", fof!(!x, y . (P(x, @c))).to_string());

        assert_eq!("∃ x. P(x, \'c)", fof!(?x . (P(x, @c))).to_string());
        assert_eq!("∃ x. P(x, \'c)", fof!(?x . [P(x, @c)]).to_string());
        assert_eq!("∃ x. P(x, \'c)", fof!(?x . {P(x, @c)}).to_string());
        assert_eq!("∃ x, y. P(x, \'c)", fof!(?x, y . (P(x, @c))).to_string());
    }
}
