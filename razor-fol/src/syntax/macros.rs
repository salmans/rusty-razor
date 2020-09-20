/*! Implements macros for creating syntactic objects. */

/// Creates a [variable] from a given identifier.
///
/// [variable]: syntax/struct.V.html
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::V;
/// use razor_fol::v;
///
/// let var = v!(v);
///
/// assert_eq!(V("v".to_string()), var);
/// ```
#[macro_export]
macro_rules! v {
    ($v:ident) => {
        $crate::syntax::V::from(stringify!($v))
    };
}

/// Creates a [function symbol] from a given identifier.
///
/// [function symbol]: syntax/struct.F.html
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::F;
/// use razor_fol::f;
///
/// let func = f!(f);
///
/// assert_eq!(F("f".to_string()), func);
/// ```
#[macro_export]
macro_rules! f {
    ($f:ident) => {
        $crate::syntax::F::from(stringify!($f))
    };
}

/// Creates a [constant] from a given identifier.
///
/// [constant]: syntax/struct.C.html
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::C;
/// use razor_fol::c;
///
/// let constant = c!(c);
///
/// assert_eq!(C("c".to_string()), constant);
/// ```
#[macro_export]
macro_rules! c {
    ($c:ident) => {
        $crate::syntax::C::from(stringify!($c))
    };
}

/// Creates a [predicate symbol] from a given identifier.
///
/// [predicate symbol]: syntax/struct.Pred.html
/// **Example**:
/// ```rust
/// # use razor_fol::syntax::Pred;
/// use razor_fol::pred;
///
/// let pred = pred!(P);
///
/// assert_eq!(Pred("P".to_string()), pred);
/// ```
#[macro_export]
macro_rules! pred {
    ($p:ident) => {
        $crate::syntax::Pred::from(stringify!($p))
    };
}

/// Parses the input tokens into a [term].
///
/// [term]: syntax/enum.Term.html
/// **Example**:
/// ```rust
/// # use razor_fol::{syntax::Term, f, v, c};
/// use razor_fol::term;
///
/// // variable term:
/// let v = term!(v);
///
/// assert_eq!(Term::from(v!(v)), v);
///
/// // constant term (preceded by `@`):
/// let c = term!(@c);
///
/// assert_eq!(Term::from(c!(c)), c);
///
/// // complex term:
/// let t = term!(f(x, g(@c, y)));
///
/// assert_eq!(
///     f!(f).app::<Term>(
///         vec![v!(x).into(),
///         f!(g).app(vec![c!(c).into(), v!(y).into()])]),
///     t,
/// );
/// ```
#[macro_export]
macro_rules! term {
    ($v:ident) => {
        $crate::syntax::Term::Var {
            variable: $crate::v!($v),
        }
    };
    (@$c:ident) => {
        $crate::syntax::Term::Const {
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
/// This macro is primarily used by [`formula!`] to parse term tuples.
///
/// [terms]: syntax/enum.Term.html
/// [`formula!`]: ./macro.formula.html
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
        Vec::<$crate::syntax::Term>::new()
    };
    ($($tail:tt)*) => {
        $crate::terms!(@acc ($($tail)*) -> ())
    };
}

/// Parses the input tokens as a [formula].
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
/// [formula]: syntax/enum.Formula.html
/// [compact]: https://salmans.github.io/rusty-razor/syntax/variations.html
/// **Example**:
/// ```rust
/// use razor_fol::formula;
///
/// // truth:
/// let f_top = formula!('|');
/// assert_eq!(r"⊤", f_top.to_string());
///
/// // falsehood:
/// let f_bot = formula!(_|_);
/// assert_eq!(r"⟘", f_bot.to_string());
///
/// // atomic formula:
/// let f_atom = formula!(P(@c, f(x)));
/// assert_eq!(r"P('c, f(x))", f_atom.to_string());
///
/// // equality:
/// let f_eq = formula!((f(x)) = (y));
/// assert_eq!(r"f(x) = y", f_eq.to_string());
///
/// // negation:
/// let f_neg = formula!(~[P(f(x))]);
/// assert_eq!(r"¬P(f(x))", f_neg.to_string());
///
/// // conjunction:
/// let f_and = formula!([P(x)] & [Q(f(x))]);
/// assert_eq!(r"P(x) ∧ Q(f(x))", f_and.to_string());
///
/// // disjunction:
/// let f_or = formula!({(x) = (y)} | {P(@a)});
/// assert_eq!(r"(x = y) ∨ P('a)", f_or.to_string());
///
/// // implication:
/// let f_impl = formula!([P(x)] -> [_|_]);
/// assert_eq!(r"P(x) → ⟘", f_impl.to_string());
///
/// // bi-implication:
/// let f_iff = formula!({P(x, y)} <=> {(x) = (y)});
/// assert_eq!(r"P(x, y) ⇔ (x = y)", f_iff.to_string());
///
/// // existential quantifier:
/// let f_ex = formula!(?x, y. (P(x, y)));
/// assert_eq!(r"∃ x, y. P(x, y)", f_ex.to_string());
///
/// // existential quantifier:
/// let f_for = formula!(!x. [Q(x, @b)]);
/// assert_eq!(r"∀ x. Q(x, 'b)", f_for.to_string());
///
/// // complex formula:
/// let fmla = formula!(!x, y. {[(P(x)) & (Q(y))] -> [R(x, y)]});
/// assert_eq!(r"∀ x, y. ((P(x) ∧ Q(y)) → R(x, y))", fmla.to_string());
/// ```
#[macro_export]
macro_rules! formula {
    // Top
    ('|') => {
        $crate::syntax::Formula::Top
    };
    // Bottom
    (_|_) => {
        $crate::syntax::Formula::Bottom
    };
    // Atom
    ($pred:ident ($($t:tt)*)) => {
        {
            let ts = $crate::terms!($($t)*);
            $crate::syntax::Pred(stringify!($pred).to_string()).app(ts)
        }
    };
    // Equality
    (($($left:tt)*) = ($($right:tt)*)) => {
        $crate::formula!(@equals ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] = [$($right:tt)*]) => {
        $crate::formula!(@equals ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} = {$($right:tt)*}) => {
        $crate::formula!(@equals ($($left)*) ($($right)*))
    };
    // Negation
    (~($($fmla:tt)*)) => {
        $crate::formula!(@not ($($fmla)*))
    };
    (~[$($fmla:tt)*]) => {
        $crate::formula!(@not ($($fmla)*))
    };
    (~{$($fmla:tt)*}) => {
        $crate::formula!(@not ($($fmla)*))
    };
    // Conjunction
    (($($left:tt)*) & ($($right:tt)*)) => {
        formula!(@and ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] & [$($right:tt)*]) => {
        formula!(@and ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} & {$($right:tt)*}) => {
        formula!(@and ($($left)*) ($($right)*))
    };
    //Disjunction
    (($($left:tt)*) | ($($right:tt)*)) => {
        formula!(@or ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] | [$($right:tt)*]) => {
        formula!(@or ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} | {$($right:tt)*}) => {
        formula!(@or ($($left)*) ($($right)*))
    };
    // Implication
    (($($left:tt)*) -> ($($right:tt)*)) => {
        formula!(@implies ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] -> [$($right:tt)*]) => {
        formula!(@implies ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} -> {$($right:tt)*}) => {
        formula!(@implies ($($left)*) ($($right)*))
    };
    // Bi-implication
    (($($left:tt)*) <=> ($($right:tt)*)) => {
        formula!(@iff ($($left)*) ($($right)*))
    };
    ([$($left:tt)*] <=> [$($right:tt)*]) => {
        formula!(@iff ($($left)*) ($($right)*))
    };
    ({$($left:tt)*} <=> {$($right:tt)*}) => {
        formula!(@iff ($($left)*) ($($right)*))
    };
    // Universally Quantified
    (! $($v:ident),+ . ($($fmla:tt)*)) => {
        formula!(@forall ($($v),+) ($($fmla)*))
    };
    (! $($v:ident),+ . [$($fmla:tt)*]) => {
        formula!(@forall ($($v),+) ($($fmla)*))
    };
    (! $($v:ident),+ . {$($fmla:tt)*}) => {
        formula!(@forall ($($v),+) ($($fmla)*))
    };
    // Existentially Quantified
    (? $($v:ident),+ . ($($fmla:tt)*)) => {
        formula!(@exists ($($v),+) ($($fmla)*))
    };
    (? $($v:ident),+ . [$($fmla:tt)*]) => {
        formula!(@exists ($($v),+) ($($fmla)*))
    };
    (? $($v:ident),+ . {$($fmla:tt)*}) => {
        formula!(@exists ($($v),+) ($($fmla)*))
    };
    // Construction rules
    (@equals ($($left:tt)*) ($($right:tt)*)) => {
        {
            let left = $crate::term!($($left)*);
            let right = $crate::term!($($right)*);
            $crate::syntax::Formula::Equals {left, right}
        }
    };
    (@not ($($fmla:tt)*)) => {
        $crate::syntax::Formula::Not{
            formula: Box::new(formula!($($fmla)*)),
        }
    };
    (@and ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::Formula::And{
            left: Box::new(formula!($($left)*)),
            right: Box::new(formula!($($right)*)),
        }
    };
    (@or ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::Formula::Or{
            left: Box::new(formula!($($left)*)),
            right: Box::new(formula!($($right)*)),
        }
    };
    (@implies ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::Formula::Implies{
            left: Box::new(formula!($($left)*)),
            right: Box::new(formula!($($right)*)),
        }
    };
    (@iff ($($left:tt)*) ($($right:tt)*)) => {
        $crate::syntax::Formula::Iff{
            left: Box::new(formula!($($left)*)),
            right: Box::new(formula!($($right)*)),
        }
    };
    (@forall ($($v:ident),+) ($($fmla:tt)*)) => {
        {
            let vs = vec![$($crate::syntax::V(stringify!($v).to_string()),)+];
            $crate::syntax::Formula::Forall{
                variables: vs,
                formula: Box::new(formula!($($fmla)*)),
            }
        }
    };
    (@exists ($($v:ident),+) ($($fmla:tt)*)) => {
        {
            let vs = vec![$($crate::syntax::V(stringify!($v).to_string()),)+];
            $crate::syntax::Formula::Exists{
                variables: vs,
                formula: Box::new(formula!($($fmla)*)),
            }
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_macro() {
        assert_eq!("⊤", formula!('|').to_string());
        assert_eq!("⟘", formula!(_|_).to_string());

        assert_eq!("P()", formula!(P()).to_string());
        assert_eq!("P(x)", formula!(P(x)).to_string());
        assert_eq!("P(x, 'c)", formula!(P(x, @c)).to_string());
        assert_eq!("P(x, 'c, y, 'd)", formula!(P(x, @c, y, @d)).to_string());
        assert_eq!("P(f(x))", formula!(P(f(x))).to_string());
        assert_eq!(
            "P(g(z), f(x, g(y)))",
            formula!(P(g(z), f(x, g(y)))).to_string()
        );

        assert_eq!("x = y", formula!((x) = (y)).to_string());
        assert_eq!("'c = y", formula!((@c) = (y)).to_string());
        assert_eq!(
            "h() = f(x, g(y, 'c))",
            formula!((h()) = (f(x, g(y, @c)))).to_string()
        );
        assert_eq!("x = y", formula!([x] = [y]).to_string());
        assert_eq!("x = y", formula!({ x } = { y }).to_string());

        assert_eq!("¬P(x, 'c)", formula!(~(P(x, @c))).to_string());
        assert_eq!("¬P(x, 'c)", formula!(~[P(x, @c)]).to_string());
        assert_eq!("¬P(x, 'c)", formula!(~{P(x, @c)}).to_string());

        assert_eq!("P(x, 'c) ∧ ⊤", formula!((P(x, @c)) & ('|')).to_string());
        assert_eq!("P(x, 'c) ∧ ⟘", formula!((P(x, @c)) & (_|_)).to_string());

        assert_eq!("P(x, 'c) ∧ Q(z)", formula!((P(x, @c)) & (Q(z))).to_string());
        assert_eq!("P(x, 'c) ∧ Q(z)", formula!([P(x, @c)] & [Q(z)]).to_string());
        assert_eq!("P(x, 'c) ∧ Q(z)", formula!({P(x, @c)} & {Q(z)}).to_string());

        assert_eq!("P(x, 'c) ∨ Q(z)", formula!((P(x, @c)) | (Q(z))).to_string());
        assert_eq!("P(x, 'c) ∨ Q(z)", formula!([P(x, @c)] | [Q(z)]).to_string());
        assert_eq!("P(x, 'c) ∨ Q(z)", formula!({P(x, @c)} | {Q(z)}).to_string());

        assert_eq!(
            "P(x, 'c) → Q(z)",
            formula!((P(x, @c)) -> (Q(z))).to_string()
        );
        assert_eq!(
            "P(x, 'c) → Q(z)",
            formula!([P(x, @c)] -> [Q(z)]).to_string()
        );
        assert_eq!(
            "P(x, 'c) → Q(z)",
            formula!({P(x, @c)} -> {Q(z)}).to_string()
        );

        assert_eq!(
            "P(x, 'c) ⇔ Q(z)",
            formula!((P(x, @c)) <=> (Q(z))).to_string()
        );
        assert_eq!(
            "P(x, 'c) ⇔ Q(z)",
            formula!([P(x, @c)] <=> [Q(z)]).to_string()
        );
        assert_eq!(
            "P(x, 'c) ⇔ Q(z)",
            formula!({P(x, @c)} <=> {Q(z)}).to_string()
        );

        assert_eq!("∀ x. P(x, \'c)", formula!(!x . (P(x, @c))).to_string());
        assert_eq!("∀ x. P(x, \'c)", formula!(!x . [P(x, @c)]).to_string());
        assert_eq!("∀ x. P(x, \'c)", formula!(!x . {P(x, @c)}).to_string());
        assert_eq!(
            "∀ x, y. P(x, \'c)",
            formula!(!x, y . (P(x, @c))).to_string()
        );

        assert_eq!("∃ x. P(x, \'c)", formula!(?x . (P(x, @c))).to_string());
        assert_eq!("∃ x. P(x, \'c)", formula!(?x . [P(x, @c)]).to_string());
        assert_eq!("∃ x. P(x, \'c)", formula!(?x . {P(x, @c)}).to_string());
        assert_eq!(
            "∃ x, y. P(x, \'c)",
            formula!(?x, y . (P(x, @c))).to_string()
        );
    }
}