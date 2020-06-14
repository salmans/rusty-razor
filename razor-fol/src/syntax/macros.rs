#[macro_export]
macro_rules! v {
    ($v:ident) => {
        $crate::syntax::V::from(stringify!($v))
    };
}

#[macro_export]
macro_rules! f {
    ($f:ident) => {
        $crate::syntax::F::from(stringify!($f))
    };
}

#[macro_export]
macro_rules! c {
    ($c:ident) => {
        $crate::syntax::C::from(stringify!($c))
    };
}

#[macro_export]
macro_rules! pred {
    ($p:ident) => {
        $crate::syntax::Pred::from(stringify!($p))
    };
}

#[macro_export]
macro_rules! term {
    ($v:ident) => {
        $crate::syntax::Term::Var {
            variable: stringify!($v).into(),
        }
    };
    (@$c:ident) => {
        $crate::syntax::Term::Const {
            constant: stringify!($c).into(),
        }
    };
    ($func:ident ($($t:tt)*)) => {
        {
            let ts: Vec<$crate::syntax::Term> = $crate::terms!($($t)*);
            $crate::syntax::F(stringify!($func).to_string()).app(ts)
        }
    };
}

#[macro_export]
macro_rules! terms {
    (@acc () -> ($($result:tt)*)) => {
        vec![$($result)*]
    };
    (@acc ($v:ident $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* $crate::syntax::Term::Var {
            variable: stringify!($v).into(),
        },))
    };
    (@acc (@$c:ident $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* $crate::syntax::Term::Const {
            constant: stringify!($c).into(),
        },))
    };
    (@acc ($func:ident ($($t:tt)*) $(, $($tail:tt)*)?) -> ($($result:tt)*)) => {
        {
            let ts = $crate::terms!($($t)*);
            let term = $crate::syntax::F(stringify!($func).to_string()).app(ts);
            $crate::terms!(@acc ($($($tail)*)?) -> ($($result)* term,))
        }
    };
    ($($tail:tt)*) => {
        $crate::terms!(@acc ($($tail)*) -> ())
    };
}

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
