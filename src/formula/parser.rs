use super::syntax::{*, Formula::*};
use nom::{*, types::CompleteStr};

const LOWER: &str = "abcdefghijklmnopqrstuvwxyz_";
const UPPER: &str = "ABCDEFGIJKLMNOPQRSTUVWXYZ";
const ALPHA_NUMERIC: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGIJKLMNOPQRSTUVWXYZ0123456789_";
const COMMA: &str = ",";
const APOSTROPHE: &str = "'";
const L_PAREN: &str = "(";
const R_PAREN: &str = ")";
const TRUE: &str = "TRUE";
const TOP: &str = "⊤";
const FALSE: &str = "FALSE";
const BOTTOM: &str = "⟘";
const EQUALS: &str = "=";
const AND: &str = "and";
const AMPERSAND: &str = "&";
const WEDGE: &str = "∧";
const OR: &str = "or";
const BAR: &str = "|";
const VEE: &str = "∨";
const NOT: &str = "not";
const TILDE: &str = "~";
const NEG: &str = "¬";
const IMPLIES: &str = "implies";
const CHAR_RIGHT_ARROW: &str = "->";
const RIGHT_ARROW: &str = "→";
const IFF: &str = "iff";
const CHAR_DOUBLE_ARROW: &str = "<=>";
const DOUBLE_ARROW: &str = "⇔";
const EXISTS: &str = "exists";
const QUESTION: &str = "?";
const CHAR_EXISTS: &str = "∃";
const FORALL: &str = "forall";
const EXCLAMATION: &str = "!";
const CHAR_FORALL: &str = "∀";
const DOT: &str = ".";
const SEMI_COLON: &str = ";";
const LINE_COMMENT: &str = "//";

named!(
    lower_ident<CompleteStr, String>,
    map!(
        pair!(one_of!(LOWER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<CompleteStr>)| {
            if rest.is_some() {
                let mut result = first.to_string();
                result.push_str(rest.unwrap().0);
                result
            } else {
                first.to_string()
            }
        }
    )
);

named!(
    upper_ident<CompleteStr, String>,
    map!(
        pair!(one_of!(UPPER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<CompleteStr>)| {
            if rest.is_some() {
                let mut result = first.to_string();
                result.push_str(rest.unwrap().0);
                result
            } else {
                first.to_string()
            }
        }
    )
);

named!(
    var<CompleteStr, V>,
    map!(
        lower_ident,
        |v| V::new(&v)
    )
);

named!(
    vars<CompleteStr, Vec<V>>,
    terminated!(
        separated_nonempty_list!(
            tag!(COMMA),
            ws!(var)
        ),
        opt!(ws!(tag!(COMMA)))
    )
);

named!(
    r#const<CompleteStr, C>,
    map!(
        preceded!(
            tag!(APOSTROPHE),
            lower_ident
        ),
        |c| C::new(&c)
    )
);

named!(
    func<CompleteStr, Func>,
    map!(
        lower_ident,
        |f| Func::new(&f)
    )
);

named!(
    terms<CompleteStr, Terms>,
    terminated!(
        separated_list!(
            ws!(tag!(COMMA)),
            term
        ),
        opt!(ws!(tag!(COMMA)))
    )
);

named!(
    term<CompleteStr, Term>,
    alt!(
        map!(  // variable
            terminated!(
                var,
                not!(   // The term is a complex term if followed by '('.
                        // Another way to deal with it is to look for a complex term first.
                    ws!(tag!(L_PAREN))
                )
            ),
            |v| v.into()
        ) | map!(  // constant
            r#const,
            |c| c.into()
        ) | map!( // complex term
            pair!(
                func,
                ws!(
                    delimited!(
                        tag!(L_PAREN),
                        terms,
                        tag!(R_PAREN)
                    )
                )
            ),
            |(f, ts): (Func, Terms)| f.app(ts)
        )
    )
);

named!(
    equals<CompleteStr, Formula>,
    do_parse!(
        left: ws!(term) >>
        tag!(EQUALS) >>
        right: ws!(term) >>
        (Equals { left, right })
    )
);

named!(
    pred<CompleteStr, Pred>,
    map!(
        upper_ident,
        |f| Pred::new(&f)
    )
);

named!(
    atom<CompleteStr, Formula>,
    alt!(
        value!(Top, alt!(tag!(TRUE) |  tag!(TOP)))
        | value!(Bottom, alt!(tag!(FALSE) |  tag!(BOTTOM)))
        | equals
        | map!( // complex term
            pair!(
                pred,
                ws!(
                    delimited!(
                        tag!(L_PAREN),
                        terms,
                        tag!(R_PAREN)
                    )
                )
            ),
            |(p, ts): (Pred, Terms)| p.app(ts)
        ) |
        delimited!(tag!(L_PAREN), formula, tag!(R_PAREN))
    )
);

named!(
    not<CompleteStr, Formula>,
    alt!(
        preceded!(
            ws!(alt!(tag!(NOT) | tag!(TILDE) | tag!(NEG))),
            map!(
                alt!(not | quantified),
                |f| Not { formula: Box::new(f) }
            )
        ) | atom
    )
);

named!(
    and<CompleteStr, Formula>,
    map!(
        pair!(
            not,
            opt!(
                preceded!(
                    ws!(alt!(tag!(AND) | tag!(AMPERSAND) | tag!(WEDGE))),
                    alt!(
                        and | quantified
                    )
                )
            )
        ),
        |(l, r)| {
            if r.is_some() {
                And { left: Box::new(l), right: Box::new(r.unwrap()) }
            } else {
                l
            }
        }
    )
);

named!(
    or<CompleteStr, Formula>,
    map!(
        pair!(
            and,
            opt!(
                preceded!(
                    ws!(alt!(tag!(OR) | tag!(BAR) | tag!(VEE))),
                    quantified
                )
            )
        ),
        |(l, r)| {
            if r.is_some() {
                Or { left: Box::new(l), right: Box::new(r.unwrap()) }
            } else {
                l
            }
        }
    )
);


named!(
    quantified<CompleteStr, Formula>,
    alt!(
        do_parse!(
            q: ws!(
                alt!(
                    value!(
                        FORALL,
                        alt!(tag!(FORALL) | tag!(EXCLAMATION) | tag!(CHAR_FORALL))
                    ) | value!(
                        EXISTS,
                        alt!(tag!(EXISTS) | tag!(QUESTION) | tag!(CHAR_EXISTS))
                    )
                )
            ) >>
            vs: vars >>
            ws!(tag!(DOT)) >>
            f: quantified >>
            (
                if q == FORALL {
                    Forall { variables: vs, formula: Box::new(f) }
                } else {
                    Exists { variables: vs, formula: Box::new(f) }
                }
            )
        ) |
        or
    )
);

named!(
    pub formula<CompleteStr, Formula>,
    do_parse!(
        first: quantified >>
        second: fold_many0!(
            pair!(
                ws!(
                    alt!(
                        value!(
                            IMPLIES,
                            alt!(tag!(IMPLIES) | tag!(RIGHT_ARROW) | tag!(CHAR_RIGHT_ARROW))
                        ) | value!(
                            IFF,
                            alt!(tag!(IFF) | tag!(DOUBLE_ARROW) | tag!(CHAR_DOUBLE_ARROW))
                        )
                    )
                ),
                quantified
            ),
            first,
            |acc, (q, f)| {
                if q == IMPLIES {
                    Implies { left: Box::new(acc), right: Box::new(f) }
                } else {
                    Iff { left: Box::new(acc), right: Box::new(f) }
                }
            }
        ) >>
        (second)
    )
);

named!(pub spaces<CompleteStr, CompleteStr>, eat_separator!(&b" \t"[..]));

#[macro_export]
macro_rules! sp (
    ($i: expr, $($args:tt)*) => (
        {
            sep!($i, spaces, $($args)*)
        }
    )
);

named!(
    pub comment<CompleteStr, ()>,
    value!(
        (),
        delimited!(
            sp!(tag!(LINE_COMMENT)),
            many0!(nom::not_line_ending),
            nom::line_ending
        )
    )
);

//named!(
//    pub theory<CompleteStr, Theory>,
//    map!(
//        many0!(
//            terminated!(
//                formula,
//                ws!(tag!(SEMI_COLON))
//            )
//        ),
//        Theory::new
//    )
//);

named!(
    pub theory<CompleteStr, Theory>,
    map!(
        many0!(
            do_parse!(
                many0!(comment) >>
                formula: terminated!(
                    formula,
                    ws!(tag!(SEMI_COLON))
                ) >>
                (formula)
            )
        ),
        Theory::new
    )
);

pub fn parse_formula(string: &str) -> Formula {
    formula(CompleteStr(string)).ok().unwrap().1
}

pub fn parse_theory(string: &str) -> Theory {
    theory(CompleteStr(string)).ok().unwrap().1
}

#[cfg(test)]
mod test_parser {
    use super::*;
    use std::fmt;
    use crate::test_prelude::*;

    fn success<R: PartialEq + fmt::Debug>(
        parser: fn(CompleteStr) -> nom::IResult<CompleteStr, R, u32>,
        parse_str: &str,
        expected: R,
        remaining: &str) {
        let parsed = parser(CompleteStr(parse_str));
        assert!(parsed.is_ok());
        let (rem, res) = parsed.unwrap();
        assert_eq!(expected, res);
        assert_eq!(CompleteStr(remaining), rem);
    }

    fn success_to_string<R: ToString>(
        parser: fn(CompleteStr) -> nom::IResult<CompleteStr, R, u32>,
        parse_str: &str,
        expected: &str,
        remaining: &str) {
        let parsed = parser(CompleteStr(parse_str));
        assert!(parsed.is_ok());
        let (str, result) = parsed.unwrap();
        assert_eq!(expected, result.to_string());
        assert_eq!(remaining, str.0);
    }

    fn fail<R: PartialEq + fmt::Debug>(
        parser: fn(CompleteStr) -> nom::IResult<CompleteStr, R, u32>,
        parse_str: &str) {
        assert!(parser(CompleteStr(parse_str)).is_err());
    }

    #[test]
    fn test_lower_identifier() {
        success(lower_ident, "_", "_".to_string(), "");
        success(lower_ident, "a", "a".to_string(), "");
        success(lower_ident, "_ab", "_ab".to_string(), "");
        success(lower_ident, "aB", "aB".to_string(), "");
        success(lower_ident, "aB!", "aB".to_string(), "!");
        success(lower_ident, "johnSn0w", "johnSn0w".to_string(), "");

        fail(lower_ident, "B");
        fail(lower_ident, "Blah");
        fail(lower_ident, "!ABC");
        fail(lower_ident, "123");
    }

    #[test]
    fn test_upper_identifier() {
        success(upper_ident, "A", "A".to_string(), "");
        success(upper_ident, "AB", "AB".to_string(), "");
        success(upper_ident, "AB!", "AB".to_string(), "!");
        success(upper_ident, "JohnSn0w", "JohnSn0w".to_string(), "");

        fail(upper_ident, "b");
        fail(upper_ident, "blah");
        fail(upper_ident, "!ABC");
        fail(upper_ident, "123");
        fail(upper_ident, "_");
        fail(upper_ident, "_AB");
    }

    #[test]
    fn test_var() {
        success(var, "x", _x(), "");

        fail(var, "  x");
        fail(var, "'a");
        fail(var, "B");
    }

    #[test]
    fn test_vars() {
        success(vars, "x", vec![_x()], "");
        success(vars, "x,y", vec![_x(), _y()], "");
        success(vars, "  x", vec![_x()], "");
        success(vars, "x, y", vec![_x(), _y()], "");
        success(vars, "x, y\t,\nz", vec![_x(), _y(), _z()], "");
        success(vars, "x,", vec![_x()], "");
        success(vars, "x,y   ,   ", vec![_x(), _y()], "");

        fail(vars, ",x");
        fail(vars, "B");
    }

    #[test]
    fn test_const() {
        success(r#const, "'a", _a(), "");
        fail(r#const, "x");
        fail(r#const, "   'a");
        fail(r#const, "'  a");
        fail(r#const, "''a");
        fail(r#const, "B");
    }

    #[test]
    fn test_func() {
        success(func, "f", f(), "");
        fail(func, "  f");
        fail(func, "'a");
        fail(func, "'B");
        fail(func, "B");
    }

    #[test]
    fn test_term() {
        success(term, "x", x(), "");
        success(term, "'a", a(), "");
        success(term, "f()", f().app0(), "");
        success(term, "f( )", f().app0(), "");
        success_to_string(term, "f(x)", "f(x)", "");
        success_to_string(term, "f(x,   y   )", "f(x, y)", "");
        success_to_string(term, "f(x,   y   \n , z)", "f(x, y, z)", "");
        success_to_string(term, "f(f(f(f(f(f(f(x)))))))", "f(f(f(f(f(f(f(x)))))))", "");
        success_to_string(term, "f  (x)", "f(x)", "");
        success_to_string(term, "f  (   x   )   ", "f(x)", "");
        success_to_string(term, "f(w, g (  x, y, z))", "f(w, g(x, y, z))", "");
        success_to_string(term, "f('a, x, g('b, h(x)))", "f('a, x, g('b, h(x)))", "");
        fail(term, "''a");
        fail(term, "P()");
        fail(term, "f(Q())");
        fail(term, "12f(x)");
        fail(term, "f(1, 2)");
        fail(term, "f(x, g(1))");
    }

    #[test]
    fn test_equals() {
        success_to_string(equals, "x = y", "x = y", "");
        success_to_string(equals, "'a = 'b", "'a = 'b", "");
        success_to_string(equals, "f(x) = y", "f(x) = y", "");
        success_to_string(equals, "  f  (x  ) = y", "f(x) = y", "");

        fail(equals, "A = B");
        fail(equals, "!a = b");
        fail(equals, "a != b");
    }

    #[test]
    fn test_pred() {
        success(pred, "P", P(), "");
        fail(pred, "  P");
        fail(pred, "'a");
        fail(pred, "x");
    }

    #[test]
    fn test_comment() {
        success(comment, "//\n", (), "");
        success(comment, "  //\n", (), "");
        success(comment, "// comment line \n", (), "");
        success(comment, "//comment line \n", (), "");
        success(comment, "   //   comment line \n", (), "");
        fail(comment, "//");
        fail(comment, "/");
    }

    #[test]
    fn test_atom() {
        success(atom, TRUE, Top, "");
        success(atom, TOP, Top, "");
        success(atom, FALSE, Bottom, "");
        success(atom, BOTTOM, Bottom, "");
        success_to_string(atom, "x = f('a)", "x = f('a)", "");
        success_to_string(atom, "P()", "P()", "");
        success_to_string(atom, "P( )", "P()", "");
        success_to_string(atom, "P(x)", "P(x)", "");
        success_to_string(atom, "P(x,   y   )", "P(x, y)", "");
        success_to_string(atom, "P(x,   y   \n , z)", "P(x, y, z)", "");
        success_to_string(atom, "P(f(f(f(f(f(f(x)))))))", "P(f(f(f(f(f(f(x)))))))", "");
        success_to_string(atom, "P  (x)", "P(x)", "");
        success_to_string(atom, "P  (   x   )   ", "P(x)", "");
        success_to_string(atom, "P(w, g (  x, y, z))", "P(w, g(x, y, z))", "");
        success_to_string(atom, "P('a, x, g('b, h(x)))", "P('a, x, g('b, h(x)))", "");
        fail(atom, "''a");
        fail(atom, "f()");
        fail(atom, "P(Q())");
        fail(atom, "12P(x)");
        fail(atom, "P(1, 2)");
        fail(atom, "P(x, g(1))");
    }

    #[test]
    fn test_formula() {
        success_to_string(formula, "TRUE", "⊤", "");
        success_to_string(formula, "FALSE", "⟘", "");
        success_to_string(formula, "((((TRUE))))", "⊤", "");
        success_to_string(formula, "P()", "P()", "");
        success_to_string(formula, "P(x)", "P(x)", "");
        success_to_string(formula, "P('a)", "P('a)", "");
        success_to_string(formula, "P(x,y)", "P(x, y)", "");
        success_to_string(formula, "P('a,'b)", "P('a, 'b)", "");
        success_to_string(formula, "P('a,x)", "P('a, x)", "");
        success_to_string(formula, "P(x, y)", "P(x, y)", "");
        success_to_string(formula, "P(x,            y     \n)", "P(x, y)", "");
        success_to_string(formula, "P(f(x))", "P(f(x))", "");
        success_to_string(
            formula,
            "P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(x)))))))))))))))))))))",
            "P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(x)))))))))))))))))))))",
            "",
        );
        success_to_string(formula, "P(f(x, g(y)), g(f(g(y))))", "P(f(x, g(y)), g(f(g(y))))", "");
        success_to_string(formula, "'a = 'b", "'a = 'b", "");
        success_to_string(formula, "x = x", "x = x", "");
        success_to_string(formula, "f() = x", "f() = x", "");
        success_to_string(formula, "f(x) = x", "f(x) = x", "");
        success_to_string(formula, "f(x) = x", "f(x) = x", "");
        success_to_string(formula, "f(x) = g(h(g(f(x)), y))", "f(x) = g(h(g(f(x)), y))", "");
        success_to_string(formula, "P(x) implies Q(x)", "P(x) → Q(x)", "");
        success_to_string(formula, "P(x) implies Q(x) -> R(x)", "(P(x) → Q(x)) → R(x)", "");
        success_to_string(formula, "P(x) implies (Q(x) -> R(x))", "P(x) → (Q(x) → R(x))", "");
        success_to_string(formula, "P(x) implies (Q(x) -> R(x))", "P(x) → (Q(x) → R(x))", "");
        success_to_string(formula, "P(x) implies (Q(x) -> R(x) -> Q(z))", "P(x) → ((Q(x) → R(x)) → Q(z))", "");
        success_to_string(formula, "P(x) iff Q(x)", "P(x) ⇔ Q(x)", "");
        success_to_string(formula, "P(x) iff Q(x) <=> R(x)", "(P(x) ⇔ Q(x)) ⇔ R(x)", "");
        success_to_string(formula, "P(x) iff (Q(x) <=> R(x))", "P(x) ⇔ (Q(x) ⇔ R(x))", "");
        success_to_string(formula, "P(x) iff (Q(x) <=> R(x) <=> Q(z))", "P(x) ⇔ ((Q(x) ⇔ R(x)) ⇔ Q(z))", "");
        success_to_string(formula, "P(x) iff Q(x) implies R(x)", "(P(x) ⇔ Q(x)) → R(x)", "");
        success_to_string(formula, "P(x) implies Q(x) iff R(x)", "(P(x) → Q(x)) ⇔ R(x)", "");
        success_to_string(formula, "exists x . P(x)", "∃ x. P(x)", "");
        success_to_string(formula, "exists x,y . P(x, y)", "∃ x, y. P(x, y)", "");
        success_to_string(formula, "exists x . exists y, z. P(x, y, z)", "∃ x. (∃ y, z. P(x, y, z))", "");
        success_to_string(formula, "exists x . P(x) implies Q(x)", "(∃ x. P(x)) → Q(x)", "");
        success_to_string(formula, "exists x . (P(x) implies Q(x))", "∃ x. (P(x) → Q(x))", "");
        success_to_string(formula, "forall x . P(x)", "∀ x. P(x)", "");
        success_to_string(formula, "forall x,y . P(x, y)", "∀ x, y. P(x, y)", "");
        success_to_string(formula, "forall x . forall y, z. P(x, y, z)", "∀ x. (∀ y, z. P(x, y, z))", "");
        success_to_string(formula, "forall x . P(x) implies Q(x)", "(∀ x. P(x)) → Q(x)", "");
        success_to_string(formula, "forall x . (P(x) implies Q(x))", "∀ x. (P(x) → Q(x))", "");
        success_to_string(formula, "forall x . exists y . P(x, y)", "∀ x. (∃ y. P(x, y))", "");
        success_to_string(formula, "P(x) or Q(y)", "P(x) ∨ Q(y)", "");
        success_to_string(formula, "P(x) or Q(y) or R(z)", "P(x) ∨ (Q(y) ∨ R(z))", "");
        success_to_string(formula, "(P(x) or Q(y)) or R(z)", "(P(x) ∨ Q(y)) ∨ R(z)", "");
        success_to_string(formula, "P(x) or Q(y) or (R(z) or S(z))", "P(x) ∨ (Q(y) ∨ (R(z) ∨ S(z)))", "");
        success_to_string(formula, "P(x) implies Q(x) or R(x)", "P(x) → (Q(x) ∨ R(x))", "");
        success_to_string(formula, "P(x) or Q(x) implies R(x)", "(P(x) ∨ Q(x)) → R(x)", "");
        success_to_string(formula, "exists x . P(x) or Q(x)", "∃ x. (P(x) ∨ Q(x))", "");
        success_to_string(formula, "P(x) or exists y . Q(y)", "P(x) ∨ (∃ y. Q(y))", "");
        success_to_string(formula, "exists x . P(x) or exists y . Q(y)", "∃ x. (P(x) ∨ (∃ y. Q(y)))", "");
        success_to_string(formula, "P(x) or forall y . Q(y)", "P(x) ∨ (∀ y. Q(y))", "");
        success_to_string(formula, "exists x . P(x) or forall y . Q(y)", "∃ x. (P(x) ∨ (∀ y. Q(y)))", "");
        success_to_string(formula, "P(x) and Q(y) or R(z)", "(P(x) ∧ Q(y)) ∨ R(z)", "");
        success_to_string(formula, "P(x) and (Q(y) or R(z))", "P(x) ∧ (Q(y) ∨ R(z))", "");
        success_to_string(formula, "P(x) or Q(y) and R(z)", "P(x) ∨ (Q(y) ∧ R(z))", "");
        success_to_string(formula, "P(x) and Q(y) and R(z)", "P(x) ∧ (Q(y) ∧ R(z))", "");
        success_to_string(formula, "P(w) and Q(x) and R(y) and S(z)", "P(w) ∧ (Q(x) ∧ (R(y) ∧ S(z)))", "");
        success_to_string(formula, "(P(x) and Q(y)) and R(z)", "(P(x) ∧ Q(y)) ∧ R(z)", "");
        success_to_string(formula, "P(x) and Q(y) implies R(z)", "(P(x) ∧ Q(y)) → R(z)", "");
        success_to_string(formula, "P(x) and exists y . Q(y)", "P(x) ∧ (∃ y. Q(y))", "");
        success_to_string(formula, "exists x . P(x) and exists y . Q(y)", "∃ x. (P(x) ∧ (∃ y. Q(y)))", "");
        success_to_string(formula, "P(x) and forall y . Q(y)", "P(x) ∧ (∀ y. Q(y))", "");
        success_to_string(formula, "exists x . P(x) and forall y . Q(y)", "∃ x. (P(x) ∧ (∀ y. Q(y)))", "");
        success_to_string(formula, "not TRUE", "¬⊤", "");
        success_to_string(formula, "not TRUE -> FALSE", "(¬⊤) → ⟘", "");
        success_to_string(formula, "~x=y", "¬(x = y)", "");
        success_to_string(formula, "TRUE -> not FALSE", "⊤ → (¬⟘)", "");
        success_to_string(formula, "not P(x, y) or Q(z)", "(¬P(x, y)) ∨ Q(z)", "");
        success_to_string(formula, "not P(x, y) and Q(z)", "(¬P(x, y)) ∧ Q(z)", "");
        success_to_string(formula, "not not R(x)", "¬(¬R(x))", "");
        success_to_string(formula, "not not not not not R(x) and S(y)", "(¬(¬(¬(¬(¬R(x)))))) ∧ S(y)", "");
        success_to_string(formula, "not exists y . Q(y)", "¬(∃ y. Q(y))", "");
        success_to_string(formula, "exists x . not exists y . Q(y)", "∃ x. (¬(∃ y. Q(y)))", "");
        success_to_string(
            formula,
            "P(x) implies Q(y) and exists z . f(z) = g(f(z)) or (forall y, z . S(y,z) implies FALSE)",
            "P(x) → (Q(y) ∧ (∃ z. ((f(z) = g(f(z))) ∨ ((∀ y, z. S(y, z)) → ⟘))))",
            "",
        );
        success_to_string(
            formula,
            "not forall x, y . P(x) and Q(y) implies h(z) = z",
            "(¬(∀ x, y. (P(x) ∧ Q(y)))) → (h(z) = z)",
            "",
        );
        success_to_string(
            formula,
            "∀ x. ∃ y. ((x = y) ∧ ¬P(y)) ∨ (Q(x) → R(y))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            formula,
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            formula,
            "! x. ? y. ((x = y) & ~P(y)) | (Q(x) -> R(y))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            formula,
            "! x. (? y. (((x = y) & (~P(y))) | (Q(x) -> R(y))))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
    }

    #[test]
    fn test_theory() {
        success_to_string(
            theory,
            "E(x,x);\
            E(x,y) -> E(y,x) ;\
            E(x,y) & E(y,z) -> E(x,z);",
            "E(x, x)\nE(x, y) → E(y, x)\n(E(x, y) ∧ E(y, z)) → E(x, z)",
            "",
        );
        success_to_string(
            theory,
            "// comment 0\n\
            E(x,x)\
            ;\
            // another comment\n\
            E(x,y) -> E(y,x) ;\
            E(x,y) & E(y,z) -> E(x,z);",
            "E(x, x)\nE(x, y) → E(y, x)\n(E(x, y) ∧ E(y, z)) → E(x, z)",
            "",
        );
    }
}


