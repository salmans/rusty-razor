use super::syntax::{*, Formula::*};
use nom::{*, types::CompleteStr};
use nom_locate::LocatedSpan;
use std::fmt as fmt;
use failure::{Fail, Error};

const LOWER: &str = "abcdefghijklmnopqrstuvwxyz_";
const UPPER: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
const ALPHA_NUMERIC: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
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

// Custom parsing errors:
const ERR_DOT: u32 = 1;
const ERR_SEMI_COLON: u32 = 2;
const ERR_L_PAREN: u32 = 3;
const ERR_R_PAREN: u32 = 4;

const ERR_LOWER: u32 = 21;

const ERR_VARS: u32 = 31;
const ERR_TERM: u32 = 32;

const ERR_EQUALS: u32 = 41;
const ERR_FORMULA: u32 = 42;

fn error_code_to_string(code: &u32) -> &'static str {
    match code {
        &ERR_DOT => ".",
        &ERR_SEMI_COLON => ";",
        &ERR_L_PAREN => "(",
        &ERR_R_PAREN => ")",
        &ERR_LOWER => "lowercase identifier",
        &ERR_VARS => "variables",
        &ERR_TERM => "term",
        &ERR_EQUALS => "=",
        &ERR_FORMULA => "formula",
        _ => "unknown",
    }
}

#[derive(Fail)]
pub enum ParserError {
    Missing {
        line: u32,
        column: u32,
        code: u32,
    },
    Expecting {
        line: u32,
        column: u32,
        code: u32,
        found: Option<String>,
    },
    Failed {
        line: u32,
        column: u32,
    },
    Unknown,
}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            ParserError::Missing { line, column, code } => {
                write!(f, "missing '{}' at line {}, column {}", error_code_to_string(code), line, column)
            }
            ParserError::Expecting { line, column, code, found } => {
                if let Some(found) = found {
                    write!(f, "expecting '{}' on line {}, column {}; found \"{}\"", error_code_to_string(code), line, column, found)
                } else {
                    write!(f, "expecting '{}' on line {}, column {}", error_code_to_string(code), line, column)
                }
            }
            ParserError::Failed { line, column} => {
                write!(f, "failed to parse the input at line {}, column {}", line, column)
            }
            ParserError::Unknown => {
                write!(f, "an error occurred while parsing the input")
            }
        }
    }
}

impl fmt::Debug for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self, f)
    }
}

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

named!(
    lower_ident<Span, String>,
    map!(
        pair!(one_of!(LOWER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<Span>)| {
            if rest.is_some() {
                let mut result = first.to_string();
                result.push_str(rest.unwrap().fragment.0);
                result
            } else {
                first.to_string()
            }
        }
    )
);

named!(
    upper_ident<Span, String>,
    map!(
        pair!(one_of!(UPPER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<Span>)| {
            if rest.is_some() {
                let mut result = first.to_string();
                result.push_str(rest.unwrap().fragment.0);
                result
            } else {
                first.to_string()
            }
        }
    )
);

named!(
    var<Span, V>,
    map!(
        lower_ident,
        |v| V::new(&v)
    )
);

named!(
    vars<Span, Vec<V>>,
    terminated!(
        separated_nonempty_list!(
            tag!(COMMA),
            ws!(var)
        ),
        opt!(ws!(tag!(COMMA)))
    )
);

named!(
    r#const<Span, C>,
    map!(
        preceded!(
            tag!(APOSTROPHE),
            return_error!(ErrorKind::Custom(ERR_LOWER), lower_ident)
        ),
        |c| C::new(&c)
    )
);

named!(
    func<Span, Func>,
    map!(
        lower_ident,
        |f| Func::new(&f)
    )
);

named!(
    nonempty_terms<Span, Terms>,
    terminated!(
        separated_nonempty_list!(
            ws!(tag!(COMMA)),
            return_error!(ErrorKind::Custom(ERR_TERM), term)
        ),
        opt!(ws!(tag!(COMMA)))
    )
);

named!(
    term_args<Span, Terms>,
    alt!(
        value!(vec![], pair!(ws!(tag!(L_PAREN)), tag!(R_PAREN)))
        | delimited!(
            ws!(tag!(L_PAREN)),
            nonempty_terms,
            return_error!(ErrorKind::Custom(ERR_R_PAREN), ws!(tag!(R_PAREN)))
        )
    )
);

named!(
    term<Span, Term>,
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
            pair!(func, term_args),
            |(f, ts): (Func, Terms)| f.app(ts)
        )
    )
);

named!(
    equals<Span, Formula>,
    do_parse!(
        left: ws!(term) >>
        tag!(EQUALS) >>
        right: add_return_error!(ErrorKind::Custom(ERR_TERM), ws!(term)) >>
        (Equals { left, right })
    )
);

named!(
    pred<Span, Pred>,
    map!(
        upper_ident,
        |f| Pred::new(&f)
    )
);

named!(
    atom<Span, Formula>,
    alt!(
        value!(Top, alt!(tag!(TRUE) |  tag!(TOP)))
        | value!(Bottom, alt!(tag!(FALSE) |  tag!(BOTTOM)))
        | add_return_error!(ErrorKind::Custom(ERR_EQUALS), equals)
        | map!( // complex term
            pair!(pred, term_args),
            |(p, ts): (Pred, Terms)| p.app(ts)
        ) |
        delimited!(
            ws!(tag!(L_PAREN)),
            return_error!(ErrorKind::Custom(ERR_FORMULA), formula),
            return_error!(ErrorKind::Custom(ERR_R_PAREN), ws!(tag!(R_PAREN)))
        )
    )
);

named!(
    not<Span, Formula>,
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
    and<Span, Formula>,
    map!(
        pair!(
            not,
            opt!(
                preceded!(
                    ws!(alt!(tag!(AND) | tag!(AMPERSAND) | tag!(WEDGE))),
                    alt!(
                        and | return_error!(ErrorKind::Custom(ERR_FORMULA), quantified)
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
    or<Span, Formula>,
    map!(
        pair!(
            and,
            opt!(
                preceded!(
                    ws!(alt!(tag!(OR) | tag!(BAR) | tag!(VEE))),
                    return_error!(ErrorKind::Custom(ERR_FORMULA), quantified)
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
    quantified<Span, Formula>,
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
            vs: return_error!(ErrorKind::Custom(ERR_VARS), vars) >>
            return_error!(ErrorKind::Custom(ERR_DOT), ws!(tag!(DOT))) >>
            f: return_error!(ErrorKind::Custom(ERR_FORMULA), quantified) >>
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
    pub formula<Span, Formula>,
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
                return_error!(ErrorKind::Custom(ERR_FORMULA), quantified)
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

named!(pub spaces<Span, Span>, eat_separator!(&b" \t"[..]));

#[macro_export]
macro_rules! sp (
    ($i: expr, $($args:tt)*) => (
        {
            sep!($i, spaces, $($args)*)
        }
    )
);

named!(
    pub comment<Span, ()>,
    value!(
        (),
        delimited!(
            sp!(tag!(LINE_COMMENT)),
            many0!(nom::not_line_ending),
            nom::line_ending
        )
    )
);

named!(
    pub last_line_comment<Span, ()>,
    value!(
        (),
        delimited!(
            sp!(tag!(LINE_COMMENT)),
            many0!(nom::not_line_ending),
            eof!()
        )
    )
);

named!(
    pub theory<Span, Theory>,
    map!(
        many_till!(
            alt!(
                value!(
                    Option::None,
                    many1!(comment)
                ) |
                map!(
                    terminated!(
                        formula,
                        return_error!(ErrorKind::Custom(ERR_SEMI_COLON),
                            ws!(tag!(SEMI_COLON))
                        )
                    ),
                    |f| Option::Some(f)
                )
            ),
            alt!(
                last_line_comment |
                value!((), eof!())
            )
        ),
        |(fs, _)| Theory::new(fs.into_iter().filter(|f| f.is_some()).map(|f| f.unwrap()).collect())
    )
);

pub fn parse_formula(string: &str) -> Formula {
    formula(Span::new(CompleteStr(string))).ok().unwrap().1
}

pub fn parse_theory_unsafe(string: &str) -> Theory {
    theory(Span::new(CompleteStr(string))).ok().unwrap().1
}

pub fn parse_theory(string: &str) -> Result<Theory, Error> {
    theory(Span::new(CompleteStr(string)))
        .map(|r| r.1)
        .map_err(|e| make_parser_error(&e).into())
}

fn make_parser_error(error: &Err<Span, u32>) -> ParserError {
    match error {
        Err::Error(Context::Code(pos, ErrorKind::Custom(code))) | Err::Failure(Context::Code(pos, ErrorKind::Custom(code))) => {
            let found = if pos.fragment.len() != 0 {
                Some(pos.fragment.0.to_string())
            } else {
                None
            };
            let code = *code;
            match code {
                ERR_SEMI_COLON | ERR_DOT | ERR_L_PAREN | ERR_R_PAREN => ParserError::Missing { line: pos.line, column: pos.get_column() as u32, code },
                ERR_FORMULA | ERR_TERM | ERR_VARS | ERR_LOWER => ParserError::Expecting { line: pos.line, column: pos.get_column() as u32, code, found },
                _ => ParserError::Failed { line: pos.line, column: pos.get_column() as u32 },
            }
        },
        Err::Error(Context::Code(pos, _)) | Err::Failure(Context::Code(pos, _)) => {
            ParserError::Failed { line: pos.line, column: pos.get_column() as u32 }
        },
        _ => ParserError::Unknown,
    }
}

#[cfg(test)]
mod test_parser {
    use super::*;
    use std::fmt;
    use crate::test_prelude::*;

    fn success<R: PartialEq + fmt::Debug>(
        parser: fn(Span) -> nom::IResult<Span, R, u32>,
        parse_str: &str,
        expected: R,
        remaining: &str) {
        let parsed = parser(Span::new(CompleteStr(parse_str)));
        assert!(parsed.is_ok());
        let (rem, res) = parsed.unwrap();
        assert_eq!(expected, res);
        assert_eq!(CompleteStr(remaining), rem.fragment);
    }

    fn success_to_string<R: ToString>(
        parser: fn(Span) -> nom::IResult<Span, R, u32>,
        parse_str: &str,
        expected: &str,
        remaining: &str) {
        let parsed = parser(Span::new(CompleteStr(parse_str)));
        assert!(parsed.is_ok());
        let (str, result) = parsed.unwrap();
        assert_eq!(expected, result.to_string());
        assert_eq!(remaining, str.fragment.0);
    }

    fn fail<R: PartialEq + fmt::Debug>(
        parser: fn(Span) -> nom::IResult<Span, R, u32>,
        parse_str: &str) {
        let result = parser(Span::new(CompleteStr(parse_str)));
        assert!(result.is_err());
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
        success_to_string(formula, "( TRUE)", "⊤", "");
        success_to_string(formula, "(TRUE )", "⊤", "");
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

    #[test]
    fn parse_failure() {
        assert_eq!("expecting 'term' on line 1, column 3; found \"X)\"", parse_theory("P(X)").err().unwrap().to_string());
        assert_eq!("expecting 'term' on line 1, column 3; found \"'A)\"", parse_theory("P('A)").err().unwrap().to_string());
        assert_eq!("missing ';' at line 1, column 5", parse_theory("P(x)").err().unwrap().to_string());
        assert_eq!("missing ')' at line 1, column 4", parse_theory("P(x").err().unwrap().to_string());
        assert_eq!("missing ')' at line 1, column 5", parse_theory("~P(x").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 10", parse_theory("P(x) and ").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 10; found \"X\"", parse_theory("P(x) and X").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 8", parse_theory("P(x) or").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 9; found \"X\"", parse_theory("P(x) or X").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 8", parse_theory("P(x) ->").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 9; found \"X\"", parse_theory("P(x) -> X").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 9", parse_theory("P(x) <=>").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 10; found \"X\"", parse_theory("P(x) <=> X").err().unwrap().to_string());
        assert_eq!("missing '.' at line 1, column 4", parse_theory("!x P(x").err().unwrap().to_string());
        assert_eq!("expecting 'variables' on line 1, column 3; found \"P(x)\"", parse_theory("! P(x)").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 6", parse_theory("!x . ").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 6; found \"X\"", parse_theory("!x . X").err().unwrap().to_string());
        assert_eq!("missing '.' at line 1, column 4", parse_theory("?x P(x").err().unwrap().to_string());
        assert_eq!("expecting 'variables' on line 1, column 3; found \"P(x)\"", parse_theory("? P(x)").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 6", parse_theory("?x . ").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 6; found \"X\"", parse_theory("?x . X").err().unwrap().to_string());
        assert_eq!("failed to parse the input at line 1, column 1", parse_theory("x").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 1, column 2; found \"X)\"", parse_theory("(X)").err().unwrap().to_string());
        assert_eq!("missing ')' at line 1, column 6", parse_theory("(P(x)").err().unwrap().to_string());
        assert_eq!("missing ';' at line 2, column 1", parse_theory("P(x)\n\
        Q(x) <=> R(x);").err().unwrap().to_string());
        assert_eq!("missing ';' at line 3, column 6", parse_theory("P(x);\n\
        Q(x) <=> R(x);\n\
        S(x) => Q(x);").err().unwrap().to_string());
        assert_eq!("expecting 'formula' on line 3, column 10", parse_theory("P(x);\n\
        Q(x) <=> R(x);\n\
        S(x) and ").err().unwrap().to_string());
    }
}


