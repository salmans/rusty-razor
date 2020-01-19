//! Implements a parser for first-order formulae and theories in Razor's syntax.
//!
//! The module provides a parser for first-order formulae by implementing [`FromStr`] for
//! [`Formula`] and [`Theory`]. The parser is often used implicitly through [`str::parse`] method.
//!
//! **Example**:
//! The following example parses a string into a [`Formula`]:
//! ```rust
//! use razor_fol::syntax::Formula;
//!
//! // parse a string into `Formula`:
//! let formula: Formula = "exists x. P(x) & Q(x)".parse().unwrap();
//!
//! assert_eq!("∃ x. (P(x) ∧ Q(x))", formula.to_string());
//! ```
//!
//! Similarly, a [`Theory`] can be parsed from a string:
//! ```rust
//! use razor_fol::syntax::Theory;
//!
//! // parse a string into `Theory` (formulae are separated by `;`)
//! let theory: Theory = r#"
//!    // mathematical notation:
//!    ∀ x. Eq(x, x);
//!    // verbose notation:
//!    forall x, y. (Eq(x, y) implies Eq(y, x));
//!    // compact notation:
//!    ? x, y, z. (Eq(x, y) & Eq(y, z) -> Eq(x, z));
//! "#.parse().unwrap();
//!
//! assert_eq!("∀ x. Eq(x, x)\n\
//! ∀ x, y. (Eq(x, y) → Eq(y, x))\n\
//! ∃ x, y, z. ((Eq(x, y) ∧ Eq(y, z)) → Eq(x, z))", theory.to_string());
//! ```
//!
//! [`Formula`]: ../syntax/enum.formula.html
//! [`Theory`]: ../syntax/struct.theory.html
//! [`FromStr`]: https://doc.rust-lang.org/stable/core/str/trait.FromStr.html
//! [`str::parse`]: https://doc.rust-lang.org/stable/std/primitive.str.html#method.parse
use super::syntax::{*, Formula::*};
use nom::{*, types::CompleteStr};
use nom_locate::LocatedSpan;
use std::fmt as fmt;
use failure::{Fail, Error};
use std::str::FromStr;

const LOWER: &str = "abcdefghijklmnopqrstuvwxyz_";
const UPPER: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
const ALPHA_NUMERIC: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
const COMMA: &str = ",";
const APOSTROPHE: &str = "'";
const L_PAREN: &str = "(";
const R_PAREN: &str = ")";
const TRUE: &str = "true";
const CHAR_TOP: &str = "'|'";
const TOP: &str = "⊤";
const FALSE: &str = "false";
const CHAR_BOTTOM: &str = "_|_";
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
const L_BLOCK_COMMENT: &str = "/*";
const R_BLOCK_COMMENT: &str = "*/";

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

fn error_code_to_string(code: u32) -> &'static str {
    match code {
        ERR_DOT => ".",
        ERR_SEMI_COLON => ";",
        ERR_L_PAREN => "(",
        ERR_R_PAREN => ")",
        ERR_LOWER => "lowercase identifier",
        ERR_VARS => "variables",
        ERR_TERM => "term",
        ERR_EQUALS => "=",
        ERR_FORMULA => "formula",
        _ => "unknown",
    }
}

#[derive(Debug, Fail)]
enum ParserError {
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
                write!(f, "missing '{}' at line {}, column {}", error_code_to_string(*code), line, column)
            }
            ParserError::Expecting { line, column, code, found } => {
                write!(f, "expecting '{}' on line {}, column {}", error_code_to_string(*code), line, column)
                    .and_then(|result| {
                        if let Some(found) = found {
                            write!(f, "; found \"{}\"", found)
                        } else {
                            Ok(result)
                        }
                    })
            }
            ParserError::Failed { line, column } => {
                write!(f, "failed to parse the input at line {}, column {}", line, column)
            }
            ParserError::Unknown => {
                write!(f, "an error occurred while parsing the input")
            }
        }
    }
}

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

named!(pub p_line_comment<Span, ()>,
  map!(
    many1!(
      tuple!(
        nom::space0,
        preceded!(tag!(LINE_COMMENT), many0!(nom::not_line_ending)),
        alt!(nom::line_ending | eof!())
      )
    ),
    |_| ()
  )
);

named!(pub p_block_comment<Span, ()>,
  map!(
    many1!(
      tuple!(
        nom::space0,
        delimited!(
            tag!(L_BLOCK_COMMENT),
            many0!(is_not!(R_BLOCK_COMMENT)),
            tag!(R_BLOCK_COMMENT)
        )
      )
    ),
    |_| ()
  )
);

named!(pub spaces<Span, ()>,
    map!(many0!(alt!(one_of!(&b" \t\n\r"[..]) => { |_|() } | p_line_comment | p_block_comment)), |_| ())
);

#[doc(hidden)]
macro_rules! sp (
  ($i:expr, $($args:tt)*) => (
    {
      use nom::Convert;
      use nom::Err;

      match sep!($i, spaces, $($args)*) {
        Err(e) => Err(e),
        Ok((i1,o))    => {
          match spaces(i1) {
            Err(e) => Err(Err::convert(e)),
            Ok((i2,_))    => Ok((i2, o))
          }
        }
      }
    }
  )
);

named!(p_lower_ident<Span, String>,
    map!(pair!(one_of!(LOWER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<Span>)| {
            let mut first = first.to_string();
            if rest.is_some() {
                first.push_str(rest.unwrap().fragment.0);
            }
            first
        }
    )
);

named!(p_upper_ident<Span, String>,
    map!(pair!(one_of!(UPPER), opt!(is_a!(ALPHA_NUMERIC))),
        |(first, rest): (char, Option<Span>)| {
            let mut first = first.to_string();
            if rest.is_some() {
                first.push_str(rest.unwrap().fragment.0);
            }
            first
        }
    )
);

named!(p_var<Span, V>,
    map!(p_lower_ident, |v| V::from(&v))
);

named!(p_vars<Span, Vec<V>>,
    terminated!(
        separated_nonempty_list!(
            tag!(COMMA),
            sp!(p_var)
        ),
        opt!(sp!(tag!(COMMA)))
    )
);

named!(p_const<Span, C>,
    map!(
        preceded!(
            tag!(APOSTROPHE),
            return_error!(ErrorKind::Custom(ERR_LOWER), p_lower_ident)
        ),
        |c| C::from(&c)
    )
);

named!(p_func<Span, F>,
    map!(p_lower_ident,
        |f| F::from(&f)
    )
);

named!(p_nonempty_terms<Span, Vec<Term>>,
    terminated!(
        separated_nonempty_list!(
            tag!(COMMA),
            return_error!(ErrorKind::Custom(ERR_TERM), p_term)
        ),
        opt!(sp!(tag!(COMMA)))
    )
);

named!(p_term_args<Span, Vec<Term>>,
    alt!(
        value!(vec![], delimited!(tag!(L_PAREN), opt!(space),tag!(R_PAREN))) |
        delimited!(
            tag!(L_PAREN),
            p_nonempty_terms,
            return_error!(ErrorKind::Custom(ERR_R_PAREN), tag!(R_PAREN))
        )
    )
);

named!(p_term<Span, Term>,
    alt!(
        map!(
            terminated!(
                sp!(p_var),
                // The term is a composite term if followed by '(':
                not!(tag!(L_PAREN))
            ),
            |v| v.into()
        ) |
        map!(sp!(p_const), |c| c.into()) |
        map!( // composite term
            pair!(sp!(p_func), sp!(p_term_args)),
            |(f, ts): (F, Vec<Term>)| f.app(ts)
        )
    )
);

named!(p_equals<Span, Formula>,
    do_parse!(left: p_term >>
        tag!(EQUALS) >>
        right: add_return_error!(ErrorKind::Custom(ERR_TERM), p_term) >>
        (left.equals(right))
    )
);

named!(p_pred<Span, Pred>,
    map!(p_upper_ident,
        |f| Pred::from(&f)
    )
);

named!(p_atom<Span, Formula>,
    alt!(
        value!(Top, alt!(tag!(TRUE) |  tag!(TOP) | tag!(CHAR_TOP))) |
        value!(Bottom, alt!(tag!(FALSE) |  tag!(BOTTOM) | tag!(CHAR_BOTTOM))) |
        add_return_error!(ErrorKind::Custom(ERR_EQUALS), p_equals) |
        // composite term:
        map!(
            pair!(p_pred, sp!(p_term_args)),
            |(p, ts): (Pred, Vec<Term>)| p.app(ts)
        ) |
        delimited!(sp!(tag!(L_PAREN)),
            return_error!(ErrorKind::Custom(ERR_FORMULA), p_formula),
            return_error!(ErrorKind::Custom(ERR_R_PAREN), tag!(R_PAREN))
        )
    )
);

named!(p_not<Span, Formula>,
    alt!(
        preceded!(
            sp!(alt!(tag!(NOT) | tag!(TILDE) | tag!(NEG))),
            map!(alt!(p_not | p_quantified), not)
        ) |
        sp!(p_atom)
    )
);

named!(p_and<Span, Formula>,
    do_parse!(
        first: p_not >>
        second: fold_many0!(
            preceded!(
                sp!(alt!(tag!(AND) | tag!(AMPERSAND) | tag!(WEDGE))),
                return_error!(ErrorKind::Custom(ERR_FORMULA), alt!(p_and | p_quantified))
            ),
            first,
            |acc: Formula, f| acc.and(f)
        ) >>
        (second)
    )
);

named!(p_or<Span, Formula>,
    do_parse!(
        first: p_and >>
        second: fold_many0!(
            preceded!(
                sp!(alt!(tag!(OR) | tag!(BAR) | tag!(VEE))),
                return_error!(ErrorKind::Custom(ERR_FORMULA), alt!(p_or | p_quantified))
            ),
            first,
            |acc: Formula, f| acc.or(f)
        ) >>
        (second)
    )
);

named!(p_implication<Span, Formula>,
    map!(
        pair!(
            p_or,
            opt!(
                pair!(
                    sp!(
                        alt!(
                            value!(
                                IMPLIES,
                                alt!(tag!(IMPLIES) | tag!(RIGHT_ARROW) | tag!(CHAR_RIGHT_ARROW))
                            ) |
                            value!(
                                IFF,
                                alt!(tag!(IFF) | tag!(DOUBLE_ARROW) | tag!(CHAR_DOUBLE_ARROW))
                            )
                        )
                    ),
                    return_error!(ErrorKind::Custom(ERR_FORMULA), alt!(p_implication | p_quantified))
                )
            )
        ),
        |(left, right)| {
            match right {
                Some((o, r)) => if o == IMPLIES { left.implies(r) } else { left.iff(r) },
                None         => left
            }
        }
    )
);

named!(p_quantified<Span, Formula>,
    do_parse!(
        q: sp!(
            alt!(
                value!(
                    FORALL,
                    alt!(tag!(FORALL) | tag!(EXCLAMATION) | tag!(CHAR_FORALL))
                ) |
                value!(
                    EXISTS,
                    alt!(tag!(EXISTS) | tag!(QUESTION) | tag!(CHAR_EXISTS))
                )
            )
        ) >>
        vs: return_error!(ErrorKind::Custom(ERR_VARS), p_vars) >>
        return_error!(ErrorKind::Custom(ERR_DOT), sp!(tag!(DOT))) >>
        f: return_error!(ErrorKind::Custom(ERR_FORMULA), p_formula) >>
        ( if q == FORALL { forall(vs, f) } else { exists(vs, f) } )
    )
);

named!(p_formula<Span, Formula>,
    alt!(p_quantified | p_implication)
);

named!(pub theory<Span, Theory>,
    map!(
        many_till!(
            map!(
                terminated!(
                    sp!(p_formula),
                    return_error!(ErrorKind::Custom(ERR_SEMI_COLON),
                        sp!(tag!(SEMI_COLON))
                    )
                ),
                |f| Option::Some(f)
            ),
            value!((), sp!(eof!()))
        ),
        |(fs, _)| {
            let formulae: Vec<Formula> = fs.into_iter()
                .filter_map(|f| f)
                .collect();
            Theory::from(formulae)
        }
    )
);

fn make_parser_error(error: &Err<Span, u32>) -> ParserError {
    match error {
        Err::Error(Context::Code(pos, ErrorKind::Custom(code))) | Err::Failure(Context::Code(pos, ErrorKind::Custom(code))) => {
            let found = if pos.fragment.len() != 0 {
                Some(pos.fragment.0.to_owned())
            } else {
                None
            };
            let code = *code;
            match code {
                ERR_SEMI_COLON | ERR_DOT | ERR_L_PAREN | ERR_R_PAREN
                => ParserError::Missing { line: pos.line, column: pos.get_column() as u32, code },
                ERR_FORMULA | ERR_TERM | ERR_VARS | ERR_LOWER
                => ParserError::Expecting { line: pos.line, column: pos.get_column() as u32, code, found },
                _ => ParserError::Failed { line: pos.line, column: pos.get_column() as u32 },
            }
        }
        Err::Error(Context::Code(pos, _)) | Err::Failure(Context::Code(pos, _)) => {
            ParserError::Failed { line: pos.line, column: pos.get_column() as u32 }
        }
        _ => ParserError::Unknown,
    }
}

impl FromStr for Formula {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        p_formula(Span::new(CompleteStr(s)))
            .map(|r| r.1)
            .map_err(|e| make_parser_error(&e).into())
    }
}

impl FromStr for Theory {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        theory(Span::new(CompleteStr(s)))
            .map(|r| r.1)
            .map_err(|e| make_parser_error(&e).into())
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
        assert_eq!(result.to_string(), expected);
        assert_eq!(str.fragment.0, remaining);
    }

    fn fail<R: PartialEq + fmt::Debug>(
        parser: fn(Span) -> nom::IResult<Span, R, u32>,
        parse_str: &str) {
        let result = parser(Span::new(CompleteStr(parse_str)));
        assert!(result.is_err());
    }

    #[test]
    fn test_lower_identifier() {
        success(p_lower_ident, "_", "_".to_owned(), "");
        success(p_lower_ident, "a", "a".to_owned(), "");
        success(p_lower_ident, "_ab", "_ab".to_owned(), "");
        success(p_lower_ident, "aB", "aB".to_owned(), "");
        success(p_lower_ident, "aB!", "aB".to_owned(), "!");
        success(p_lower_ident, "johnSn0w", "johnSn0w".to_owned(), "");

        fail(p_lower_ident, "B");
        fail(p_lower_ident, "Blah");
        fail(p_lower_ident, "!ABC");
        fail(p_lower_ident, "123");
    }

    #[test]
    fn test_upper_identifier() {
        success(p_upper_ident, "A", "A".to_owned(), "");
        success(p_upper_ident, "AB", "AB".to_owned(), "");
        success(p_upper_ident, "AB!", "AB".to_owned(), "!");
        success(p_upper_ident, "JohnSn0w", "JohnSn0w".to_owned(), "");

        fail(p_upper_ident, "b");
        fail(p_upper_ident, "blah");
        fail(p_upper_ident, "!ABC");
        fail(p_upper_ident, "123");
        fail(p_upper_ident, "_");
        fail(p_upper_ident, "_AB");
    }

    #[test]
    fn test_var() {
        success(p_var, "x", _x(), "");

        fail(p_var, "  x");
        fail(p_var, "'a");
        fail(p_var, "B");
    }

    #[test]
    fn test_vars() {
        success(p_vars, "x", vec![_x()], "");
        success(p_vars, "x,y", vec![_x(), _y()], "");
        success(p_vars, "  x", vec![_x()], "");
        success(p_vars, "x, y", vec![_x(), _y()], "");
        success(p_vars, "x, y\t,\nz", vec![_x(), _y(), _z()], "");
        success(p_vars, "x,", vec![_x()], "");
        success(p_vars, "x,y   ,   ", vec![_x(), _y()], "");

        fail(p_vars, ",x");
        fail(p_vars, "B");
    }

    #[test]
    fn test_const() {
        success(p_const, "'a", _a(), "");
        fail(p_const, "x");
        fail(p_const, "   'a");
        fail(p_const, "'  a");
        fail(p_const, "''a");
        fail(p_const, "B");
    }

    #[test]
    fn test_func() {
        success(p_func, "f", f(), "");
        fail(p_func, "  f");
        fail(p_func, "'a");
        fail(p_func, "'B");
        fail(p_func, "B");
    }

    #[test]
    fn test_term() {
        success(p_term, "x", x(), "");
        success(p_term, "'a", a(), "");
        success(p_term, "f()", f().app0(), "");
        success(p_term, "f( )", f().app0(), "");
        success_to_string(p_term, "f(x)", "f(x)", "");
        success_to_string(p_term, "f(x,   y   )", "f(x, y)", "");
        success_to_string(p_term, "f(x,   y   \n , z)", "f(x, y, z)", "");
        success_to_string(p_term, "f(f(f(f(f(f(f(x)))))))", "f(f(f(f(f(f(f(x)))))))", "");
        success_to_string(p_term, "f  (x)", "f(x)", "");
        success_to_string(p_term, "f  (   x   )   ", "f(x)", "");
        success_to_string(p_term, "f(w, g (  x, y, z))", "f(w, g(x, y, z))", "");
        success_to_string(p_term, "f('a, x, g('b, h(x)))", "f('a, x, g('b, h(x)))", "");
        fail(p_term, "''a");
        fail(p_term, "P()");
        fail(p_term, "f(Q())");
        fail(p_term, "12f(x)");
        fail(p_term, "f(1, 2)");
        fail(p_term, "f(x, g(1))");
    }

    #[test]
    fn test_equals() {
        success_to_string(p_equals, "x = y", "x = y", "");
        success_to_string(p_equals, "'a = 'b", "'a = 'b", "");
        success_to_string(p_equals, "f(x) = y", "f(x) = y", "");
        success_to_string(p_equals, "  f  (x  ) = y", "f(x) = y", "");

        fail(p_equals, "A = B");
        fail(p_equals, "!a = b");
        fail(p_equals, "a != b");
    }

    #[test]
    fn test_pred() {
        success(p_pred, "P", P(), "");
        fail(p_pred, "  P");
        fail(p_pred, "'a");
        fail(p_pred, "x");
    }

    #[test]
    fn test_line_comment() {
        success(p_line_comment, "//\n", (), "");
        success(p_line_comment, "  //\n", (), "");
        success(p_line_comment, "// comment line \n", (), "");
        success(p_line_comment, "//comment line \n", (), "");
        success(p_line_comment, "   //   comment line \n", (), "");
        success(p_line_comment, "//", (), "");
        fail(p_line_comment, "/");
    }

    #[test]
    fn test_block_comment() {
        success(p_block_comment, "/**/", (), "");
        success(p_block_comment, "  /**/", (), "");
        success(p_block_comment, "/* comment line */", (), "");
        success(p_block_comment, "/* comment line \n*/", (), "");
        success(p_block_comment, "/*comment line */", (), "");
        success(p_block_comment, "   /*   comment line \n*/", (), "");
        fail(p_block_comment, "/*");
        fail(p_block_comment, "/");
    }

    #[test]
    fn test_atom() {
        success(p_atom, TRUE, Top, "");
        success(p_atom, CHAR_TOP, Top, "");
        success(p_atom, TOP, Top, "");
        success(p_atom, FALSE, Bottom, "");
        success(p_atom, CHAR_BOTTOM, Bottom, "");
        success(p_atom, BOTTOM, Bottom, "");
        success_to_string(p_atom, "x = f('a)", "x = f('a)", "");
        success_to_string(p_atom, "P()", "P()", "");
        success_to_string(p_atom, "P( )", "P()", "");
        success_to_string(p_atom, "P(x)", "P(x)", "");
        success_to_string(p_atom, "P(x,   y   )", "P(x, y)", "");
        success_to_string(p_atom, "P(x,   y   \n , z)", "P(x, y, z)", "");
        success_to_string(p_atom, "P(f(f(f(f(f(f(x)))))))", "P(f(f(f(f(f(f(x)))))))", "");
        success_to_string(p_atom, "P  (x)", "P(x)", "");
        success_to_string(p_atom, "P  (   x   )   ", "P(x)", "");
        success_to_string(p_atom, "P(w, g (  x, y, z))", "P(w, g(x, y, z))", "");
        success_to_string(p_atom, "P('a, x, g('b, h(x)))", "P('a, x, g('b, h(x)))", "");
        fail(p_atom, "''a");
        fail(p_atom, "f()");
        fail(p_atom, "P(Q())");
        fail(p_atom, "12P(x)");
        fail(p_atom, "P(1, 2)");
        fail(p_atom, "P(x, g(1))");
    }

    #[test]
    fn test_formula() {
        success_to_string(p_formula, "true", "⊤", "");
        success_to_string(p_formula, "false", "⟘", "");
        success_to_string(p_formula, "((((true))))", "⊤", "");
        success_to_string(p_formula, "( true)", "⊤", "");
        success_to_string(p_formula, "(true )", "⊤", "");
        success_to_string(p_formula, "P()", "P()", "");
        success_to_string(p_formula, "  P()", "P()", "");
        success_to_string(p_formula, "  ~P()", "¬P()", "");
        success_to_string(p_formula, "P(x)", "P(x)", "");
        success_to_string(p_formula, "P('a)", "P('a)", "");
        success_to_string(p_formula, "P(x,y)", "P(x, y)", "");
        success_to_string(p_formula, "P('a,'b)", "P('a, 'b)", "");
        success_to_string(p_formula, "P('a,x)", "P('a, x)", "");
        success_to_string(p_formula, "P(x, y)", "P(x, y)", "");
        success_to_string(p_formula, "P(x,            y     \n)", "P(x, y)", "");
        success_to_string(p_formula, "P(f(x))", "P(f(x))", "");
        success_to_string(
            p_formula,
            "P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(x)))))))))))))))))))))",
            "P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(x)))))))))))))))))))))",
            "",
        );
        success_to_string(p_formula, "P(f(x, g(y)), g(f(g(y))))", "P(f(x, g(y)), g(f(g(y))))", "");
        success_to_string(p_formula, "'a = 'b", "'a = 'b", "");
        success_to_string(p_formula, "x = x", "x = x", "");
        success_to_string(p_formula, "f() = x", "f() = x", "");
        success_to_string(p_formula, "f(x) = x", "f(x) = x", "");
        success_to_string(p_formula, "f(x) = x", "f(x) = x", "");
        success_to_string(p_formula, "f(x) = g(h(g(f(x)), y))", "f(x) = g(h(g(f(x)), y))", "");
        success_to_string(p_formula, "P(x) implies Q(x)", "P(x) → Q(x)", "");
        success_to_string(p_formula, "P(x) implies Q(x) -> R(x)", "P(x) → (Q(x) → R(x))", "");
        success_to_string(p_formula, "P(x) implies (Q(x) -> R(x))", "P(x) → (Q(x) → R(x))", "");
        success_to_string(p_formula, "P(x) implies (Q(x) -> R(x))", "P(x) → (Q(x) → R(x))", "");
        success_to_string(p_formula, "P(x) implies (Q(x) -> R(x) -> Q(z))", "P(x) → (Q(x) → (R(x) → Q(z)))", "");
        success_to_string(p_formula, "P(x) iff Q(x)", "P(x) ⇔ Q(x)", "");
        success_to_string(p_formula, "P(x) iff Q(x) <=> R(x)", "P(x) ⇔ (Q(x) ⇔ R(x))", "");
        success_to_string(p_formula, "P(x) iff (Q(x) <=> R(x))", "P(x) ⇔ (Q(x) ⇔ R(x))", "");
        success_to_string(p_formula, "P(x) iff (Q(x) <=> R(x) <=> Q(z))", "P(x) ⇔ (Q(x) ⇔ (R(x) ⇔ Q(z)))", "");
        success_to_string(p_formula, "P(x) iff Q(x) implies R(x)", "P(x) ⇔ (Q(x) → R(x))", "");
        success_to_string(p_formula, "P(x) implies Q(x) iff R(x)", "P(x) → (Q(x) ⇔ R(x))", "");
        success_to_string(p_formula, "exists x . P(x)", "∃ x. P(x)", "");
        success_to_string(p_formula, "exists x,y . P(x, y)", "∃ x, y. P(x, y)", "");
        success_to_string(p_formula, "exists x . exists y, z. P(x, y, z)", "∃ x. (∃ y, z. P(x, y, z))", "");
        success_to_string(p_formula, "exists x . P(x) implies Q(x)", "∃ x. (P(x) → Q(x))", "");
        success_to_string(p_formula, "exists x . (P(x) implies Q(x))", "∃ x. (P(x) → Q(x))", "");
        success_to_string(p_formula, "forall x . P(x)", "∀ x. P(x)", "");
        success_to_string(p_formula, "forall x,y . P(x, y)", "∀ x, y. P(x, y)", "");
        success_to_string(p_formula, "forall x . forall y, z. P(x, y, z)", "∀ x. (∀ y, z. P(x, y, z))", "");
        success_to_string(p_formula, "forall x . P(x) implies Q(x)", "∀ x. (P(x) → Q(x))", "");
        success_to_string(p_formula, "forall x . (P(x) implies Q(x))", "∀ x. (P(x) → Q(x))", "");
        success_to_string(p_formula, "forall x . exists y . P(x, y)", "∀ x. (∃ y. P(x, y))", "");
        success_to_string(p_formula, "P(x) or Q(y)", "P(x) ∨ Q(y)", "");
        success_to_string(p_formula, "P(x) or Q(y) or R(z)", "P(x) ∨ (Q(y) ∨ R(z))", "");
        success_to_string(p_formula, "(P(x) or Q(y)) or R(z)", "(P(x) ∨ Q(y)) ∨ R(z)", "");
        success_to_string(p_formula, "P(x) or Q(y) or (R(z) or S(z))", "P(x) ∨ (Q(y) ∨ (R(z) ∨ S(z)))", "");
        success_to_string(p_formula, "P(x) implies Q(x) or R(x)", "P(x) → (Q(x) ∨ R(x))", "");
        success_to_string(p_formula, "P(x) or Q(x) implies R(x)", "(P(x) ∨ Q(x)) → R(x)", "");
        success_to_string(p_formula, "exists x . P(x) or Q(x)", "∃ x. (P(x) ∨ Q(x))", "");
        success_to_string(p_formula, "P(x) or exists y . Q(y)", "P(x) ∨ (∃ y. Q(y))", "");
        success_to_string(p_formula, "exists x . P(x) or exists y . Q(y)", "∃ x. (P(x) ∨ (∃ y. Q(y)))", "");
        success_to_string(p_formula, "P(x) or forall y . Q(y)", "P(x) ∨ (∀ y. Q(y))", "");
        success_to_string(p_formula, "exists x . P(x) or forall y . Q(y)", "∃ x. (P(x) ∨ (∀ y. Q(y)))", "");
        success_to_string(p_formula, "P(x) and Q(y) or R(z)", "(P(x) ∧ Q(y)) ∨ R(z)", "");
        success_to_string(p_formula, "P(x) and (Q(y) or R(z))", "P(x) ∧ (Q(y) ∨ R(z))", "");
        success_to_string(p_formula, "P(x) or Q(y) and R(z)", "P(x) ∨ (Q(y) ∧ R(z))", "");
        success_to_string(p_formula, "P(x) and Q(y) and R(z)", "P(x) ∧ (Q(y) ∧ R(z))", "");
        success_to_string(p_formula, "P(w) and Q(x) and R(y) and S(z)", "P(w) ∧ (Q(x) ∧ (R(y) ∧ S(z)))", "");
        success_to_string(p_formula, "(P(x) and Q(y)) and R(z)", "(P(x) ∧ Q(y)) ∧ R(z)", "");
        success_to_string(p_formula, "P(x) and Q(y) implies R(z)", "(P(x) ∧ Q(y)) → R(z)", "");
        success_to_string(p_formula, "P(x) and exists y . Q(y)", "P(x) ∧ (∃ y. Q(y))", "");
        success_to_string(p_formula, "exists x . P(x) and exists y . Q(y)", "∃ x. (P(x) ∧ (∃ y. Q(y)))", "");
        success_to_string(p_formula, "P(x) and forall y . Q(y)", "P(x) ∧ (∀ y. Q(y))", "");
        success_to_string(p_formula, "exists x . P(x) and forall y . Q(y)", "∃ x. (P(x) ∧ (∀ y. Q(y)))", "");
        success_to_string(p_formula, "not true", "¬⊤", "");
        success_to_string(p_formula, "not true -> false", "(¬⊤) → ⟘", "");
        success_to_string(p_formula, "~x=y", "¬(x = y)", "");
        success_to_string(p_formula, "true -> not false", "⊤ → (¬⟘)", "");
        success_to_string(p_formula, "not P(x, y) or Q(z)", "(¬P(x, y)) ∨ Q(z)", "");
        success_to_string(p_formula, "not P(x, y) and Q(z)", "(¬P(x, y)) ∧ Q(z)", "");
        success_to_string(p_formula, "not not R(x)", "¬(¬R(x))", "");
        success_to_string(p_formula, "not not not not not R(x) and S(y)", "(¬(¬(¬(¬(¬R(x)))))) ∧ S(y)", "");
        success_to_string(p_formula, "not exists y . Q(y)", "¬(∃ y. Q(y))", "");
        success_to_string(p_formula, "exists x . not exists y . Q(y)", "∃ x. (¬(∃ y. Q(y)))", "");
        success_to_string(p_formula, "Q(y) & ! x. P(x)", "Q(y) ∧ (∀ x. P(x))", "");
        success_to_string(p_formula, "Q(y) | ! x. P(x)", "Q(y) ∨ (∀ x. P(x))", "");
        success_to_string(p_formula, "Q(y) -> ! x. P(x)", "Q(y) → (∀ x. P(x))", "");
        success_to_string(
            p_formula,
            "P(x) implies Q(y) and exists z . f(z) = g(f(z)) or (forall y, z . S(y,z) implies false)",
            "P(x) → (Q(y) ∧ (∃ z. ((f(z) = g(f(z))) ∨ (∀ y, z. (S(y, z) → ⟘)))))",
            "",
        );
        success_to_string(
            p_formula,
            "not forall x, y . P(x) and Q(y) implies h(z) = z",
            "¬(∀ x, y. ((P(x) ∧ Q(y)) → (h(z) = z)))",
            "",
        );
        success_to_string(
            p_formula,
            "∀ x. ∃ y. ((x = y) ∧ ¬P(y)) ∨ (Q(x) → R(y))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            p_formula,
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            p_formula,
            "! x. ? y. ((x = y) & ~P(y)) | (Q(x) -> R(y))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
        success_to_string(
            p_formula,
            "! x. (? y. (((x = y) & (~P(y))) | (Q(x) -> R(y))))",
            "∀ x. (∃ y. (((x = y) ∧ (¬P(y))) ∨ (Q(x) → R(y))))",
            "",
        );
    }

    #[test]
    fn test_theory() {
        success_to_string(
            theory,
            "  P(x)   ;",
            "P(x)",
            "",
        );
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
        success_to_string(
            theory,
            "// comment 0\n\
            E /*reflexive*/(//first argument \n\
            x, \n\
            /*second argument*/ x)\
            ;\
            // another comment\n\
            /* yet another comment */
            E(x,y) -> E(y,x) /*symmetric*/ ;\
            E(x,y) & E(y,z) -> /* transitivity */ E(x,z);",
            "E(x, x)\nE(x, y) → E(y, x)\n(E(x, y) ∧ E(y, z)) → E(x, z)",
            "",
        );
        success_to_string(
            theory,
            "P(x);exists x . Q(x);R(x) -> S(x);",
            "P(x)\n∃ x. Q(x)\nR(x) → S(x)",
            "",
        );
    }

    #[test]
    fn parse_failure() {
        {
            let parsed: Result<Theory, Error> = "P(X)".parse();
            assert_eq!("expecting 'term' on line 1, column 3; found \"X)\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P('A)".parse();
            assert_eq!("expecting 'term' on line 1, column 3; found \"'A)\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x)".parse();
            assert_eq!("missing ';' at line 1, column 5", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x".parse();
            assert_eq!("missing ')' at line 1, column 4", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "~P(x".parse();
            assert_eq!("missing ')' at line 1, column 5", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) and ".parse();
            assert_eq!("expecting 'formula' on line 1, column 10", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) and X".parse();
            assert_eq!("expecting 'formula' on line 1, column 10; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) or".parse();
            assert_eq!("expecting 'formula' on line 1, column 8", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) or X".parse();
            assert_eq!("expecting 'formula' on line 1, column 9; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) ->".parse();
            assert_eq!("expecting 'formula' on line 1, column 8", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) -> X".parse();
            assert_eq!("expecting 'formula' on line 1, column 9; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) <=>".parse();
            assert_eq!("expecting 'formula' on line 1, column 9", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x) <=> X".parse();
            assert_eq!("expecting 'formula' on line 1, column 10; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "!x P(x".parse();
            assert_eq!("missing '.' at line 1, column 4", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "! P(x)".parse();
            assert_eq!("expecting 'variables' on line 1, column 3; found \"P(x)\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "!x . ".parse();
            assert_eq!("expecting 'formula' on line 1, column 6", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "!x . X".parse();
            assert_eq!("expecting 'formula' on line 1, column 6; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "?x P(x".parse();
            assert_eq!("missing '.' at line 1, column 4", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "? P(x)".parse();
            assert_eq!("expecting 'variables' on line 1, column 3; found \"P(x)\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "?x . ".parse();
            assert_eq!("expecting 'formula' on line 1, column 6", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "?x . X".parse();
            assert_eq!("expecting 'formula' on line 1, column 6; found \"X\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "x".parse();
            assert_eq!("failed to parse the input at line 1, column 1", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "(X)".parse();
            assert_eq!("expecting 'formula' on line 1, column 2; found \"X)\"", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "(P(x)".parse();
            assert_eq!("missing ')' at line 1, column 6", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x)\n\
            Q(x) <=> R(x);".parse();
            assert_eq!("missing ';' at line 2, column 1", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x);\n\
            Q(x) <=> R(x);\n\
            S(x) => Q(x);".parse();
            assert_eq!("missing ';' at line 3, column 6", parsed.err().unwrap().to_string());
        }
        {
            let parsed: Result<Theory, Error> = "P(x);\n\
            Q(x) <=> R(x);\n\
            S(x) and ".parse();
            assert_eq!("expecting 'formula' on line 3, column 10", parsed.err().unwrap().to_string());
        }
    }
}


