//! Implements a parser for first-order formulae and theories in Razor's syntax.
//!
//! The module provides a parser for first-order formulae by implementing [`FromStr`] for
//! [`FOF`] and [`Theory`]. The parser is often used implicitly through [`parse`] method.
//!
//! **Example**:
//! The following example parses a string into a [`FOF`]:
//! ```rust
//! use razor_fol::syntax::FOF;
//!
//! // parse a string into `FOF`:
//! let formula: FOF = "exists x. P(x) & Q(x)".parse().unwrap();
//!
//! assert_eq!("∃ x. (P(x) ∧ Q(x))", formula.to_string());
//! ```
//!
//! Similarly, a [`Theory`] can be parsed from a string:
//! ```rust
//! use razor_fol::syntax::{FOF, Theory};
//!
//! // parse a string into `Theory` (formulae are separated by `;`)
//! let theory: Theory<FOF> = r#"
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
//! [`FOF`]: crate::syntax::FOF
//! [`Theory`]: crate::syntax::Theory
//! [`FromStr`]: std::str::FromStr
//! [`parse`]: ::std::str#parse
use super::syntax::{Theory, FOF};
use lalrpop_util::ParseError;
use std::str::FromStr;
use thiserror::Error;

lalrpop_mod!(pub grammar); // synthesized by LALRPOP

#[derive(PartialEq, Debug)]
pub enum TokenType {
    Comma,
    Dot,
    Semicolon,
    LParen,
    RParen,
    Equal,
    True,
    False,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Forall,
    Exists,
    Lower,
    Upper,
    Const,
    Unknown,
}

impl<S: AsRef<str>> From<S> for TokenType {
    fn from(s: S) -> Self {
        match s.as_ref() {
            "_COMMA_" => Self::Comma,
            "_DOT_" => Self::Dot,
            "_SEMICOLON_" => Self::Semicolon,
            "_LPAREN_" => Self::LParen,
            "_RPAREN_" => Self::RParen,
            "_EQUAL_" => Self::Equal,
            "_TRUE_" => Self::True,
            "_FALSE_" => Self::False,
            "_NOT_" => Self::Not,
            "_AND_" => Self::And,
            "_OR_" => Self::Or,
            "_IMPLIES_" => Self::Implies,
            "_IFF_" => Self::Iff,
            "_FORALL_" => Self::Forall,
            "_EXISTS_" => Self::Exists,
            "_LOWER_" => Self::Lower,
            "_UPPER_" => Self::Upper,
            "_CONST_" => Self::Const,
            _ => Self::Unknown,
        }
    }
}

impl ToString for TokenType {
    fn to_string(&self) -> String {
        match self {
            Self::Comma => "`,`",
            Self::Dot => "`.`",
            Self::Semicolon => "`;`",
            Self::LParen => "`(`",
            Self::RParen => "`)`",
            Self::Equal => "`=`",
            Self::True => "`true`",
            Self::False => "`false`",
            Self::Not => "`not`",
            Self::And => "`and`",
            Self::Or => "`or`",
            Self::Implies => "`implies`",
            Self::Iff => "`iff`",
            Self::Forall => "`forall`",
            Self::Exists => "`exists`",
            Self::Lower => "`lowercase identifier`",
            Self::Upper => "`uppercase identifier`",
            Self::Const => "`constant identifier`",
            Self::Unknown => "`unknown token`",
        }
        .into()
    }
}

/// Is the type of errors returned by the parser.
#[derive(Error, PartialEq, Debug)]
pub enum Error {
    #[error("found `{found:?}` at line {}, column {}; expecting {}",
            (*.position).line,
            (*.position).column,
            Error::pretty_expected_tokens(&*.expected),
    )]
    UnrecognizedToken {
        position: Position,
        expected: Vec<TokenType>,
        found: String,
    },
    #[error("invalid token at line {}, column {}", (*.position).line, (*.position).column)]
    InvalidToken { position: Position },
    #[error("unexpected end of input at line {}, column {}; expecting {}",
            (*.position).line,
            (*.position).column,
            Error::pretty_expected_tokens(&*.expected)
    )]
    UnrecognizedEOF {
        position: Position,
        expected: Vec<TokenType>,
    },
    #[error("{}", .source.to_string())]
    Syntax {
        #[from]
        source: crate::syntax::Error,
    },
    #[error("unexpected token `{found:?}` at line {}, column {}", (*.position).line, (*.position).column)]
    ExtraToken { position: Position, found: String },
}

impl Error {
    fn pretty_expected_tokens(items: &[TokenType]) -> String {
        let strs = items.iter().map(ToString::to_string).collect::<Vec<_>>();
        match items.len() {
            0 => "".into(),
            1 => format!("{}", strs[0]),
            2 => format!("{} or {}", strs[0], strs[1]),
            n => format!("{}, or {}", strs[0..n - 1].join(", "), strs[n - 1]),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct Position {
    line: usize,
    column: usize,
}

// Stores source information to retrieve token positions in the source.
struct SourceInfo<'s> {
    lines: Vec<usize>,
    source: &'s str,
}

impl<'s> SourceInfo<'s> {
    fn new(source: &'s str) -> Self {
        let lines = source
            .bytes()
            .enumerate()
            .filter(|&(_, ch)| ch == b'\n')
            .map(|(i, _)| i + 1);
        Self {
            lines: std::iter::once(0).chain(lines).collect(),
            source,
        }
    }

    fn position(&self, location: usize) -> Position {
        let index = self
            .lines
            .iter()
            .enumerate()
            .find(|&(_, l)| location < *l)
            .map(|(i, _)| i);
        let line = index.unwrap_or(self.lines.len());
        let column = self.source[self.lines[line - 1]..location].chars().count() + 1;

        Position { line, column }
    }

    fn convert_error<T: ToString>(&self, error: ParseError<usize, T, Error>) -> Error {
        match error {
            ParseError::InvalidToken { location } => {
                let pos = self.position(location);
                Error::InvalidToken {
                    position: Position {
                        line: pos.line,
                        column: pos.column,
                    },
                }
            }
            ParseError::UnrecognizedEOF { location, expected } => {
                let pos = self.position(location);
                Error::UnrecognizedEOF {
                    position: Position {
                        line: pos.line,
                        column: pos.column,
                    },
                    expected: expected.into_iter().map(From::from).collect(),
                }
            }
            ParseError::UnrecognizedToken { token, expected } => {
                let pos = self.position(token.0);
                Error::UnrecognizedToken {
                    position: Position {
                        line: pos.line,
                        column: pos.column,
                    },
                    expected: expected.into_iter().map(From::from).collect(),
                    found: token.1.to_string(),
                }
            }
            ParseError::ExtraToken { token } => {
                let pos = self.position(token.0);
                Error::ExtraToken {
                    position: Position {
                        line: pos.line,
                        column: pos.column,
                    },
                    found: token.1.to_string(),
                }
            }
            ParseError::User { error } => error,
        }
    }
}

impl FromStr for FOF {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let info = SourceInfo::new(s);
        grammar::FormulaParser::new()
            .parse(s)
            .map_err(|e| info.convert_error(e))
    }
}

impl FromStr for Theory<FOF> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let info = SourceInfo::new(s);
        grammar::TheoryParser::new()
            .parse(s)
            .map_err(|e| info.convert_error(e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{c, f, fof, pred, term, v};

    #[test]
    fn lower_ident() {
        assert_eq!(grammar::LowerParser::new().parse("_").unwrap(), "_");
        assert_eq!(grammar::LowerParser::new().parse("a").unwrap(), "a");
        assert_eq!(grammar::LowerParser::new().parse("_ab").unwrap(), "_ab");
        assert_eq!(grammar::LowerParser::new().parse("aB").unwrap(), "aB");
        assert_eq!(grammar::LowerParser::new().parse("a_B").unwrap(), "a_B");
        assert_eq!(grammar::LowerParser::new().parse("aB_").unwrap(), "aB_");
        assert_eq!(
            grammar::LowerParser::new().parse("duch3Ss").unwrap(),
            "duch3Ss"
        );

        assert!(grammar::LowerParser::new().parse("aB!").is_err());

        assert!(grammar::LowerParser::new().parse("B").is_err());
        assert!(grammar::LowerParser::new().parse("Blah").is_err());
        assert!(grammar::LowerParser::new().parse("!ABC").is_err());
        assert!(grammar::LowerParser::new().parse("123").is_err());
    }

    #[test]
    fn upper_ident() {
        assert_eq!(grammar::UpperParser::new().parse("A").unwrap(), "A");
        assert_eq!(grammar::UpperParser::new().parse("AB").unwrap(), "AB");
        assert_eq!(grammar::UpperParser::new().parse("A_B").unwrap(), "A_B");
        assert_eq!(grammar::UpperParser::new().parse("AB_").unwrap(), "AB_");
        assert_eq!(
            grammar::UpperParser::new().parse("Duch3Ss").unwrap(),
            "Duch3Ss"
        );

        assert!(grammar::UpperParser::new().parse("AB!").is_err());

        assert!(grammar::UpperParser::new().parse("b").is_err());
        assert!(grammar::UpperParser::new().parse("blah").is_err());
        assert!(grammar::UpperParser::new().parse("!ABC").is_err());
        assert!(grammar::UpperParser::new().parse("123").is_err());
        assert!(grammar::UpperParser::new().parse("_").is_err());
        assert!(grammar::UpperParser::new().parse("_AB").is_err());
    }

    #[test]
    fn var() {
        assert_eq!(grammar::VarParser::new().parse("x").unwrap(), v!(x));
        assert_eq!(grammar::VarParser::new().parse("   x").unwrap(), v!(x));

        assert!(grammar::VarParser::new().parse("'a").is_err());
        assert!(grammar::VarParser::new().parse("B").is_err());
    }

    #[test]
    fn vars() {
        assert_eq!(grammar::VarsParser::new().parse("").unwrap(), vec![]);
        assert_eq!(grammar::VarsParser::new().parse("x").unwrap(), vec![v!(x)]);
        assert_eq!(
            grammar::VarsParser::new().parse("x,y").unwrap(),
            vec![v!(x), v!(y)]
        );
        assert_eq!(
            grammar::VarsParser::new().parse("  x").unwrap(),
            vec![v!(x)]
        );
        assert_eq!(
            grammar::VarsParser::new().parse("x, y").unwrap(),
            vec![v!(x), v!(y)]
        );
        assert_eq!(
            grammar::VarsParser::new().parse("x, y\t,\nz").unwrap(),
            vec![v!(x), v!(y), v!(z)]
        );
        assert_eq!(grammar::VarsParser::new().parse("x,").unwrap(), vec![v!(x)]);
        assert_eq!(
            grammar::VarsParser::new().parse("x,y   ,    ").unwrap(),
            vec![v!(x), v!(y)]
        );

        assert!(grammar::VarParser::new().parse(",x").is_err());
        assert!(grammar::VarParser::new().parse("B").is_err());
    }

    #[test]
    fn r#const() {
        assert_eq!(grammar::ConstParser::new().parse("'a").unwrap(), c!(a));
        assert_eq!(grammar::ConstParser::new().parse("    'a").unwrap(), c!(a));
        assert_eq!(grammar::ConstParser::new().parse("'_a").unwrap(), c!(_a));
        assert_eq!(grammar::ConstParser::new().parse("'a_").unwrap(), c!(a_));
        assert_eq!(grammar::ConstParser::new().parse("'a_b").unwrap(), c!(a_b));

        assert!(grammar::ConstParser::new().parse("x").is_err());
        assert!(grammar::ConstParser::new().parse("''a").is_err());
        assert!(grammar::ConstParser::new().parse("'B").is_err());
        assert!(grammar::ConstParser::new().parse("B").is_err());
        assert!(grammar::ConstParser::new().parse("'   a").is_err());
    }

    #[test]
    fn r#func() {
        assert_eq!(grammar::FuncParser::new().parse("f").unwrap(), f!(f));
        assert_eq!(grammar::FuncParser::new().parse("   f").unwrap(), f!(f));

        assert!(grammar::FuncParser::new().parse("'a").is_err());
        assert!(grammar::FuncParser::new().parse("'B").is_err());
        assert!(grammar::FuncParser::new().parse("B").is_err());
    }

    #[test]
    fn term() {
        assert_eq!(grammar::TermParser::new().parse("x").unwrap(), term!(x));
        assert_eq!(grammar::TermParser::new().parse("'a").unwrap(), term!(@a));
        assert_eq!(grammar::TermParser::new().parse("f()").unwrap(), term!(f()));
        assert_eq!(
            grammar::TermParser::new().parse("f(   )").unwrap(),
            term!(f())
        );
        assert_eq!(
            grammar::TermParser::new().parse("f(x)").unwrap(),
            term!(f(x))
        );
        assert_eq!(
            grammar::TermParser::new().parse("f(x,   y  )").unwrap(),
            term!(f(x, y))
        );
        assert_eq!(
            grammar::TermParser::new()
                .parse("f(x,   y  \n , z)")
                .unwrap(),
            term!(f(x, y, z))
        );
        assert_eq!(
            grammar::TermParser::new()
                .parse("f(f(f(f(f(f(f(x)))))))")
                .unwrap(),
            term!(f(f(f(f(f(f(f(x))))))))
        );
        assert_eq!(
            grammar::TermParser::new().parse("f   (x)").unwrap(),
            term!(f(x))
        );
        assert_eq!(
            grammar::TermParser::new().parse("f   (   x   )").unwrap(),
            term!(f(x))
        );
        assert_eq!(
            grammar::TermParser::new()
                .parse("f(w, g (  x, y, z))")
                .unwrap(),
            term!(f(w, g(x, y, z)))
        );

        assert!(grammar::TermParser::new().parse("''a").is_err());
        assert!(grammar::TermParser::new().parse("P()").is_err());
        assert!(grammar::TermParser::new().parse("f(Q())").is_err());
        assert!(grammar::TermParser::new().parse("12f(x)").is_err());
        assert!(grammar::TermParser::new().parse("f(1, 2)").is_err());
        assert!(grammar::TermParser::new().parse("f(x, g(1))").is_err());
    }

    #[test]
    fn equals() {
        assert_eq!(
            grammar::EqualParser::new().parse("x = y").unwrap(),
            fof!((x) = (y))
        );
        assert_eq!(
            grammar::EqualParser::new().parse("'a = 'b").unwrap(),
            fof!((@a) = (@b))
        );
        assert_eq!(
            grammar::EqualParser::new().parse("f(x) = y").unwrap(),
            fof!((f(x)) = (y))
        );
        assert_eq!(
            grammar::EqualParser::new().parse("f   (x  ) = y").unwrap(),
            fof!((f(x)) = (y))
        );

        assert!(grammar::TermParser::new().parse("A = B").is_err());
        assert!(grammar::TermParser::new().parse("!a = b").is_err());
        assert!(grammar::TermParser::new().parse("a != b").is_err());
    }

    #[test]
    fn pred() {
        assert_eq!(grammar::PredParser::new().parse("P").unwrap(), pred!(P));
        assert_eq!(grammar::PredParser::new().parse("   P").unwrap(), pred!(P));

        assert!(grammar::PredParser::new().parse("'a").is_err());
        assert!(grammar::PredParser::new().parse("x").is_err());
    }

    #[test]
    fn atom() {
        assert_eq!(grammar::AtomParser::new().parse("true").unwrap(), fof!('|'));
        assert_eq!(grammar::AtomParser::new().parse("⊤").unwrap(), fof!('|'));
        assert_eq!(grammar::AtomParser::new().parse("'|'").unwrap(), fof!('|'));
        assert_eq!(
            grammar::AtomParser::new().parse("false").unwrap(),
            fof!(_ | _)
        );
        assert_eq!(grammar::AtomParser::new().parse("⟘").unwrap(), fof!(_ | _));
        assert_eq!(
            grammar::AtomParser::new().parse("_|_").unwrap(),
            fof!(_ | _)
        );
        assert_eq!(
            grammar::AtomParser::new().parse("x = f('a)").unwrap(),
            fof!([x] = [f(@a)])
        );
        assert_eq!(grammar::AtomParser::new().parse("P()").unwrap(), fof!(P()));
        assert_eq!(grammar::AtomParser::new().parse("P( )").unwrap(), fof!(P()));
        assert_eq!(
            grammar::AtomParser::new().parse("P(x)").unwrap(),
            fof!(P(x))
        );
        assert_eq!(
            grammar::AtomParser::new().parse("P(x,   y   )").unwrap(),
            fof!(P(x, y))
        );
        assert_eq!(
            grammar::AtomParser::new()
                .parse("P(x,   y   \n , z)")
                .unwrap(),
            fof!(P(x, y, z))
        );
        assert_eq!(
            grammar::AtomParser::new()
                .parse("P(f(f(f(f(f(f(x)))))))")
                .unwrap(),
            fof!(P(f(f(f(f(f(f(x))))))))
        );
        assert_eq!(
            grammar::AtomParser::new().parse("P  (x)").unwrap(),
            fof!(P(x))
        );
        assert_eq!(
            grammar::AtomParser::new().parse("P  (  x  )  ").unwrap(),
            fof!(P(x))
        );
        assert_eq!(
            grammar::AtomParser::new()
                .parse("P(w, g (  x, y, z))")
                .unwrap(),
            fof!(P(w, g(x, y, z)))
        );
        assert_eq!(
            grammar::AtomParser::new()
                .parse("P('a, x, g('b, h(x)))")
                .unwrap(),
            fof!(P(@a, x, g(@b, h(x))))
        );

        assert!(grammar::PredParser::new().parse("''a").is_err());
        assert!(grammar::PredParser::new().parse("f()").is_err());
        assert!(grammar::PredParser::new().parse("P(Q())").is_err());
        assert!(grammar::PredParser::new().parse("12P(x)").is_err());
        assert!(grammar::PredParser::new().parse("P(1, 2)").is_err());
        assert!(grammar::PredParser::new().parse("P(x, g(1))").is_err());
    }

    #[test]
    fn formula() {
        assert_eq!(
            grammar::AtomParser::new().parse("P  (x)").unwrap(),
            fof!(P(x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("true").unwrap(),
            fof!('|')
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("false").unwrap(),
            fof!(_ | _)
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("((((true))))").unwrap(),
            fof!('|')
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("( true)").unwrap(),
            fof!('|')
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("(true )").unwrap(),
            fof!('|')
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P()").unwrap(),
            fof!(P())
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("  P()").unwrap(),
            fof!(P())
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("  ~P()").unwrap(),
            fof!(~[P()])
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P(x)").unwrap(),
            fof!(P(x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P('a)").unwrap(),
            fof!(P(@a))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P(x,y)").unwrap(),
            fof!(P(x, y))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P('a,'b)").unwrap(),
            fof!(P(@a, @b))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P('a,x)").unwrap(),
            fof!(P(@a, x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P(x, y)").unwrap(),
            fof!(P(x, y))
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x,            y     \n)")
                .unwrap(),
            fof!(P(x, y))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P(f(x))").unwrap(),
            fof!(P(f(x)))
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(x)))))))))))))))))))))")
                .unwrap(),
            fof!(P(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(
                f(x)
            ))))))))))))))))))))),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(f(x, g(y)), g(f(g(y))))")
                .unwrap(),
            fof!(P(f(x, g(y)), g(f(g(y))))),
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("'a = 'b").unwrap(),
            fof!((@a) = (@b))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("x = x").unwrap(),
            fof!((x) = (x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("f() = x").unwrap(),
            fof!((f()) = (x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("f(x) = x").unwrap(),
            fof!((f(x)) = (x))
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("f(x) = x").unwrap(),
            fof!((f(x)) = (x))
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("f(x) = g(h(g(f(x)), y))")
                .unwrap(),
            fof!([f(x)] = [g(h(g(f(x)), y))]),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies Q(x)")
                .unwrap(),
            fof!([P(x)] -> [Q(x)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies Q(x) -> R(x)")
                .unwrap(),
            fof!({P(x)} -> {[Q(x)] -> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies (Q(x) -> R(x))")
                .unwrap(),
            fof!({P(x)} -> {[Q(x)] -> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies (Q(x) -> R(x) -> Q(z))")
                .unwrap(),
            fof!({P(x)} -> {[Q(x)] -> [(R(x)) -> (Q(z))]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) iff Q(x)")
                .unwrap(),
            fof!([P(x)] <=> [Q(x)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) iff Q(x) <=> R(x)")
                .unwrap(),
            fof!({P(x)} <=> {[Q(x)] <=> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) iff (Q(x) <=> R(x))")
                .unwrap(),
            fof!({P(x)} <=> {[Q(x)] <=> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) iff (Q(x) <=> R(x) <=> Q(z))")
                .unwrap(),
            fof!({P(x)} <=> {[Q(x)] <=> [(R(x)) <=> (Q(z))]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) iff Q(x) implies R(x)")
                .unwrap(),
            fof!({P(x)} <=> {[Q(x)] -> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies (Q(x) iff R(x))")
                .unwrap(),
            fof!({P(x)} -> {[Q(x)] <=> [R(x)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x)")
                .unwrap(),
            fof!(? x. [P(x)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x,y . P(x, y)")
                .unwrap(),
            fof!(?x, y. [P(x, y)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . exists y, z. P(x, y, z)")
                .unwrap(),
            fof!(? x. {? y, z. [P(x, y, z)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) implies Q(x)")
                .unwrap(),
            fof!(? x. [{P(x)} -> {Q(x)}]),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . (P(x) implies Q(x))")
                .unwrap(),
            fof!(? x. [{P(x)} -> {Q(x)}]),
        );

        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x . P(x)")
                .unwrap(),
            fof!(! x. [P(x)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x,y . P(x, y)")
                .unwrap(),
            fof!(! x, y. [P(x, y)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x . forall y, z. P(x, y, z)")
                .unwrap(),
            fof!(! x. [! y, z. {P(x, y, z)}])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x . P(x) implies Q(x)")
                .unwrap(),
            fof!(! x. {[P(x)] -> [Q(x)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x . (P(x) implies Q(x))")
                .unwrap(),
            fof!(! x. {[P(x)] -> [Q(x)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("forall x . exists y . P(x, y)")
                .unwrap(),
            fof!(! x. {? y. [P(x, y)]}),
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("P(x) or Q(y)").unwrap(),
            fof!([P(x)] | [Q(y)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or Q(y) or R(z)")
                .unwrap(),
            fof!({ [P(x)] | [Q(y)] } | { R(z) })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("(P(x) or Q(y)) or R(z)")
                .unwrap(),
            fof!({ [P(x)] | [Q(y)] } | { R(z) })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or Q(y) or (R(z) or S(z))")
                .unwrap(),
            fof!({ [P(x)] | [Q(y)] } | { [R(z)] | [S(z)] })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) implies Q(x) or R(x)")
                .unwrap(),
            fof!({ P(x)} -> { [Q(x)] | [R(x)] })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or Q(x) implies R(x)")
                .unwrap(),
            fof!({ [P(x)] | [Q(x)] } -> {R(x)})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) or Q(x)")
                .unwrap(),
            fof!(? x. {[P(x)] | [Q(x)]})
        );

        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or exists y . Q(y)")
                .unwrap(),
            fof!({P(x)} | {? y . [Q(y)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) or exists y . Q(y)")
                .unwrap(),
            fof!(? x. {[P(x)] | [? y. (Q(y))]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or forall y . Q(y)")
                .unwrap(),
            fof!([P(x)] | [! y. (Q(y))])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) or forall y . Q(y)")
                .unwrap(),
            fof!(?x . { [P(x)] | [!y. (Q(y))]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and Q(y) or R(z)")
                .unwrap(),
            fof!({ [P(x)] & [Q(y)] } | { R(z) })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and (Q(y) or R(z))")
                .unwrap(),
            fof!({ P(x) } & { [Q(y)] | [R(z)] })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) or Q(y) and R(z)")
                .unwrap(),
            fof!({ P(x) } | { [Q(y)] & [R(z)] })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and Q(y) and R(z)")
                .unwrap(),
            fof!({ [P(x)] & [Q(y)] } & { R(z) })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(w) and Q(x) and R(y) and S(z)")
                .unwrap(),
            fof!({ [(P(w)) & (Q(x))] & [R(y)] } & { S(z) })
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("(P(x) and Q(y)) and R(z)")
                .unwrap(),
            fof!([(P(x)) & (Q(y))] & [R(z)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and Q(y) implies R(z)")
                .unwrap(),
            fof!([(P(x)) & (Q(y))] -> [R(z)])
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and exists y . Q(y)")
                .unwrap(),
            fof!({P(x)} & {? y . [Q(y)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) and exists y . Q(y)")
                .unwrap(),
            fof!(? x. {[P(x)] & [? y. (Q(y))]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("P(x) and forall y . Q(y)")
                .unwrap(),
            fof!({P(x)} & {!y.[Q(y)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . P(x) and forall y . Q(y)")
                .unwrap(),
            fof!(?x.{[P(x)] & [!y . (Q(y))]})
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("not true").unwrap(),
            fof!(~('|'))
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not true -> false")
                .unwrap(),
            fof!({~('|')} -> {_|_})
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("~x=y").unwrap(),
            fof!(~{(x) = (y)})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("true -> not false")
                .unwrap(),
            fof!({'|'} -> {~[_|_]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not P(x, y) or Q(z)")
                .unwrap(),
            fof!({~[P(x, y)]} | {Q(z)})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not P(x, y) and Q(z)")
                .unwrap(),
            fof!({~[P(x, y)]} & {Q(z)})
        );
        assert_eq!(
            grammar::FormulaParser::new().parse("not not R(x)").unwrap(),
            fof!(~(~[R(x)]))
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not not not not not R(x) and S(y)")
                .unwrap(),
            fof!({~(~(~(~(~[R(x)]))))} & {S(y)}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not exists y . Q(y)")
                .unwrap(),
            fof!(~{? y. [Q(y)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("exists x . not exists y . Q(y)")
                .unwrap(),
            fof!(? x. {~(? y. [Q(y)])}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("Q(y) & ! x. P(x)")
                .unwrap(),
            fof!({Q(y)} & {! x. [P(x)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("Q(y) | ! x. P(x)")
                .unwrap(),
            fof!({Q(y)} | {! x. [P(x)]})
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("Q(y) -> ! x. P(x)")
                .unwrap(),
            fof!({Q(y)} -> {! x. [P(x)]})
        );
        assert_eq!(
            grammar::FormulaParser::new().parse(            "P(x) implies Q(y) and exists z . f(z) = g(f(z)) or (forall y, z . S(y,z) implies false)").unwrap(),
            fof!({P(x)} -> {{Q(y)} & {? z. {{(f(z)) = (g(f(z)))} | {!y, z.{[S(y, z)] -> [_|_]}}}}}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("not forall x, y . P(x) and Q(y) implies h(z) = z")
                .unwrap(),
            fof!(~{! x, y . {[(P(x)) & (Q(y))] -> [(h(z)) = (z)]}}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("∀ x. ∃ y. (x = y ∧ ¬P(y)) ∨ (Q(x) → R(y))")
                .unwrap(),
            fof!(! x. {? y . [([(x) = (y)] & [~(P(y))]) | ([Q(x)] -> [R(y)])]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("∀ x. (∃ y. ((x = y ∧ (¬P(y))) ∨ (Q(x) → R(y))))")
                .unwrap(),
            fof!(! x. {? y . [([(x) = (y)] & [~(P(y))]) | ([Q(x)] -> [R(y)])]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("! x. ? y. (x = y & ~P(y)) | (Q(x) -> R(y))")
                .unwrap(),
            fof!(! x. {? y . [([(x) = (y)] & [~(P(y))]) | ([Q(x)] -> [R(y)])]}),
        );
        assert_eq!(
            grammar::FormulaParser::new()
                .parse("! x. (? y. ((x = y & (~P(y))) | (Q(x) -> R(y))))")
                .unwrap(),
            fof!(! x. {? y . [([(x) = (y)] & [~(P(y))]) | ([Q(x)] -> [R(y)])]}),
        );
    }

    #[test]
    pub fn theory() {
        assert_eq!(
            grammar::TheoryParser::new().parse("  P(x)   ;").unwrap(),
            vec![fof!(P(x))].into_iter().collect(),
        );
        assert_eq!(
            grammar::TheoryParser::new()
                .parse(
                    "E(x,x);\
                     E(x,y) -> E(y,x) ;\
                     E(x,y) & E(y,z) -> E(x,z);",
                )
                .unwrap(),
            vec![
                fof!(E(x, x)),
                fof!([E(x, y)] -> [E(y, x)]),
                fof!({[E(x, y)] & [E(y, z)]} -> {E(x, z)})
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(
            grammar::TheoryParser::new()
                .parse(
                    "// comment 0
                     E(x,x)
                     ;
                     // another comment
                     E(x,y) -> E(y,x) ;
                     E(x,y) & E(y,z) -> E(x,z);",
                )
                .unwrap(),
            vec![
                fof!(E(x, x)),
                fof!([E(x,y)] -> [E(y, x)]),
                fof!({[E(x,y)] & [E(y, z)]} -> {E(x, z)})
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(
            grammar::TheoryParser::new()
                .parse(
                    "// comment 0
                     E /*reflexive*/(//first argument
                     x,
                     /*second argument*/ x)
                     ;
                     // another comment
                     /* yet another comment */
                     E(x,y) -> E(y,x) /*symmetric*/ ;
                     E(x,y) & E(y,z) -> /* transitivity 
*/ E(x,z);",
                )
                .unwrap(),
            vec![
                fof!(E(x, x)),
                fof!([E(x,y)] -> [E(y, x)]),
                fof!({[E(x,y)] & [E(y, z)]} -> {E(x, z)})
            ]
            .into_iter()
            .collect(),
        );
        assert_eq!(
            grammar::TheoryParser::new()
                .parse("P(x);exists x . Q(x);R(x) -> S(x);")
                .unwrap(),
            vec![fof!(P(x)), fof!(? x . [Q(x)]), fof!([R(x)] -> [S(x)])]
                .into_iter()
                .collect(),
        );
    }

    #[test]
    fn failure() {
        use TokenType::*;

        {
            let parsed: Result<Theory<FOF>, Error> = "P(X)".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 3 },
                    expected: vec![Const, Lower, RParen,],
                    found: "X".into(),
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P('A)".parse();
            assert_eq!(
                Error::InvalidToken {
                    position: Position { line: 1, column: 3 }
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x)".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 5 },
                    expected: vec![And, Comma, Equal, Iff, Implies, Or, RParen, Semicolon]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 4 },
                    expected: vec![
                        And, Comma, Dot, Equal, Iff, Implies, LParen, Or, RParen, Semicolon
                    ]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "~P(x".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 5 },
                    expected: vec![
                        And, Comma, Dot, Equal, Iff, Implies, LParen, Or, RParen, Semicolon
                    ]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) and ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 9 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) and X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position {
                        line: 1,
                        column: 11
                    },
                    expected: vec![LParen,]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) or ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 8 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) or X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position {
                        line: 1,
                        column: 10
                    },
                    expected: vec![LParen,]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) -> ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 8 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) -> X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position {
                        line: 1,
                        column: 10
                    },
                    expected: vec![LParen,]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) <=> ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 9 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x) <=> X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position {
                        line: 1,
                        column: 11
                    },
                    expected: vec![LParen,]
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "!x P(x".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 4 },
                    expected: vec![
                        And, Comma, Dot, Equal, Iff, Implies, LParen, Or, RParen, Semicolon
                    ],
                    found: "P".into()
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "! P(x".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 3 },
                    expected: vec![Dot, Lower],
                    found: "P".into()
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "!x . ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 5 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "!x . X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 7 },
                    expected: vec![LParen,],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "∀x . X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 7 },
                    expected: vec![LParen,],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "?x P(x".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 4 },
                    expected: vec![
                        And, Comma, Dot, Equal, Iff, Implies, LParen, Or, RParen, Semicolon
                    ],
                    found: "P".into()
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "? P(x".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 3 },
                    expected: vec![Dot, Lower],
                    found: "P".into()
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "?x . ".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 5 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "?x . X".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 7 },
                    expected: vec![LParen,],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "x".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 2 },
                    expected: vec![
                        And, Comma, Dot, Equal, Iff, Implies, LParen, Or, RParen, Semicolon
                    ],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "(X)".parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 1, column: 3 },
                    expected: vec![LParen],
                    found: ")".into(),
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "(P(x)".parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 1, column: 6 },
                    expected: vec![And, Comma, Equal, Iff, Implies, Or, RParen, Semicolon],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x)
Q(x) <=> R(x);"
                .parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 2, column: 1 },
                    expected: vec![And, Comma, Equal, Iff, Implies, Or, RParen, Semicolon],
                    found: "Q".into(),
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x);
Q(x) => R(x);
S(x) <=> Q(x);"
                .parse();
            assert_eq!(
                Error::UnrecognizedToken {
                    position: Position { line: 2, column: 6 },
                    expected: vec![And, Iff, Implies, Or, RParen, Semicolon],
                    found: "=".into(),
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "P(x);
Q(x) <=> R(x);
S(x) and "
                .parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position { line: 3, column: 9 },
                    expected: vec![Const, Exists, False, Forall, Lower, LParen, Not, True, Upper],
                },
                parsed.err().unwrap()
            );
        }
        {
            let parsed: Result<Theory<FOF>, Error> = "f(x) = 'a;
// Testing error location with unicode characters:
∀x . /* comment 🪒 ♖♞♗♚♕♝♘♜ */ X"
                .parse();
            assert_eq!(
                Error::UnrecognizedEOF {
                    position: Position {
                        line: 3,
                        column: 32
                    },
                    expected: vec![LParen,],
                },
                parsed.err().unwrap()
            );
        }
        {
            use crate::syntax::signature::PredSig;
            let parsed: Result<Theory<FOF>, Error> = "P(x);
P(x,y);"
                .parse();
            assert_eq!(
                Error::Syntax {
                    source: crate::syntax::Error::InconsistentPredSig {
                        this: PredSig {
                            symbol: pred!(P),
                            arity: 1
                        },
                        other: PredSig {
                            symbol: pred!(P),
                            arity: 2
                        }
                    }
                },
                parsed.err().unwrap()
            );
        }
    }
    #[test]
    fn token_type_from_str() {
        assert_eq!(TokenType::from("_COMMA_"), TokenType::Comma);
        assert_eq!(TokenType::from("_DOT_"), TokenType::Dot);
        assert_eq!(TokenType::from("_SEMICOLON_"), TokenType::Semicolon);
        assert_eq!(TokenType::from("_LPAREN_"), TokenType::LParen);
        assert_eq!(TokenType::from("_RPAREN_"), TokenType::RParen);
        assert_eq!(TokenType::from("_EQUAL_"), TokenType::Equal);
        assert_eq!(TokenType::from("_TRUE_"), TokenType::True);
        assert_eq!(TokenType::from("_FALSE_"), TokenType::False);
        assert_eq!(TokenType::from("_NOT_"), TokenType::Not);
        assert_eq!(TokenType::from("_AND_"), TokenType::And);
        assert_eq!(TokenType::from("_OR_"), TokenType::Or);
        assert_eq!(TokenType::from("_IMPLIES_"), TokenType::Implies);
        assert_eq!(TokenType::from("_IFF_"), TokenType::Iff);
        assert_eq!(TokenType::from("_FORALL_"), TokenType::Forall);
        assert_eq!(TokenType::from("_EXISTS_"), TokenType::Exists);
        assert_eq!(TokenType::from("_LOWER_"), TokenType::Lower);
        assert_eq!(TokenType::from("_UPPER_"), TokenType::Upper);
        assert_eq!(TokenType::from("_CONST_"), TokenType::Const);
        assert_eq!(TokenType::from("Bad"), TokenType::Unknown);
    }

    #[test]
    fn token_type_to_string() {
        assert_eq!(TokenType::Comma.to_string(), "`,`");
        assert_eq!(TokenType::Dot.to_string(), "`.`");
        assert_eq!(TokenType::Semicolon.to_string(), "`;`");
        assert_eq!(TokenType::LParen.to_string(), "`(`");
        assert_eq!(TokenType::RParen.to_string(), "`)`");
        assert_eq!(TokenType::Equal.to_string(), "`=`");
        assert_eq!(TokenType::True.to_string(), "`true`");
        assert_eq!(TokenType::False.to_string(), "`false`");
        assert_eq!(TokenType::Not.to_string(), "`not`");
        assert_eq!(TokenType::And.to_string(), "`and`");
        assert_eq!(TokenType::Or.to_string(), "`or`");
        assert_eq!(TokenType::Implies.to_string(), "`implies`");
        assert_eq!(TokenType::Iff.to_string(), "`iff`");
        assert_eq!(TokenType::Forall.to_string(), "`forall`");
        assert_eq!(TokenType::Exists.to_string(), "`exists`");
        assert_eq!(TokenType::Lower.to_string(), "`lowercase identifier`");
        assert_eq!(TokenType::Upper.to_string(), "`uppercase identifier`");
        assert_eq!(TokenType::Const.to_string(), "`constant identifier`");
        assert_eq!(TokenType::Unknown.to_string(), "`unknown token`");
    }

    #[test]
    fn error_message() {
        assert_eq!(
            Error::UnrecognizedToken {
                position: Position {
                    line: 42,
                    column: 11
                },
                expected: vec![],
                found: "Duchess".into()
            }
            .to_string(),
            "found `\"Duchess\"` at line 42, column 11; expecting "
        );
        assert_eq!(
            Error::UnrecognizedToken {
                position: Position {
                    line: 42,
                    column: 11
                },
                expected: vec![TokenType::And],
                found: "Duchess".into()
            }
            .to_string(),
            "found `\"Duchess\"` at line 42, column 11; expecting `and`"
        );
        assert_eq!(
            Error::UnrecognizedToken {
                position: Position{line: 42,
                                   column: 11},
                expected: vec![TokenType::Lower, TokenType::Upper],
                found: "Duchess".into()
            }
            .to_string(),
            "found `\"Duchess\"` at line 42, column 11; expecting `lowercase identifier` or `uppercase identifier`"
        );
        assert_eq!(
            Error::UnrecognizedToken {
                position: Position{line: 42,
                                   column: 11
                },
                expected: vec![TokenType::Upper, TokenType::Lower, TokenType::Implies],
                found: "Duchess".into()
            }
            .to_string(),
            "found `\"Duchess\"` at line 42, column 11; expecting `uppercase identifier`, `lowercase identifier`, or `implies`"
        );
        assert_eq!(
            Error::UnrecognizedEOF {
                position: Position {
                    line: 42,
                    column: 11
                },
                expected: vec![],
            }
            .to_string(),
            "unexpected end of input at line 42, column 11; expecting "
        );
        assert_eq!(
            Error::UnrecognizedEOF {
                position: Position {
                    line: 42,
                    column: 11
                },
                expected: vec![TokenType::Upper],
            }
            .to_string(),
            "unexpected end of input at line 42, column 11; expecting `uppercase identifier`"
        );
        assert_eq!(
            Error::UnrecognizedEOF {
                position: Position{line: 42,
                                   column: 11},
                expected: vec![TokenType::Upper, TokenType::Lower],
            }
            .to_string(),
            "unexpected end of input at line 42, column 11; expecting `uppercase identifier` or `lowercase identifier`"
        );
        assert_eq!(
            Error::UnrecognizedEOF {
                position: Position{line: 42,
                                   column: 11},
                expected: vec![TokenType::Upper, TokenType::Lower, TokenType::Implies],
            }
            .to_string(),
            "unexpected end of input at line 42, column 11; expecting `uppercase identifier`, `lowercase identifier`, or `implies`"
        );
        assert_eq!(
            Error::InvalidToken {
                position: Position {
                    line: 42,
                    column: 11
                }
            }
            .to_string(),
            "invalid token at line 42, column 11"
        );
        assert_eq!(
            Error::ExtraToken {
                position: Position {
                    line: 42,
                    column: 11
                },
                found: "Duchess".into()
            }
            .to_string(),
            "unexpected token `\"Duchess\"` at line 42, column 11"
        );
    }
}
