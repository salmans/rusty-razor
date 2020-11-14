use super::Error;
use crate::chase::{r#impl::basic::WitnessTerm, Observation, Rel, WitnessTermTrait, E};
use razor_fol::syntax;

/// Is the symbol associated to a relational instance.
#[derive(Hash, PartialEq, Eq, Clone, PartialOrd, Ord, Debug)]
pub(super) enum Symbol {
    /// Constant symbol
    Const(syntax::C),

    /// Function symbol
    Func { symbol: syntax::F, arity: u8 },

    /// Predicate symbol
    Pred { symbol: syntax::Pred, arity: u8 },

    /// Equality symbol
    Equality,

    /// Domain of elements
    Domain,
}

impl Symbol {
    /// Creates a witness term from the receiver symbol, given a list of arguments `E`.
    pub fn witness(&self, args: &[E]) -> Result<WitnessTerm, Error> {
        match self {
            Symbol::Const(symbol) => {
                assert!(args.is_empty());
                Ok(symbol.clone().into())
            }
            Symbol::Func { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);

                let witness = symbol
                    .clone()
                    .app(args.iter().map(|e| e.clone().into()).collect());
                Ok(witness)
            }
            _ => Err(Error::BadWitnessTerm {
                symbol: self.to_string(),
            }),
        }
    }

    /// Creates an observation from the receiver symbol with a slice of `E` as arguments.
    pub fn observation(&self, args: &[E]) -> Option<Observation<WitnessTerm>> {
        match self {
            Symbol::Pred { symbol, arity } => {
                assert_eq!(args.len() as u8, *arity);
                Some(
                    Rel::from(symbol.clone())
                        .app(args.iter().map(|e| WitnessTerm::from(*e)).collect()),
                )
            }
            Symbol::Equality => {
                assert_eq!(args.len(), 2);
                Some(WitnessTerm::from(args[0]).equals(args[1].into()))
            }
            Symbol::Const(c) => {
                assert_eq!(args.len(), 1);
                Some(WitnessTerm::from(c.clone()).equals(WitnessTerm::from(args[0])))
            }
            Symbol::Func { symbol, ref arity } => {
                assert_eq!(args.len() as u8, arity + 1);
                let last = args[*arity as usize];
                let app = symbol.clone().app(
                    args[0..(*arity as usize)]
                        .iter()
                        .map(WitnessTerm::from)
                        .collect(),
                );
                Some(app.equals(last.into()))
            }
            Symbol::Domain => None, // the Domain instance is used only for book-keeping
        }
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let display = match self {
            Symbol::Const(c) => format!("constant {}", c.to_string()),
            Symbol::Func { symbol, arity } => {
                format!("function {}, arity {}", symbol.to_string(), arity)
            }
            Symbol::Pred { symbol, arity } => {
                format!("predicate {}, arity {}", symbol.to_string(), arity)
            }
            Symbol::Equality => "equality (=)".into(),
            Symbol::Domain => "domain".into(),
        };
        write!(f, "{}", display)
    }
}
