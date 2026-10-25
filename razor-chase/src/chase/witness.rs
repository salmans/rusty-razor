//! The witnesses that name the elements the chase creates for fresh existentials.
use razor_fol::{syntax::Var, transform::Symbols};
use std::fmt;

/// Names the elements the chase creates for one existential of a head, one per assignment of
/// the universals it depends on. A witness is its identity alone: it has no symbol, takes no part
/// in any truth test, and never shares a key with a function of the theory.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Witness {
    kind: Kind,
    index: usize,
}

/// Whether a witness depends on no universal or on some, which decides how it displays.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Kind {
    Constant,
    Function,
}

/// Displays a witness as the Skolem symbol the conversion to geometric form would introduce in
/// its place: `'c#N` when it depends on no universal and `f#N` otherwise, numbered after the
/// Skolem constants and functions the conversion introduced. A displayed `c#N` or `f#N` of a
/// witness is never a symbol of the theory: it is display only, and never parsed or looked up.
impl fmt::Display for Witness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            Kind::Constant => write!(f, "'c#{}", self.index),
            Kind::Function => write!(f, "f#{}", self.index),
        }
    }
}

/// Where a witness was introduced in the sequent that holds it: an existential of a head
/// disjunct, applied to the universals it depends on.
#[derive(Clone, Debug)]
pub struct Origin {
    /// The witness introduced here.
    pub witness: Witness,
    /// The existential the witness names elements for.
    pub existential: Var,
    /// The universals the existential depends on, in the order of the witness's arguments.
    pub args: Vec<Var>,
}

/// Hands out the witnesses of a theory's head existentials, in the order of its sequents, their
/// disjuncts and their existentials.
#[derive(Debug)]
pub(crate) struct Witnesses {
    constants: usize,
    functions: usize,
}

impl Witnesses {
    /// Hands out witnesses that display after the Skolem symbols `symbols` introduced.
    pub(crate) fn new(symbols: &Symbols) -> Self {
        Self {
            constants: symbols.constants(),
            functions: symbols.functions(),
        }
    }

    /// Introduces a witness no other existential has, for `existential` over `args`.
    pub(crate) fn fresh(&mut self, existential: Var, args: Vec<Var>) -> Origin {
        let (kind, counter) = if args.is_empty() {
            (Kind::Constant, &mut self.constants)
        } else {
            (Kind::Function, &mut self.functions)
        };
        let witness = Witness {
            kind,
            index: *counter,
        };
        *counter += 1;
        Origin {
            witness,
            existential,
            args,
        }
    }
}
