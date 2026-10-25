//! The relational chase: models are `codd` databases, sequents are incrementally maintained
//! views of their *active triggers*, and equality is a union-find over elements.
//!
//! * A model is a database of canonical tuples together with a persistent union-find over its
//!   elements and a table of function applications. Every structure is persistent, so forking a
//!   model is cheap.
//! * The active triggers of a sequent (the `body` environments for which no head disjunct holds)
//!   are a stored antijoin view, maintained incrementally as the model grows or merges elements.
//! * Equality is not a relation. A head equation merges two classes and rewrites the tuples that
//!   mention the loser. Repeated body variables are plain selections and joins, so no sequent
//!   joins through an equality table.
//! * Functions and constants are relations `$f(x̄, y)` and `@c(y)`, and functionality is
//!   enforced when a fact is inserted: a second output for the same arguments is merged with
//!   the first.
//! * A head disjunct's truth test asks only that some elements satisfy it, which makes the
//!   chase the restricted chase. When none do, an existential that a function application of
//!   the disjunct outputs is that application's value, and any other is created and named by a
//!   *witness* the compiler introduces for it, which has no relation: only the table of function
//!   applications records it, keyed by the witness's identity.
//! * A symbol or variable the prover introduces is recorded where it is introduced (the symbols
//!   of the conversion to geometric form by one `Symbols` per theory, witnesses with the
//!   existential they come from by the compiled sequent that introduces them, placeholders and
//!   function relations by the compilation of a sequent) and looked up there; its name only
//!   displays it and is never parsed.
//! * A sequent with one disjunct fires on each of its current triggers in turn, and skips the
//!   triggers that an earlier firing in the same step already satisfied. A disjunctive
//!   sequent fires on one trigger and forks the model once per disjunct.
//! * The search can be bounded by domain size or by the Skolem depth of elements. Under a depth
//!   bound, *controlled reuse* keeps models complete within the bound.
//!
//! The modules mirror the framework: `sequent` compiles a sequent, `model` holds a model,
//! `evaluator` runs a chase step and `pre_processor` turns a theory into both; `union_find` is
//! the union-find they share.
mod evaluator;
mod model;
mod pre_processor;
mod sequent;
#[cfg(test)]
mod tests;
mod union_find;

pub use evaluator::RelEvaluator;
pub use model::RelModel;
pub use pre_processor::RelPreProcessor;
pub use sequent::RelSequent;

use crate::chase::{r#impl::basic::BasicWitnessTerm, Witness, E};
use codd::expression::{Mono, View};
use razor_fol::syntax::{Const, Func, Pred};

/// Tuples of elements stored in the database.
pub type Tuple = Vec<E>;

/// A stored view over tuples of elements.
pub type ViewExpr = View<Tuple, Mono<Tuple>>;

/// Symbols of the signature as stored in the database.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Symbol {
    /// A predicate of the theory.
    Pred(Pred),
    /// A function of the theory (or a Skolem function); stored with its output as the last
    /// column.
    Func(Func),
    /// A constant of the theory (or a Skolem constant); stored as a unary relation.
    Const(Const),
    /// The domain of the model.
    Domain,
}

/// What a function application applies, and the key of its entries in a model's table of
/// applications.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Function {
    /// A function or constant of the database, whose applications are facts.
    Symbol(Symbol),
    /// A witness, whose applications only name the elements it creates.
    Witness(Witness),
}

impl Symbol {
    /// The name of the database relation for this symbol: a key into the database, never
    /// parsed back into the symbol.
    pub fn relation_name(&self) -> String {
        match self {
            Symbol::Pred(p) => p.name().to_string(),
            Symbol::Func(f) => format!("${}", f.name()),
            Symbol::Const(c) => format!("@{}", c.name()),
            Symbol::Domain => "$$domain".to_string(),
        }
    }
}

impl Function {
    /// The witness term of the application of this function to `args`.
    pub fn term(&self, args: &[E]) -> BasicWitnessTerm {
        let terms = || args.iter().map(|a| BasicWitnessTerm::Elem(*a)).collect();
        match self {
            Function::Symbol(Symbol::Const(c)) => BasicWitnessTerm::Const(c.clone()),
            Function::Symbol(Symbol::Func(f)) => BasicWitnessTerm::App {
                function: f.clone(),
                terms: terms(),
            },
            Function::Witness(witness) => BasicWitnessTerm::Witness {
                witness: *witness,
                terms: terms(),
            },
            Function::Symbol(_) => unreachable!("only functions and constants are applied"),
        }
    }
}
