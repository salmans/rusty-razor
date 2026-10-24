//! Defines the [`Bounder`] on the search that every [`Evaluator`] honours.
//!
//! [`Evaluator`]: crate::chase::Evaluator

/// A bound on the models the chase builds, consulted whenever a model is about to grow.
///
/// The Skolem depth of an element is that of the term that created it: a constant has depth 0
/// and `f(e1, ..., en)` has one more than its deepest argument.
pub trait Bounder: std::fmt::Debug {
    /// May a model of `size` elements grow by an element of Skolem `depth`?
    fn admit(&self, size: usize, depth: u32) -> Admission;
}

/// The verdict of a [`Bounder`] on one new element.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admission {
    /// The element fits.
    Create,
    /// The element reaches the bound: create it and report the model incomplete.
    Overflow,
    /// The element would exceed the depth bound: reuse an existing element instead (controlled
    /// reuse).
    Reuse,
}

/// Bounds nothing: every element is admitted.
#[derive(Clone, Copy, Debug, Default)]
pub struct Unbounded;

impl Bounder for Unbounded {
    fn admit(&self, _size: usize, _depth: u32) -> Admission {
        Admission::Create
    }
}

/// Bounds the number of elements: a model that grows beyond it is reported incomplete.
#[derive(Clone, Copy, Debug)]
pub struct DomainSize(pub usize);

impl Bounder for DomainSize {
    fn admit(&self, size: usize, _depth: u32) -> Admission {
        if size >= self.0 {
            Admission::Overflow
        } else {
            Admission::Create
        }
    }
}

/// What to do when a new element would exceed the depth bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DepthMode {
    /// Create the element anyway and report the model as incomplete (partial model building).
    Pure,
    /// Reuse the deepest argument of the term instead of creating an element, so that models
    /// stay complete within the bound (controlled reuse).
    Reuse,
}

/// Bounds the Skolem depth of elements at `max`; `mode` decides what happens to a deeper one.
#[derive(Clone, Copy, Debug)]
pub struct Depth {
    /// The deepest element admitted.
    pub max: u32,
    /// What to do with an element deeper than `max`.
    pub mode: DepthMode,
}

impl Bounder for Depth {
    fn admit(&self, _size: usize, depth: u32) -> Admission {
        if depth <= self.max {
            return Admission::Create;
        }
        match self.mode {
            DepthMode::Pure => Admission::Overflow,
            DepthMode::Reuse => Admission::Reuse,
        }
    }
}
