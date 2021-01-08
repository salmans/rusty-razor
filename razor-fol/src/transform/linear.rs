use super::Relational;
use crate::syntax::{formula::*, symbol::Generator, V};
use std::collections::HashMap;

impl Relational {
    pub fn linear_with(&self, config: &LinearConfig) -> Relational {
        linearize(self, config)
            .into_clauses()
            .into_iter()
            .map(|clause| {
                clause
                    .into_atomics()
                    .into_iter()
                    // remove reflexive equations:
                    .filter(|atomic| match atomic {
                        Atomic::Equals(this) => this.left != this.right,
                        _ => true,
                    })
                    .into()
            })
            .into()
    }

    /// Replaces replaces any varialbe `v` that appears in more than one position of `formula`
    /// with a fresh variable `y` and an atom `=(v, y)` is conjoined with `formula`.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::FOF;
    /// use razor_fol::transform::{RelationalConfig, LinearConfig};
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<FOF>().unwrap();
    /// let gnfs = fof.gnf();
    /// let gnf_head = gnfs[0].head();
    /// let relational = gnf_head.relational();
    /// let linear = relational.linear();
    /// assert_eq!(    
    ///     r"(((($f(x, ?0) ∧ (?0 = ~?0:0)) ∧ P(~?0:0)) ∧ @c(?1)) ∧ (?1 = ~?1:0)) ∧ Q(~?1:0)",
    ///     linear.to_string()
    /// );
    /// ```
    pub fn linear(&self) -> Relational {
        self.linear_with(&LinearConfig::default())
    }
}

/// Is used to expand implicit equations by replacing variables that appear in more than
/// one position of a formula with freshly generated variables. The expansion algorithm
/// is provided by the [`transform`] method.
///
/// [`transform`]: EqualityExpander::transform()
pub struct LinearConfig {
    // Is the [`Generator`] instance used to generate new variable names when variables
    // appear in more than one position.
    equality_generator: Generator,
}

impl LinearConfig {
    /// Use `generator` to distinguish variables that appear in more than one positions.
    pub fn set_equality_generator(&mut self, generator: Generator) {
        self.equality_generator = generator;
    }
}

impl Default for LinearConfig {
    /// Creates a new `EqualityExpander` instance with default generators and symbols:
    /// * The equality symbol is `=`.
    /// * Variables appearing in more than one position are distinguished with `~` as the
    /// prefix, followed by `:` and a unique index.
    fn default() -> Self {
        Self {
            equality_generator: Generator::new().set_prefix("~").set_delimiter(":"),
        }
    }
}

fn linearize(rel: &Relational, config: &LinearConfig) -> Relational {
    let mut vars = HashMap::<V, i32>::new();
    rel.iter()
        .map(|clause| {
            clause
                .iter()
                .flat_map(|atomic| match atomic {
                    Atomic::Atom(this) => {
                        let mut equations = Vec::<Atomic<_>>::new();
                        let mut new_terms = Vec::new();
                        for variable in &this.terms {
                            vars.entry(variable.symbol().clone())
                                .and_modify(|count| {
                                    let new_var = V(config
                                        .equality_generator
                                        .indexed_symbol(variable.0.to_string(), *count));

                                    let left = variable.clone();
                                    let right = new_var.clone().into();

                                    let eq = Equals { left, right }.into();
                                    equations.push(eq);
                                    new_terms.push(new_var.into());
                                    *count += 1;
                                })
                                .or_insert_with(|| {
                                    new_terms.push(variable.clone().into());
                                    0
                                });
                        }
                        equations.push(
                            Atom {
                                predicate: this.predicate.clone(),
                                terms: new_terms,
                            }
                            .into(),
                        );
                        equations
                    }
                    Atomic::Equals(this) => {
                        let mut equations = Vec::<Atomic<_>>::new();
                        let left = &this.left;
                        let right = &this.right;
                        let mut new_left = V("".into());
                        let mut new_right = V("".into());

                        vars.entry(left.symbol().clone())
                            .and_modify(|count| {
                                let new_var = V(config
                                    .equality_generator
                                    .indexed_symbol(left.to_string(), *count));

                                let left = left.clone();
                                let right = new_var.clone().into();

                                let eq = Equals { left, right }.into();
                                equations.push(eq);
                                new_left = new_var.into();
                                *count += 1;
                            })
                            .or_insert_with(|| {
                                new_left = left.symbol().clone();
                                0
                            });

                        vars.entry(right.symbol().clone())
                            .and_modify(|count| {
                                let new_var = V(config
                                    .equality_generator
                                    .indexed_symbol(right.to_string(), *count));

                                let left = right.clone();
                                let right = new_var.clone().into();

                                let eq = Equals { left, right }.into();
                                equations.push(eq);
                                new_right = new_var.into();
                                *count += 1;
                            })
                            .or_insert_with(|| {
                                new_right = right.symbol().clone();
                                0
                            });

                        equations.push(
                            Equals {
                                left: new_left.into(),
                                right: new_right.into(),
                            }
                            .into(),
                        );
                        equations
                    }
                })
                .into()
        })
        .into()
}

#[cfg(test)]
mod tests {
    use crate::{fof, syntax::FOF, transform::PcfSet};

    // Assumes the input in GNF
    fn clause_set(fof: FOF) -> Vec<PcfSet> {
        fof.gnf()
            .into_iter()
            .map(|f| f.into_body_and_head().1)
            .collect()
    }

    fn linear(fof: FOF) -> String {
        let rels = clause_set(fof)
            .iter()
            .map(|f| f.relational().linear())
            .map(FOF::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_linear() {
        // Note: the body of sequents in the tests below are needed to satisfy
        // the requirement that heads of geometric sequents with no free variables
        // in their head gets compressed; otherwise, these tests wouldn't not
        // be interesting.
        assert_eq!("[]", linear(fof!('|')));
        assert_eq!("[false]", linear(fof!(_|_)));
        assert_eq!("[P()]", linear(fof!(P())));
        assert_eq!("[P(x, y)]", linear(fof!(P(x, y))));
        assert_eq!("[(x = ~x:0) & P(x, ~x:0)]", linear(fof!(P(x, x))));
        assert_eq!(
            "[(P(x, y) & (x = ~x:0)) & Q(~x:0)]",
            linear(fof!({P(x, y)} -> {[P(x, y)] & [Q(x)]}))
        );
        assert_eq!(
            "[((P(x, y) & (x = ~x:0)) & (y = ~y:0)) & Q(~x:0, ~y:0)]",
            linear(fof!({P(x, y)} -> {[P(x, y)] & [Q(x, y)]}))
        );
        assert_eq!(
            "[((P(x) & (x = ~x:0)) & (y = ~y:0)) & Q(y, ~x:0, ~y:0)]",
            linear(fof!({P(x, y)} -> {[P(x)] & [Q(y, x, y)]}))
        );
        assert_eq!(
            "[(((P(x) & (x = ~x:0)) & Q(~x:0)) & (x = ~x:1)) & R(~x:1)]",
            linear(fof!([P(x)] -> [{ [P(x)] & [Q(x)] } & { R(x) }]))
        );
        assert_eq!(
            "[P(x, y) | ((x = ~x:0) & Q(~x:0))]",
            linear(fof!({P(x, y)} -> {[P(x, y)] | [Q(x)]}))
        );
        assert_eq!(
            "[P(x, y) | (((x = ~x:0) & (y = ~y:0)) & Q(~x:0, ~y:0))]",
            linear(fof!({P(x, y)} -> {[P(x, y)] | [Q(x, y)]}))
        );
        assert_eq!(
            "[P(x) | (((x = ~x:0) & (y = ~y:0)) & Q(y, ~x:0, ~y:0))]",
            linear(fof!({P(x, y)} -> {[P(x)] | [Q(y, x, y)]}))
        );
        assert_eq!(
            "[(P(x) | ((x = ~x:0) & Q(~x:0))) | ((x = ~x:1) & R(~x:1))]",
            linear(fof!([P(x)] -> [{ [P(x)] | [Q(x)] } | { R(x) }]))
        );
    }
}
