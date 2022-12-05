//! Implements an algorithm for linearizing [`Relational`] formulae.

use super::Relational;
use crate::syntax::{formula::*, term::Variable, Var};
use std::collections::HashMap;

impl Relational {
    /// Is similar to [`Relational::linear`] but uses a custom closure to create new variable
    /// terms, resulting from removing variables that appear in multiple positions of `self`.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// # use std::convert::TryFrom;
    /// use razor_fol::transform::{Gnf, ToRelational};
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<Fof>().unwrap();
    /// let gnf = Gnf::try_from(fof).unwrap();
    /// let gnf_head = gnf.head();
    /// let relational = gnf_head.relational();
    /// let mut generator = |name: &str, count| format!("V:{}:{}", name, count).into();    
    /// let linear = relational.linear_with(&mut generator);
    /// assert_eq!(    
    ///     r"(((($f(x, ?0) ∧ ?0 = V:?0:0) ∧ P(V:?0:0)) ∧ @c(?1)) ∧ ?1 = V:?1:0) ∧ Q(V:?1:0)",
    ///     linear.to_string()
    /// );
    /// ```    
    pub fn linear_with<G>(&self, generator: &mut G) -> Relational
    where
        G: FnMut(&str, u32) -> Var,
    {
        linearize(self, generator)
            .into_clauses()
            .into_iter()
            .map(|clause| {
                clause
                    .into_literals()
                    .into_iter()
                    // remove reflexive equations:
                    .filter(|atomic| {
                        if let Atomic::Equals(this) = atomic {
                            this.left != this.right
                        } else {
                            true
                        }
                    })
                    .collect()
            })
            .collect()
    }

    /// Returns a new [`Relational`] instance, resulting from replacing any varialbe `v` that
    /// appears in more than one position of `self` with a fresh variable `y` and
    /// conjoined with an equation `v = y`.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Fof;
    /// # use std::convert::TryFrom;
    /// use razor_fol::transform::{Gnf, ToRelational};
    ///
    /// let fof = "P(x) -> P(f(x)) & Q('c)".parse::<Fof>().unwrap();
    /// let gnf = Gnf::try_from(fof).unwrap();
    /// let gnf_head = gnf.head();
    /// let relational = gnf_head.relational();
    /// let linear = relational.linear();
    /// assert_eq!(    
    ///     r"(((($f(x, ?0) ∧ ?0 = ~?0:0) ∧ P(~?0:0)) ∧ @c(?1)) ∧ ?1 = ~?1:0) ∧ Q(~?1:0)",
    ///     linear.to_string()
    /// );
    /// ```
    pub fn linear(&self) -> Relational {
        let mut generator = |name: &str, count| format!("~{}:{}", name, count).into();
        self.linear_with(&mut generator)
    }
}

// A helper to generate new fresh variable terms and equations to extend the original formula.
fn make_equations<G>(
    vars: &mut HashMap<Var, u32>,
    terms: &[Variable],
    generator: &mut G,
) -> (Vec<Atomic<Variable>>, Vec<Variable>)
where
    G: FnMut(&str, u32) -> Var,
{
    let mut equations = Vec::<Atomic<_>>::new();
    let mut new_terms = Vec::new();
    for variable in terms {
        vars.entry(variable.symbol().clone())
            .and_modify(|count| {
                let new_var: Var = generator(variable.name(), *count);

                let left = variable.clone();
                let right = new_var.clone().into();

                equations.push(Equals { left, right }.into());
                new_terms.push(new_var.into());
                *count += 1;
            })
            .or_insert_with(|| {
                new_terms.push(variable.clone());
                0
            });
    }
    (equations, new_terms)
}

fn linearize<G>(rel: &Relational, generator: &mut G) -> Relational
where
    G: FnMut(&str, u32) -> Var,
{
    let mut vars = HashMap::<Var, u32>::new();
    rel.iter()
        .map(|clause| {
            clause
                .iter()
                .flat_map(|atomic| match atomic {
                    Atomic::Atom(this) => {
                        let (mut equations, new_terms) =
                            make_equations(&mut vars, &this.terms, generator);
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
                        // left at index 0 and right at index 1:
                        let (mut equations, mut new_terms) = make_equations(
                            &mut vars,
                            &[this.left.clone(), this.right.clone()],
                            generator,
                        );
                        assert_eq!(2, new_terms.len());

                        equations.push(
                            Equals {
                                left: new_terms.remove(0),
                                right: new_terms.remove(0),
                            }
                            .into(),
                        );
                        equations
                    }
                })
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::{fof, syntax::Fof, transform::PcfSet};

    // Assumes the input in GNF
    fn clause_set(fof: Fof) -> PcfSet {
        use std::convert::TryFrom;

        PcfSet::try_from(fof).unwrap()
    }

    fn linear(fof: Fof) -> String {
        use crate::transform::ToRelational;

        let rels = clause_set(fof)
            .iter()
            .map(|f| f.relational().linear())
            .map(Fof::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_linear() {
        assert_eq!("[true]", linear(fof!('|')));
        assert_eq!("[]", linear(fof!(_ | _)));
        assert_eq!("[P()]", linear(fof!(P())));
        assert_eq!("[P(x, y)]", linear(fof!(P(x, y))));
        assert_eq!("[x = ~x:0 & P(x, ~x:0)]", linear(fof!(P(x, x))));
        assert_eq!(
            "[(P(x, y) & x = ~x:0) & Q(~x:0)]",
            linear(fof!([P(x, y)] & [Q(x)]))
        );
        assert_eq!(
            "[((P(x, y) & x = ~x:0) & y = ~y:0) & Q(~x:0, ~y:0)]",
            linear(fof!([P(x, y)] & [Q(x, y)]))
        );
        assert_eq!(
            "[((P(x) & x = ~x:0) & y = ~y:0) & Q(y, ~x:0, ~y:0)]",
            linear(fof!([P(x)] & [Q(y, x, y)]))
        );
        assert_eq!(
            "[(((P(x) & x = ~x:0) & Q(~x:0)) & x = ~x:1) & R(~x:1)]",
            linear(fof!({ [P(x)] & [Q(x)] } & { R(x) }))
        );
        assert_eq!("[P(x, y), Q(x)]", linear(fof!([P(x, y)] | [Q(x)])));
        assert_eq!("[P(x, y), Q(x, y)]", linear(fof!([P(x, y)] | [Q(x, y)])));
        assert_eq!(
            "[P(x), y = ~y:0 & Q(y, x, ~y:0)]",
            linear(fof!([P(x)] | [Q(y, x, y)]))
        );
        assert_eq!(
            "[P(x), Q(x), R(x)]",
            linear(fof!({ [P(x)] | [Q(x)] } | { R(x) }))
        );
    }
}
