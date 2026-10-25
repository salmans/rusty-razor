//! Implements a range-restriction algorithm for [`Relational`] formulae.
use super::{FlatClause, Relational};
use crate::syntax::{formula::*, Var};

impl Relational {
    /// Given a list of variables `range`, ensures that every variable in `range` appears at
    /// least once in the formula represented by `self`. This is done by conjoining
    /// atomic formulae in the form of `RR(v)` where `RR` is a "range-restriction" predicate
    /// with `symbol` as the predicate symbol.
    ///
    /// **Note**: the term "range-restricted" is borrowed from the [Alice's book] of
    /// database literature.
    ///    
    /// **Example**:
    /// ```rust
    /// use razor_fol::{syntax::FOF, transform::{ToRelational, PCF}, v};
    ///
    /// let fof = "P(x) & Q(y)".parse::<FOF>().unwrap();
    /// let relational = PCF::try_from(fof).unwrap().relational();
    /// let range_restricted = relational.range_restrict(&vec![v!(x), v!(z)], "RR");
    /// assert_eq!(r"(P(x) ∧ Q(y)) ∧ RR(z)", range_restricted.to_string());
    /// ```
    ///
    /// [Alice's book]: http://webdam.inria.fr/Alice/
    pub fn range_restrict(&self, range: &[Var], symbol: &str) -> Relational {
        self.iter()
            .map(|clause| {
                let free = clause.free_vars();
                let mut range = Vec::from(range);
                range.retain(|x| !free.contains(&x));
                let mut literals = clause.to_vec();
                literals.extend(restrict(&range, symbol).into_literals());
                literals.into()
            })
            .collect()
    }
}

// Is a helper for `range_restrict` to build range_restriction conjuncts.
#[inline(always)]
fn restrict(range: &[Var], symbol: &str) -> FlatClause {
    let mut result = Vec::new();
    for v in range {
        result.push(
            Atom {
                predicate: symbol.into(),
                terms: vec![v.clone().into()],
            }
            .into(),
        );
    }
    result.into()
}

#[cfg(test)]
mod test {
    use crate::{
        fof,
        syntax::{Var, FOF},
        transform::PCF,
        v,
    };

    fn rr(fof: FOF, range: &[Var]) -> String {
        use crate::transform::ToRelational;

        let rels = PCF::disjuncts(fof)
            .iter()
            .map(|f| f.relational().range_restrict(range, "RR"))
            .map(FOF::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_range_restrict() {
        assert_eq!("[true]", rr(fof!('|'), &[]));
        assert_eq!("[RR(x) & RR(y)]", rr(fof!('|'), &[v!(x), v!(y)]));
        assert_eq!("[]", rr(fof!(_ | _), &[]));

        assert_eq!("[P(x)]", rr(fof!(P(x)), &[]));
        assert_eq!(
            "[P(w, x, y) & RR(z)]",
            rr(fof!(P(w, x, y)), &[v!(x), v!(y), v!(z)])
        );

        assert_eq!("[P(x) & Q(y)]", rr(fof!([P(x)] & [Q(y)]), &[]));
        assert_eq!(
            "[((P(v, w) & Q(x)) & RR(y)) & RR(z)]",
            rr(
                fof!([P(v, w)] & [Q(x)]),
                &[v!(v), v!(w), v!(x), v!(y), v!(z)],
            )
            .to_string()
        );

        assert_eq!("[P(x), Q(y)]", rr(fof!([P(x)] | [Q(y)]), &[]));

        assert_eq!(
            "[P(x) & RR(y), Q(y) & RR(x)]",
            rr(fof!([P(x)] | [Q(y)]), &[v!(x), v!(y)])
        );
    }
}
