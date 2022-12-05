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
    /// # use std::convert::TryFrom;
    /// use razor_fol::{syntax::Fof, transform::{Gnf, ToRelational}, v};
    ///
    /// let fof = "R(x, y) -> P(x) & Q(y)".parse::<Fof>().unwrap();
    /// let gnf = Gnf::try_from(fof).unwrap();
    /// let gnf_head = gnf.head();
    /// let relational = gnf_head.relational();
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
                let mut literals = clause.literals().to_vec();
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
        syntax::{Fof, Var},
        transform::PcfSet,
        v,
    };

    // Assumes the input in GNF
    fn clause_set(fof: Fof) -> PcfSet {
        use std::convert::TryFrom;

        PcfSet::try_from(fof).unwrap()
    }

    fn rr(fof: Fof, range: &[Var]) -> String {
        use crate::transform::ToRelational;

        let rels = clause_set(fof)
            .iter()
            .map(|f| f.relational().range_restrict(range, "RR"))
            .map(Fof::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_range_restrict() {
        assert_eq!("[true]", rr(fof!('|'), &vec![]));
        assert_eq!("[RR(x) & RR(y)]", rr(fof!('|'), &vec![v!(x), v!(y)]));
        assert_eq!("[]", rr(fof!(_ | _), &vec![]));

        assert_eq!("[P(x)]", rr(fof!(P(x)), &vec![]));
        assert_eq!(
            "[P(w, x, y) & RR(z)]",
            rr(fof!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)])
        );

        assert_eq!("[P(x) & Q(y)]", rr(fof!([P(x)] & [Q(y)]), &vec![]));
        assert_eq!(
            "[((P(v, w) & Q(x)) & RR(y)) & RR(z)]",
            rr(
                fof!([P(v, w)] & [Q(x)]),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)],
            )
            .to_string()
        );

        assert_eq!("[P(x), Q(y)]", rr(fof!([P(x)] | [Q(y)]), &vec![]));

        assert_eq!(
            "[P(x) & RR(y), Q(y) & RR(x)]",
            rr(fof!([P(x)] | [Q(y)]), &vec![v!(x), v!(y)])
        );
    }
}
