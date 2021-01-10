use super::{RelClause, Relational};
use crate::syntax::{formula::*, Var};

impl Relational {
    /// Given a list of variables `range`, ensures that every variable in `range` appears at
    /// least once in the receiver. This is done by conjoining atomic formulae in the form
    /// of `RR(v)` where `RR` is a "range restriction" predicate with `symbol` as the
    /// predicate symbol. The transformation fails if the `formula` is not relationalized.
    /// The underlying algorithm assumes that the input is negation and quantifier-free;
    /// that is, `¬`, `→`, `⇔`, `∃`, `∀` are not allowed as connectives.
    ///
    /// **Note**: the term "range restriction" is borrowed from the database literature.
    ///
    /// **Example**:
    /// ```rust
    /// use razor_fol::syntax::FOF;
    /// use razor_fol::v;
    ///
    /// let fof = "R(x, y) -> P(x) & Q(y)".parse::<FOF>().unwrap();
    /// let gnfs = fof.gnf();
    /// let gnf_head = gnfs[0].head();
    /// let relational = gnf_head.relational();
    /// let range_restricted = relational.range_restrict(&vec![v!(x), v!(z)], "RR");
    /// assert_eq!(r"(P(x) ∧ Q(y)) ∧ RR(z)", range_restricted.to_string());
    /// ```
    pub fn range_restrict(&self, range: &[Var], symbol: &str) -> Relational {
        self.iter()
            .map(|clause| {
                let free = clause.free_vars();
                let mut range = Vec::from(range);
                range.retain(|x| !free.contains(&x));
                let mut atomics = clause.atomics().to_vec();
                atomics.extend(restrict(&range, symbol).into_atomics());
                atomics.into()
            })
            .into()
    }
}

// Is a helper for `range_restrict` to build range_restriction conjuncts.
#[inline(always)]
fn restrict(range: &[Var], symbol: &str) -> RelClause {
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
        transform::PcfSet,
        v,
    };

    // Assumes the input in GNF
    fn clause_set(fof: FOF) -> Vec<PcfSet> {
        fof.gnf()
            .into_iter()
            .map(|f| f.into_body_and_head().1)
            .collect()
    }

    fn rr(fof: FOF, range: &[Var]) -> String {
        let rels = clause_set(fof)
            .iter()
            .map(|f| f.relational().range_restrict(range, "RR"))
            .map(FOF::from)
            .collect::<Vec<_>>();
        format!("{:?}", rels)
    }

    #[test]
    fn test_range_restrict() {
        assert_eq!("[]", rr(fof!('|'), &vec![]));
        assert_eq!("[]", rr(fof!('|'), &vec![v!(x), v!(y)]));
        assert_eq!("[false]", rr(fof!(_|_), &vec![]));

        assert_eq!("[P(x)]", rr(fof!(P(x)), &vec![]));
        assert_eq!(
            "[P(w, x, y) & RR(z)]",
            rr(fof!(P(w, x, y)), &vec![v!(x), v!(y), v!(z)])
        );

        assert_eq!(
            "[P(x) & Q(y)]",
            rr(fof!({R(x, y)} -> {[P(x)] & [Q(y)]}), &vec![])
        );
        assert_eq!(
            "[((P(v, w) & Q(x)) & RR(y)) & RR(z)]",
            rr(
                fof!({R(v, w, x)} -> {[P(v, w)] & [Q(x)]}),
                &vec![v!(v), v!(w), v!(x), v!(y), v!(z)],
            )
            .to_string()
        );

        assert_eq!(
            "[P(x) | Q(y)]",
            rr(fof!({R(x, y)} -> {[P(x)] | [Q(y)]}), &vec![])
        );

        assert_eq!(
            "[(P(x) & RR(y)) | (Q(y) & RR(x))]",
            rr(fof!([P(x)] | [Q(y)]), &vec![v!(x), v!(y)])
        );
    }
}