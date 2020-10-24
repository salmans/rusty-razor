use super::{
    attribute::AttributeList,
    expression::{and_expression, atomic_expression, or_expression, RawExpression, SubExpression},
    Error, Tuple,
};
use codd::expression::*;
use razor_fol::syntax::Formula;
use std::collections::HashMap;

pub(super) struct ViewMemo<'a> {
    views: HashMap<RawExpression, Mono<Tuple>>,
    database: &'a mut codd::Database,
}

impl<'a> ViewMemo<'a> {
    pub fn new(database: &'a mut codd::Database) -> Self {
        Self {
            views: HashMap::new(),
            database,
        }
    }

    pub fn make_expression(
        &mut self,
        formula: &Formula,
        attributes: &AttributeList,
    ) -> Result<Mono<Tuple>, Error> {
        self.expression(formula, &Vec::new().into(), attributes)
            .map(SubExpression::into_expression)
    }

    fn memoize(&mut self, sub_expr: &mut SubExpression) -> Result<(), codd::Error> {
        if !self.views.contains_key(sub_expr.raw()) {
            let expr = sub_expr.expression().clone();
            let view = self.database.store_view(expr.boxed())?;
            let entry = Mono::from(view);
            self.views.insert(sub_expr.raw().clone(), entry.clone());
            sub_expr.set_expression(entry);
        }
        Ok(())
    }

    fn expression(
        &mut self,
        formula: &Formula,
        join_attr: &AttributeList,
        final_attr: &AttributeList,
    ) -> Result<SubExpression, Error> {
        match formula {
            Formula::Bottom => Ok(SubExpression::new(
                Vec::new().into(),
                |t: &Tuple| t.clone(),
                Mono::from(Empty::new()),
                RawExpression::Empty,
            )),
            Formula::Top => Ok(SubExpression::new(
                Vec::new().into(),
                |t: &Tuple| t.clone(),
                Mono::from(Singleton::new(vec![].into())),
                RawExpression::Full,
            )),
            Formula::Atom { predicate, .. } => {
                let free_vars = formula.free_vars().into_iter().cloned().collect();
                let mut sub = atomic_expression(predicate, &free_vars, &join_attr, &final_attr)?;
                if matches!(sub.raw(), RawExpression::Project {..}) {
                    self.memoize(&mut sub)?;
                }
                Ok(sub)
            }
            Formula::And { left, right } => {
                let mut sub = and_expression(left, right, join_attr, final_attr)?;
                self.memoize(&mut sub)?;
                Ok(sub)
            }

            Formula::Or { left, right } => {
                let mut sub = or_expression(left, right, join_attr, final_attr)?;
                self.memoize(&mut sub)?;
                Ok(sub)
            }
            _ => Err(Error::BadRelationalFormula {
                formula: formula.clone(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chase::{
        r#impl::relational::{attribute::Attribute, expression::make_expression},
        E,
    };
    use codd::{relalg, Database};
    use razor_fol::{formula, v};
    use std::convert::TryFrom;

    macro_rules! atts {
        ($vs:expr) => {{
            let vs: Result<Vec<_>, _> = $vs.iter().map(|v| Attribute::try_from(v)).collect();
            AttributeList::from(vs.unwrap())
        }};
    }

    macro_rules! test_memo {
        ($fmla:expr, $atts: expr, $is_memoized:expr) => {{
            let mut db = setup_database().unwrap();
            let mut memo = ViewMemo::new(&mut db);
            let original = make_expression(&$fmla, &$atts).unwrap();
            let memoized = memo.make_expression(&$fmla, &$atts).unwrap();

            if $is_memoized {
                assert!(matches!(memoized, Mono::View(_)));
                let rememoized = memo.make_expression(&$fmla, &$atts).unwrap();
                match (&memoized, &rememoized) {
                    (Mono::View(ref v1), Mono::View(ref v2)) => {
                        assert_eq!(format!("{:?}", v1), format!("{:?}", v2))
                    }
                    _ => {}
                }
            } else {
                assert!(matches!(memoized, Mono::Relation(_)));
            }

            let original_tuples = db.evaluate(&original).unwrap();
            let memoized_tuples = db.evaluate(&memoized).unwrap();
            assert_eq!(original_tuples, memoized_tuples);
        }};
    }

    fn setup_database() -> Result<Database, Error> {
        let mut db = Database::new();
        let p = relalg! { create relation "P":[Tuple] in db }.unwrap();
        let q = relalg! { create relation "Q":[Tuple] in db }.unwrap();
        let r = relalg! { create relation "R":[Tuple] in db }.unwrap();

        relalg! (insert into (p) values [vec![E(1)], vec![E(2)], vec![E(3)]] in db).unwrap();
        relalg! (insert into (q) values [vec![E(20), E(200)], vec![E(30), E(300)], vec![E(40), E(400)]] in db).unwrap();
        relalg! (insert into (r) values [vec![E(2), E(20)], vec![E(3), E(30)], vec![E(4), E(40)]] in db).unwrap();

        Ok(db)
    }

    #[test]
    fn test_atom() {
        test_memo!(formula!(P(x)), atts!(vec![v!(x)]), false);
        test_memo!(formula!(Q(x, y)), atts!(vec![v!(x), v!(y)]), false);
        test_memo!(formula!(Q(x, y)), atts!(vec![v!(y), v!(x)]), true);
        test_memo!(formula!(Q(x, y)), atts!(vec![v!(x), v!(x)]), true);
    }

    #[test]
    fn test_and() {
        test_memo!(
            formula!([P(x)] & [R(y, z)]),
            atts!(vec![v!(x), v!(y), v!(z)]),
            true
        );
        test_memo!(
            formula!([P(x)] & [R(y, x)]),
            atts!(vec![v!(x), v!(y)]),
            true
        );
        test_memo!(
            formula!([P(x)] & [R(x, y)]),
            atts!(vec![v!(x), v!(y)]),
            true
        );
        test_memo!(
            formula!([P(x)] & [Q(y, z)]),
            atts!(vec![v!(y), v!(x)]),
            true
        );
        test_memo!(
            formula!([P(x)] & [Q(y, z)]),
            atts!(vec![v!(x), v!(y)]),
            true
        );
    }

    #[test]
    fn test_or() {
        test_memo!(
            formula!([Q(x, y)] | [R(y, x)]),
            atts!(vec![v!(x), v!(y)]),
            true
        );
        test_memo!(formula!([Q(x, y)] | [R(y, x)]), atts!(vec![v!(y)]), true);
    }

    #[test]
    fn test_formula() {
        test_memo!(
            formula!({ [P(x)] & [P(x)] } & { P(x) }),
            atts!(vec![v!(x)]),
            true
        );
        test_memo!(
            formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y)] }),
            atts!(vec![v!(x)]),
            true
        );
        test_memo!(
            formula!({ [P(x)] & [P(x)] } & { [P(x)] & [Q(y, z)] }),
            atts!(vec![v!(y), v!(x), v!(z)]),
            true
        );
    }
}
