/*! Implements conversion to Prenex Normal Form (PNF) for formula.*/

use super::TermBased;
use crate::syntax::{Formula::*, *};

// Appends a postfix to the input variable until the result is not no longer in the list of
// no collision variables.
fn rename(variable: &V, no_collision_variables: &Vec<&V>) -> V {
    let mut name = variable.0.clone();
    let names: Vec<&String> = no_collision_variables.into_iter().map(|v| &v.0).collect();
    while names.contains(&&name) {
        name.push_str("`")
    }
    return V::from(&name);
}

// Returns a list of variables that appear in both input lists.
fn shared_variables<'a>(quantifier_vars: &'a Vec<V>, other_vars: &Vec<&V>) -> Vec<&'a V> {
    quantifier_vars
        .iter()
        .filter(|v| other_vars.contains(v))
        .collect()
}

impl Formula {
    /// Returns a Prenex Normal Form (PNF) equivalent to the receiver.
    ///
    /// **Hint**: A PNF is a formula with all quantifiers (existential and universal) and bound
    /// variables at the front, followed by a quantifier-free part.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "Q(x, y) → ∃ x, y. P(x, y)".parse().unwrap();
    /// assert_eq!("∃ x`, y`. (Q(x, y) → P(x`, y`))", formula.pnf().to_string());
    /// ```
    pub fn pnf(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            // e.g. ~(Qx. P(x)) -> Q' x. ~P(x)
            Not { formula } => {
                let formula = formula.pnf();
                match formula {
                    Forall { variables, formula } => exists(variables, not(*formula).pnf()),
                    Exists { variables, formula } => forall(variables, not(*formula).pnf()),
                    _ => not(formula),
                }
            }
            // e.g. (Q x. F(x)) & G(y) => Q x'. F(x') & G(y) or F(x) & (Q y. G(y)) => Q y'. F(x) & G(y')
            And { left, right } => {
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, formula.and(right)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, formula.and(right)).pnf()
                } else if let Forall {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, left.and(formula)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, left.and(formula)).pnf()
                } else {
                    And {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
            }
            // e.g. (Q x. F(x)) | G(y) => Q x'. F(x') | G(y) or F(x) | (Q y. G(y)) => Q y'. F(x) | G(y')
            Or { left, right } => {
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, formula.or(right)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, formula.or(right)).pnf()
                } else if let Forall {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, left.or(formula)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, left.or(formula)).pnf()
                } else {
                    Or {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
            }
            // e.g. (Q x. F(x)) -> G(y) => Q' x'. F(x') -> G(y) or F(x) -> (Q y. G(y)) => Q' y'. F(x) -> G(y')
            Implies { left, right } => {
                let left = left.pnf();
                let right = right.pnf();
                let left_free_variables = left.free_vars();
                let right_free_variables = right.free_vars();
                let mut all_free_variables = right_free_variables.clone();
                all_free_variables.append(&mut left_free_variables.clone());

                if let Forall {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, formula.implies(right)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = left
                {
                    let shared_vars = shared_variables(variables, &right_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, formula.implies(right)).pnf()
                } else if let Forall {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    forall(variables, left.implies(formula)).pnf()
                } else if let Exists {
                    ref variables,
                    ref formula,
                } = right
                {
                    let shared_vars = shared_variables(variables, &left_free_variables);
                    let mut all_vars: Vec<&V> = variables.iter().collect();
                    all_vars.append(&mut all_free_variables);

                    let renaming = |v: &V| {
                        if shared_vars.contains(&v) {
                            rename(v, &all_vars)
                        } else {
                            v.clone()
                        }
                    };
                    let variables: Vec<V> = variables.iter().map(&renaming).collect();
                    let formula = formula.rename_vars(&renaming);
                    exists(variables, left.implies(formula)).pnf()
                } else {
                    Implies {
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
            }
            Iff { left, right } => left
                .clone()
                .implies(*right.clone())
                .and(right.clone().implies(*left.clone()))
                .pnf(),
            Exists { variables, formula } => exists(variables.clone(), formula.pnf()),
            Forall { variables, formula } => forall(variables.clone(), formula.pnf()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_debug_string, formula, pred, term, v, v_1};

    #[test]
    fn test_pnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string!("true", formula.pnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string!("false", formula.pnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string!("P(x)", formula.pnf());
        }

        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string!("x = y", formula.pnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string!("~P(x)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string!("P(x) & Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string!("P(x) | Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string!("P(x) -> Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string!("(P(x) -> Q(y)) & (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "? x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("? x. ((P(x) & (~Q(y))) | R(z))", formula.pnf());
        }
        {
            let formula: Formula = "! x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string!("! x. ((P(x) & (~Q(y))) | R(z))", formula.pnf());
        }
        // sanity checking:
        {
            let formula: Formula = "~? x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (~P(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) & Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) & Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) & Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) & Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) & Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) & Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) & P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) & P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) & ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) & P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) & ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) & P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) & ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) & P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) & ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) & P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) | Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) | Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) | Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) | Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) | Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) | Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) | P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) | P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) | ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) | P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) | ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) | P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) | ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) | P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) | ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) | P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("? x. (P(x) -> Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string!("! x. (P(x) -> Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("? x`. (P(x`) -> Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string!("! x`. (P(x`) -> Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (P(x`, y`) -> Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (P(x`, y`) -> Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x. (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x. (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) -> ! x. P(x)".parse().unwrap();
            assert_debug_string!("! x`. (Q(x) -> P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) -> ? x. P(x)".parse().unwrap();
            assert_debug_string!("? x`. (Q(x) -> P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) -> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("! x`, y`. (Q(x, y) -> P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) -> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!("? x`, y`. (Q(x, y) -> P(x`, y`))", formula.pnf());
        }

        {
            let formula: Formula = "(! x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string!(
                "! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string!(
                "? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string!(
                "? x`, y`. (! x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                formula.pnf(),
            );
        }
        //renaming tests
        assert_debug_string!(
            "! x``, x`. (P(x``) & Q(x))",
            forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .and(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) & Q(x))",
            exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .and(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (P(x``) & Q(x, x`))",
            exists(vec![v!(x)], formula!(P(x)))
                .and(pred!(Q).app(vec![term!(x), v_1!(x).into()]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) & Q(x))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                .and(formula!(Q(x)))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) & P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .and(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) & P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .and(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) & P(x``))",
            pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .and(exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x) & P(x``, x`))",
            pred!(Q)
                .app(vec![term!(x)])
                .and(exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x), v_1!(x).into()]),
                ))
                .pnf(),
        );

        assert_debug_string!(
            "! x``, x`. (P(x``) | Q(x))",
            forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (P(x``) | Q(x))",
            exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (P(x``) | Q(x, x`))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .or(pred!(Q).app(vec![term!(x), v_1!(x).into()]))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (P(x``, x`) | Q(x))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                .or(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) | P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .or(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) | P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .or(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) | P(x``))",
            pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .or(exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x) | P(x``, x`))",
            pred!(Q)
                .app(vec![term!(x)])
                .or(exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x), v_1!(x).into()]),
                ))
                .pnf(),
        );

        assert_debug_string!(
            "? x``, x`. (P(x``) -> Q(x))",
            forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (P(x``) -> Q(x))",
            exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``. (P(x``) -> Q(x, x`))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .implies(pred!(Q).app(vec![term!(x), v_1!(x).into()]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``. (P(x``, x`) -> Q(x))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                .implies(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (Q(x) -> P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .implies(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (Q(x) -> P(x``))",
            pred!(Q)
                .app(vec![term!(x)])
                .implies(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x, x`) -> P(x``))",
            pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .implies(exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (Q(x) -> P(x``, x`))",
            pred!(Q)
                .app(vec![term!(x)])
                .implies(exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x), v_1!(x).into()]),
                ))
                .pnf(),
        );

        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x)]))
                .iff(pred!(Q).app(vec![term!(x), v_1!(x).into()]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
            exists(vec![v!(x)], pred!(P).app(vec![term!(x), v_1!(x).into()]))
                .iff(pred!(Q).app(vec![term!(x)]))
                .pnf(),
        );
        assert_debug_string!(
            "! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pred!(Q)
                .app(vec![term!(x)])
                .iff(forall(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            pred!(Q)
                .app(vec![term!(x)])
                .iff(exists(vec![v!(x), v_1!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
            pred!(Q)
                .app(vec![term!(x), v_1!(x).into()])
                .iff(exists(vec![v!(x)], pred!(P).app(vec![term!(x)])))
                .pnf(),
        );
        assert_debug_string!(
            "? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
            pred!(Q)
                .app(vec![term!(x)])
                .iff(exists(
                    vec![v!(x)],
                    pred!(P).app(vec![term!(x), v_1!(x).into()]),
                ))
                .pnf(),
        );
        // both sides of binary formulae
        {
            let formula: Formula = "(! x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (! x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("? x. (? x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (! x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string!("! x. (? x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string!(
                "! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        // multiple steps
        {
            let formula: Formula = "~~?x.P(x)".parse().unwrap();
            assert_debug_string!("? x. (~(~P(x)))", formula.pnf());
        }
        {
            let formula: Formula = "~~!x.P(x)".parse().unwrap();
            assert_debug_string!("! x. (~(~P(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & ((! x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) & (Q(x`) & R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & ((? x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) & (Q(x`) & R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | ((! x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) | (Q(x`) | R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | ((? x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) | (Q(x`) | R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> ((! x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (P(x) -> (Q(x`) -> R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> ((? x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (P(x) -> (Q(x`) -> R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> ((! x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> ((? x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string!("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", formula.pnf());
        }
        // random formulae
        {
            let formula: Formula = "!x . (P(x) -> ?y . (P(y) & Q(x, y)))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (P(y) & Q(x, y))))", formula.pnf());
        }
        {
            let formula: Formula = "?x . (P(x) & !y . (P(y) -> Q(x, y)))".parse().unwrap();
            assert_debug_string!("? x. (! y. (P(x) & (P(y) -> Q(x, y))))", formula.pnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))".parse().unwrap();
            assert_debug_string!("! x. (? y. (P(x) -> (~(P(y) -> Q(x, y)))))", formula.pnf());
        }
        {
            let formula: Formula = "(P() | ? x. Q(x)) -> !z. R(z)".parse().unwrap();
            assert_debug_string!("! x. (! z. ((P() | Q(x)) -> R(z)))", formula.pnf());
        }
        {
            let formula: Formula = "!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))"
                .parse()
                .unwrap();
            assert_debug_string!(
                "! x. (? y. (! z. (! x`. (! w. ((Q(x) & (~R(x`))) | ((~Q(y)) -> R(y)))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "!x. (!y. P(x, y) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (! y. (? y`. (P(x, y) -> Q(x, y`))))", formula.pnf());
        }
        {
            let formula: Formula = "!x. ((!y. P(x, y)) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string!("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))", formula.pnf());
        }
    }
}
