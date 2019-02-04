use crate::chase::chase::*;
use crate::formula::syntax::*;
use std::collections::HashSet;
use std::collections::HashMap;
use std::fmt;
use itertools::Either;
use itertools::Itertools;

#[derive(Clone)]
pub struct BasicModel {
    element_index: i32,
    rewrites: HashMap<WitnessTerm, E>,
    facts: HashSet<Observation>,
}

impl BasicModel {
    pub fn new() -> BasicModel {
        BasicModel {
            element_index: 0,
            rewrites: HashMap::new(),
            facts: HashSet::new(),
        }
    }

    fn record(&mut self, witness: WitnessTerm) -> E {
        match witness {
            WitnessTerm::Elem { element } => {
                if self.domain().contains(&element) {
                    element
                } else {
                    panic!("Element does not exist in the model's domain!")
                }
            }
            WitnessTerm::Const { .. } => {
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    let element = E(self.element_index);
                    self.element_index = self.element_index + 1;
                    self.rewrites.insert(witness, element.clone());
                    element
                }
            }
            WitnessTerm::App { function, terms } => {
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record(t).into()).collect();
                let witness = WitnessTerm::App { function, terms };
                if let Some(e) = self.rewrites.get(&witness) {
                    (*e).clone()
                } else {
                    let element = E(self.element_index);
                    self.element_index = self.element_index + 1;
                    self.rewrites.insert(witness, element.clone());
                    element
                }
            }
        }
    }
}

impl Model for BasicModel {
    fn domain(&self) -> HashSet<&E> {
        self.rewrites.values().collect()
    }

    fn facts(&self) -> HashSet<&Observation> {
        self.facts.iter().collect()
    }

    fn observe(&mut self, observation: &Observation) {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<WitnessTerm> = terms.into_iter().map(|t| self.record((*t).clone()).into()).collect();
                let observation = Observation::Fact { relation: (*relation).clone(), terms };
                self.facts.insert(observation);
            }
            Observation::Identity { left, right } => {
                let left = self.record((*left).clone());
                let right = self.record((*right).clone());
                let (src, dest) = if left > right {
                    (right, left)
                } else {
                    (left, right)
                };
                self.rewrites.values_mut().for_each(|v| {
                    if v == &dest {
                        v.identify(&src);
                    }
                });
                // TODO: by maintaining references to elements, the following can be avoided:
                self.facts = self.facts.iter().map(|f| {
                    if let Observation::Fact { ref relation, ref terms } = f {
                        let terms: Vec<WitnessTerm> = terms.iter().map(|t| {
                            if let WitnessTerm::Elem { element } = t {
                                if element == &dest {
                                    src.clone().into()
                                } else {
                                    (*t).clone()
                                }
                            } else {
                                (*t).clone() // should never happen
                            }
                        }).collect();
                        Observation::Fact { relation: relation.clone(), terms }
                    } else {
                        f.clone() // should never happen
                    }
                }).collect();
            }
        }
    }

    fn is_observed(&self, observation: &Observation) -> bool {
        match observation {
            Observation::Fact { relation, terms } => {
                let terms: Vec<Option<E>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    false
                } else {
                    let terms: Vec<WitnessTerm> = terms.into_iter().map(|e| e.unwrap().into()).collect();
                    self.facts.contains(&Observation::Fact { relation: (*relation).clone(), terms })
                }
            }
            Observation::Identity { left, right } => {
                let left = self.element(left);
                left.is_some() && left == self.element(right)
            }
        }
    }

    fn witness(&self, element: &E) -> HashSet<&WitnessTerm> {
        self.rewrites.iter()
            .filter(|(t, e)| *e == element)
            .map(|(t, _)| t)
            .collect()
    }

    fn element(&self, witness: &WitnessTerm) -> Option<E> {
        match witness {
            WitnessTerm::Elem { element } => {
                if self.domain().contains(element) { Some((*element).clone()) } else { None }
            }
            WitnessTerm::Const { .. } => self.rewrites.get(witness).map(|e| (*e).clone()),
            WitnessTerm::App { function, terms } => {
                let terms: Vec<Option<E>> = terms.iter().map(|t| self.element(t)).collect();
                if terms.iter().any(|e| e.is_none()) {
                    None
                } else {
                    let terms: Vec<WitnessTerm> = terms.into_iter().map(|e| e.unwrap().into()).collect();
                    self.rewrites.get(&WitnessTerm::App { function: (*function).clone(), terms }).map(|e| (*e).clone())
                }
            }
        }
    }
}

impl fmt::Display for BasicModel {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let domain: Vec<String> = self.domain().into_iter().map(|e| e.to_string()).collect();
        let facts: Vec<String> = self.facts().into_iter().map(|e| e.to_string()).collect();
        write!(f, "Domain: {{{}}}\nFacts: {}\n", domain.join(", "), facts.join(", "))
    }
}

#[derive(Clone)]
pub enum Literal {
    Atm { predicate: Pred, terms: Terms },
    Eql { left: Term, right: Term },
}

impl Literal {
    fn build_body(formula: &Formula) -> Vec<Literal> {
        match formula {
            Formula::Top => vec![],
            Formula::Atom { predicate, terms } =>
                vec![Literal::Atm { predicate: predicate.clone(), terms: terms.to_vec() }],
            Formula::Equals { left, right } =>
                vec![Literal::Eql { left: left.clone(), right: right.clone() }],
            Formula::And { left, right } => {
                let mut left = Literal::build_body(left);
                let mut right = Literal::build_body(right);
                left.append(&mut right);
                left
            }
            _ => panic!("Expecting a geometric sequent in standard form.")
        }
    }

    fn build_head(formula: &Formula) -> Vec<Vec<Literal>> {
        match formula {
            Formula::Top => vec![vec![]],
            Formula::Bottom => vec![],
            Formula::Atom { predicate, terms } =>
                vec![vec![Literal::Atm { predicate: predicate.clone(), terms: terms.to_vec() }]],
            Formula::Equals { left, right } =>
                vec![vec![Literal::Eql { left: left.clone(), right: right.clone() }]],
            Formula::And { left, right } => {
                let mut left = Literal::build_head(left);
                let mut right = Literal::build_head(right);
                if left.is_empty() {
                    left
                } else if right.is_empty() {
                    right
                } else if left.len() == 1 && right.len() == 1 {
                    let mut left = left.remove(0);
                    let mut right = right.remove(0);
                    left.append(&mut right);
                    vec![left]
                } else {
                    panic!("Expecting a geometric sequent in standard form.")
                }
            }
            Formula::Or { left, right } => {
                let mut left = Literal::build_head(left);
                let mut right = Literal::build_head(right);
                left.append(&mut right);
                left
            }
            _ => panic!("Expecting a geometric sequent in standard form.")
        }
    }
}

impl<'t> fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Literal::Atm { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate, ts.join(", "))
            }
            Literal::Eql { left, right } => write!(f, "{} = {}", left, right),
        }
    }
}

#[derive(Clone)]
pub struct BasicSequent {
    pub free_vars: Vec<V>,
    body: Formula,
    head: Formula,
    pub body_literals: Vec<Literal>,
    pub head_literals: Vec<Vec<Literal>>,
}

impl From<&Formula> for BasicSequent {
    fn from(formula: &Formula) -> Self {
        match formula {
            Formula::Implies { left, right } => {
                let free_vars: Vec<V> = formula.free_vars().into_iter().map(|v| v.clone()).collect();
                let body_literals = Literal::build_body(left);
                let head_literals = Literal::build_head(right);
                let body = *left.clone();
                let head = *right.clone();
                BasicSequent { free_vars, body, head, body_literals, head_literals }
            }
            _ => panic!("Expecting a geometric sequent in standard form.")
        }
    }
}

impl fmt::Display for BasicSequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let body: Vec<String> = self.body_literals.iter().map(|l| l.to_string()).collect();
        let head: Vec<String> =
            self.head_literals.iter().map(|ls| {
                let ls: Vec<String> = ls.iter().map(|l| l.to_string()).collect();
                format!("[{}]", ls.join(", "))
            }).collect();
        write!(f, "[{}] -> [{}]", body.join(", "), head.join(", "))
    }
}

impl Sequent for BasicSequent {
    fn body(&self) -> Formula {
        self.body.clone()
    }

    fn head(&self) -> Formula {
        self.head.clone()
    }
}

pub struct BasicEvaluator {}

impl Term {
    fn to_witness(&self, wit: &impl Fn(&V) -> E) -> WitnessTerm {
        match self {
            Term::Const { constant } => WitnessTerm::Const { constant: constant.clone() },
            Term::Var { variable } => WitnessTerm::Elem { element: wit(&variable) },
            Term::App { function, terms } => {
                let terms = terms.iter().map(|t| t.to_witness(wit)).collect();
                WitnessTerm::App { function: function.clone(), terms }
            }
        }
    }
}


impl<Sel: Selector<Item=BasicSequent>, B: Bounder> Evaluator<BasicSequent, BasicModel, Sel, B> for BasicEvaluator {
    fn evaluate(&self, model: &BasicModel, selector: Sel, bounder: Option<&B>)
                -> Option<Vec<Either<BasicModel, BasicModel>>> {
        use itertools::Itertools;
        let domain: Vec<&E> = model.domain().into_iter().collect();
        let domain_size = domain.len();
        for sequent in selector {
            let sequent_vars = sequent.free_vars;
            let sequent_size = sequent_vars.len();
            let end = usize::pow(domain_size, sequent_size as u32);
            for i in 0..end {
                let mut wit_map: HashMap<&V, E> = HashMap::new();
                let mut j: usize = 0;
                let mut total = i;
                while j < sequent_size {
                    wit_map.insert(sequent_vars.get(j).unwrap(), (*domain.get(total % domain_size).unwrap()).clone());
                    j += 1;
                    total /= domain_size;
                }
                let witness_func = |v: &V| wit_map.get(v).unwrap().clone();
                let convert = |lit: &Literal| {
                    match lit {
                        Literal::Atm { predicate, terms } => {
                            let terms = terms.into_iter().map(|t| t.to_witness(&witness_func)).collect();
                            Observation::Fact { relation: Rel(predicate.0.clone()), terms }
                        }
                        Literal::Eql { left, right } => {
                            let left = left.to_witness(&witness_func);
                            let right = right.to_witness(&witness_func);
                            Observation::Identity { left, right }
                        }
                    }
                };

                let body: Vec<Observation> = sequent.body_literals.iter().map(convert).collect();
                let head: Vec<Vec<Observation>> = sequent.head_literals.iter().map(|l| l.iter().map(convert).collect()).collect();

                if body.iter().all(|o| model.is_observed(o))
                    && !head.iter().any(|os| os.iter().all(|o| model.is_observed(o))) {
                    if head.is_empty() {
                        return None; // failure
                    } else {
                        return head.iter().map(|os| {
                            let mut model = model.clone();
                            os.iter().foreach(|o| model.observe(o));
                            // this evaluator returns the models from first successful sequent
                            if let Some(bounder) = bounder {
                                if os.iter().any(|o| bounder.bound(&model, o)) {
                                    Some(Either::Right(model))
                                } else {
                                    Some(Either::Left(model))
                                }
                            } else {
                                Some(Either::Left(model))
                            }
                        }).collect();
                    }
                }
            }
        }
        Some(Vec::new())
    }
}


#[cfg(test)]
mod test_basic {
    use super::*;
    use crate::test_prelude::*;
    use std::iter::FromIterator;
    use crate::formula::parser::parse_formula;
    use crate::formula::parser::parse_theory;
    use crate::chase::selector::TopDown;
    use crate::chase::strategy::FIFO;
    use crate::chase::bounder::DomainSize;

    #[test]
    fn test_empty_model() {
        let model = BasicModel::new();
        assert_eq!(HashSet::new(), model.domain());
        assert_eq!(HashSet::new(), model.facts());
    }

    #[test]
    fn test_observe() {
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app0());
            assert_eq!(HashSet::from_iter(vec![_R_().app0()].iter()), model.facts());
            assert!(model.is_observed(&_R_().app0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(_c_()));
            assert_eq!(HashSet::from_iter(vec![&e_0()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app1(_e_0())].iter()), model.facts());
            assert!(model.is_observed(&_R_().app1(_c_())));
            assert!(model.is_observed(&_R_().app1(_e_0())));
            assert!(!model.is_observed(&_R_().app1(_e_1())));
            assert_eq!(HashSet::from_iter(vec![&_c_()]), model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_b_()));
            assert_eq!(HashSet::from_iter(vec![&e_0()]), model.domain());
            assert_eq!(HashSet::new(), model.facts());
            assert_eq!(HashSet::from_iter(vec![&_a_(), &_b_()]), model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_a_().equals(_a_()));
            assert_eq!(HashSet::from_iter(vec![&e_0()]), model.domain());
            assert_eq!(HashSet::new(), model.facts());
            assert_eq!(HashSet::from_iter(vec![&_a_()]), model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_P_().app1(_a_()));
            model.observe(&_Q_().app1(_b_()));
            model.observe(&_a_().equals(_b_()));
            assert_eq!(HashSet::from_iter(vec![&e_0()]), model.domain());
            assert_eq!(HashSet::from_iter(
                vec![_P_().app1(_e_0()), _Q_().app1(_e_0())].iter()), model.facts());
            assert!(model.is_observed(&_P_().app1(_e_0())));
            assert!(model.is_observed(&_P_().app1(_a_())));
            assert!(model.is_observed(&_P_().app1(_b_())));
            assert!(model.is_observed(&_Q_().app1(_e_0())));
            assert!(model.is_observed(&_Q_().app1(_a_())));
            assert!(model.is_observed(&_Q_().app1(_b_())));
            assert_eq!(HashSet::from_iter(vec![&_a_(), &_b_()]), model.witness(&e_0()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app1(f().wit_app1(_c_())));
            assert_eq!(HashSet::from_iter(vec![&e_0(), &e_1()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app1(_e_1())].iter()), model.facts());
            assert!(model.is_observed(&_R_().app1(_e_1())));
            assert!(model.is_observed(&_R_().app1(f().wit_app1(_c_()))));
            assert_eq!(HashSet::from_iter(vec![&_c_()]), model.witness(&e_0()));
            assert_eq!(HashSet::from_iter(vec![&f().wit_app1(_e_0())]), model.witness(&e_1()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(_a_(), _b_()));
            assert_eq!(HashSet::from_iter(vec![&e_0(), &e_1()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app2(_e_0(), _e_1())].iter()), model.facts());
            assert!(model.is_observed(&_R_().app2(_e_0(), _e_1())));
            assert!(!model.is_observed(&_R_().app2(_e_0(), _e_0())));
            assert_eq!(HashSet::from_iter(vec![&_a_()]), model.witness(&e_0()));
            assert_eq!(HashSet::from_iter(vec![&_b_()]), model.witness(&e_1()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(f().wit_app1(_c_()), g().wit_app1(f().wit_app1(_c_()))));
            assert_eq!(HashSet::from_iter(vec![&e_0(), &e_1(), &e_2()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app2(_e_1(), _e_2())].iter()), model.facts());
            assert!(model.is_observed(&_R_().app2(_e_1(), _e_2())));
            assert!(model.is_observed(&_R_().app2(f().wit_app1(_c_()), g().wit_app1(f().wit_app1(_c_())))));
            assert!(model.is_observed(&_R_().app2(f().wit_app1(_c_()), _e_2())));
            assert_eq!(HashSet::from_iter(vec![&_c_()]), model.witness(&e_0()));
            assert_eq!(HashSet::from_iter(vec![&f().wit_app1(_e_0())]), model.witness(&e_1()));
            assert_eq!(HashSet::from_iter(vec![&g().wit_app1(_e_1())]), model.witness(&e_2()));
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(_a_(), _b_()));
            model.observe(&_S_().app2(_c_(), _d_()));
            assert_eq!(HashSet::from_iter(vec![&e_0(), &e_1(), &e_2(), &e_3()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app2(_e_0(), _e_1())
                                               , _S_().app2(_e_2(), _e_3())
            ].iter()), model.facts());
        }
        {
            let mut model = BasicModel::new();
            model.observe(&_R_().app2(_a_(), f().wit_app1(_a_())));
            model.observe(&_S_().app1(_b_()));
            model.observe(&_R_().app2(g().wit_app1(f().wit_app1(_a_())), _b_()));
            model.observe(&_S_().app1(_c_()));
            assert_eq!(HashSet::from_iter(vec![&e_0(), &e_1(), &e_2(), &e_3(), &e_4()]), model.domain());
            assert_eq!(HashSet::from_iter(vec![_R_().app2(_e_0(), _e_1())
                                               , _S_().app1(_e_4())
                                               , _S_().app1(_e_2())
                                               , _R_().app2(_e_3(), _e_2())
            ].iter()), model.facts());
        }
    }

    #[test]
    #[should_panic]
    fn test_observe_missing_element() {
        let mut model = BasicModel::new();
        model.observe(&_R_().app1(_e_0()));
    }

    #[test]
    fn test_build_sequent() {
        assert_debug_string("[] -> [[]]",
                            BasicSequent::from(&parse_formula("TRUE -> TRUE")));
        assert_debug_string("[] -> [[]]",
                            BasicSequent::from(&parse_formula("TRUE -> TRUE & TRUE")));
        assert_debug_string("[] -> [[], []]",
                            BasicSequent::from(&parse_formula("TRUE -> TRUE | TRUE")));
        assert_debug_string("[] -> []",
                            BasicSequent::from(&parse_formula("TRUE -> FALSE")));
        assert_debug_string("[] -> []",
                            BasicSequent::from(&parse_formula("TRUE -> FALSE & TRUE")));
        assert_debug_string("[] -> []",
                            BasicSequent::from(&parse_formula("TRUE -> TRUE & FALSE")));
        assert_debug_string("[] -> [[]]",
                            BasicSequent::from(&parse_formula("TRUE -> TRUE | FALSE")));
        assert_debug_string("[] -> [[]]",
                            BasicSequent::from(&parse_formula("TRUE -> FALSE | TRUE")));
        assert_debug_string("[P(x)] -> [[Q(x)]]",
                            BasicSequent::from(&parse_formula("P(x) -> Q(x)")));
        assert_debug_string("[P(x), Q(x)] -> [[Q(y)]]",
                            BasicSequent::from(&parse_formula("P(x) & Q(x) -> Q(y)")));
        assert_debug_string("[P(x), Q(x)] -> [[Q(x)], [R(z), S(z)]]",
                            BasicSequent::from(&parse_formula("P(x) & Q(x) -> Q(x) | (R(z) & S(z))")));
        assert_debug_string("[] -> [[P(x), Q(x)], [P(y), Q(y)], [P(z), Q(z)]]",
                            BasicSequent::from(&parse_formula("TRUE -> (P(x) & Q(x)) | (P(y) & Q(y)) | (P(z) & Q(z))")));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_1() {
        BasicSequent::from(&parse_formula("TRUE"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_2() {
        BasicSequent::from(&parse_formula("FALSE"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_3() {
        BasicSequent::from(&parse_formula("FALSE -> TRUE"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_4() {
        BasicSequent::from(&parse_formula("(P(x) | Q(x)) -> R(x)"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_5() {
        BasicSequent::from(&parse_formula("P(x) -> R(x) & (Q(z) | R(z))"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_6() {
        BasicSequent::from(&parse_formula("P(x) -> ?x. Q(x)"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_7() {
        BasicSequent::from(&parse_formula("?x.Q(x) -> P(x)"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_8() {
        BasicSequent::from(&parse_formula("TRUE -> ~FALSE"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_9() {
        BasicSequent::from(&parse_formula("TRUE -> ~TRUE"));
    }

    #[test]
    #[should_panic]
    fn test_build_invalid_sequent_10() {
        BasicSequent::from(&parse_formula("~P(x) -> ~Q(x)"));
    }

    #[test]
    fn test_core() {
        assert_eq!("Domain: {e#0}\n\
                      Facts: <P(e#0)>\n\
                      'a -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy0.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <P(e#0)>, <P(e#1)>\n\
                       'a -> e#0\n\
                       'b -> e#1",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy1.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <Q(e#0)>\n\
                       'a -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy2.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <R(e#0, e#1)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy3.raz"))));
        assert_eq!("Domain: {e#0}\n\
                Facts: \n\
                'a, 'b -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy4.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <P(e#0, e#1)>\n\
                       'a -> e#0\n\
                       'b -> e#1",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy5.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <P(e#1)>\n\
                       'a -> e#0\n\
                       f[e#0] -> e#1",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy6.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <Q(e#0)>, <R(e#0)>\n\
                       'a -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy7.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>\n\
                       'a -> e#0\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0}\n\
                       Facts: <Q(e#0)>\n\
                       'b -> e#0\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0}\n\
                       Facts: <R(e#0)>\n\
                       'c -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy8.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <Q(e#0)>\n\
                       'a, 'b -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy9.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <R(e#0)>\n\
                       'a -> e#0\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0}\n\
                       Facts: <Q(e#0)>, <S(e#0)>\n\
                       'b -> e#0",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy10.raz"))));
        assert_eq!("Domain: {}\n\
                       Facts: \n",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy11.raz"))));
        assert_eq!("Domain: {}\n\
                       Facts: \n",
                   print_models(solve_basic(read_theory_from_file("theories/core/thy12.raz"))));
        assert_eq!("", print_models(solve_basic(read_theory_from_file("theories/core/thy13.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <Q(e#0)>\n\
                       'b -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy14.raz"))));
        assert_eq!("", print_models(solve_basic(read_theory_from_file("theories/core/thy15.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0, e#0)>, <Q(e#0)>\n\
                       'c -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy16.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2}\n\
                       Facts: <P(e#0, e#0)>, <P(e#1, e#2)>, <Q(e#0)>\n\
                       'c -> e#0\n\
                       'a -> e#1\n\
                       'b -> e#2", print_models(solve_basic(read_theory_from_file("theories/core/thy17.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2}\n\
                       Facts: <P(e#0, e#1)>, <P(e#2, e#2)>, <Q(e#2)>\n\
                       'a -> e#0\n\
                       'b -> e#1\n\
                       'c -> e#2", print_models(solve_basic(read_theory_from_file("theories/core/thy18.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#10, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: \n\
                       'a -> e#0\n\
                       f[e#0] -> e#1\n\
                       f[e#1] -> e#2\n\
                       f[e#2] -> e#3\n\
                       f[e#3] -> e#4\n\
                       f[e#4] -> e#5\n\
                       f[e#5] -> e#6\n\
                       f[e#6] -> e#7\n\
                       f[e#7] -> e#8\n\
                       f[e#8] -> e#9\n\
                       'b, f[e#9] -> e#10", print_models(solve_basic(read_theory_from_file("theories/core/thy19.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#10, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <P(e#0)>, <P(e#1)>, <P(e#2)>, <P(e#3)>, <P(e#4)>, <P(e#5)>, <P(e#6)>, <P(e#7)>, <P(e#8)>, <P(e#9)>\n\
                       'a -> e#0\n\
                       f[e#0] -> e#1\n\
                       f[e#1] -> e#2\n\
                       f[e#2] -> e#3\n\
                       f[e#3] -> e#4\n\
                       f[e#4] -> e#5\n\
                       f[e#5] -> e#6\n\
                       f[e#6] -> e#7\n\
                       f[e#7] -> e#8\n\
                       f[e#8] -> e#9\n\
                       'b, f[e#9] -> e#10", print_models(solve_basic(read_theory_from_file("theories/core/thy20.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#10, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <P(e#0)>, <P(e#1)>, <P(e#2)>, <P(e#3)>, <P(e#4)>, <P(e#5)>, <P(e#6)>, <P(e#7)>, <P(e#8)>\n\
                       'a -> e#0\n\
                       f[e#0] -> e#1\n\
                       f[e#1] -> e#2\n\
                       f[e#2] -> e#3\n\
                       f[e#3] -> e#4\n\
                       f[e#4] -> e#5\n\
                       f[e#5] -> e#6\n\
                       f[e#6] -> e#7\n\
                       f[e#7] -> e#8\n\
                       f[e#8] -> e#9\n\
                       'b, f[e#9] -> e#10", print_models(solve_basic(read_theory_from_file("theories/core/thy21.raz"))));
        assert_eq!("Domain: {e#0}\n\
                Facts: <P(e#0)>, <Q(e#0)>, <R(e#0)>\n\
                'a -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy22.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <Q(e#0)>, <R(e#0)>, <S(e#0)>\n\
                       'sk#0, 'sk#1, 'sk#2 -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy23.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>, <Q(e#0)>, <R(e#0)>, <S(e#0)>, <T(e#0)>\n\
                       'sk#0, 'sk#1, 'sk#2, 'sk#3 -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy24.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2, e#3}\n\
                       Facts: <P(e#0)>, <Q(e#1)>, <R(e#2)>, <S(e#3)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3", print_models(solve_basic(read_theory_from_file("theories/core/thy25.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <P(e#0)>\n\
                       'sk#0 -> e#0\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0}\n\
                       Facts: <P(e#0)>\n\
                       'sk#1 -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy26.raz"))));
        assert_eq!("", print_models(solve_basic(read_theory_from_file("theories/core/thy27.raz"))));
        assert_eq!("Domain: {}\n\
                       Facts: <T()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <U()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <T()>, <U()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <T()>, <U()>, <V()>\n", print_models(solve_basic(read_theory_from_file("theories/core/thy28.raz"))));
        assert_eq!("Domain: {}\n\
                       Facts: <P()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <S()>, <W()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <S()>, <X()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <S()>, <Y()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <R()>, <T()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <R()>, <U()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <R()>, <T()>, <U()>, <V()>\n\
                       \n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {}\n\
                       Facts: <Q()>, <R()>, <T()>, <U()>, <V()>\n", print_models(solve_basic(read_theory_from_file("theories/core/thy29.raz"))));
        assert_eq!("", print_models(solve_basic(read_theory_from_file("theories/core/thy30.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <Q(e#0, e#0)>, <R(e#0)>, <U(e#0)>\n\
                       'sk#0 -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy31.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <Q(e#0, e#1)>, <R(e#0)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1", print_models(solve_basic(read_theory_from_file("theories/core/thy32.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2}\n\
                       Facts: <Q(e#0)>, <Q(e#2)>, <R(e#0, e#0)>, <R(e#2, e#0)>, <R(e#2, e#2)>, <S(e#1)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2}\n\
                       Facts: <Q(e#0)>, <Q(e#2)>, <R(e#0, e#0)>, <R(e#2, e#0)>, <R(e#2, e#2)>, <S(e#1)>, <S(e#2)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2}\n\
                       Facts: <Q(e#0)>, <Q(e#2)>, <R(e#0, e#0)>, <R(e#2, e#0)>, <R(e#2, e#2)>, <S(e#0)>, <S(e#1)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2}\n\
                       Facts: <Q(e#0)>, <Q(e#2)>, <R(e#0, e#0)>, <R(e#2, e#0)>, <R(e#2, e#2)>, <S(e#0)>, <S(e#1)>, <S(e#2)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2", print_models(solve_basic(read_theory_from_file("theories/core/thy33.raz"))));
        assert_eq!("Domain: {e#0, e#1}\n\
                       Facts: <P(e#0)>, <P(e#1)>\n\
                       'a -> e#0\n\
                       'sk#0 -> e#1", print_models(solve_basic(read_theory_from_file("theories/core/thy34.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P11(e#2)>, <P111(e#3)>, <P1111(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#7 -> e#3\n\
                       'sk#15 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P11(e#2)>, <P111(e#3)>, <P1112(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#7 -> e#3\n\
                       'sk#15 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P11(e#2)>, <P112(e#3)>, <P1121(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#7 -> e#3\n\
                       'sk#17 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P11(e#2)>, <P112(e#3)>, <P1122(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#7 -> e#3\n\
                       'sk#17 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P12(e#2)>, <P121(e#3)>, <P1211(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#9 -> e#3\n\
                       'sk#19 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P12(e#2)>, <P121(e#3)>, <P1212(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#9 -> e#3\n\
                       'sk#19 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P12(e#2)>, <P122(e#3)>, <P1221(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#9 -> e#3\n\
                       'sk#21 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P1(e#1)>, <P12(e#2)>, <P122(e#3)>, <P1222(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#3 -> e#2\n\
                       'sk#9 -> e#3\n\
                       'sk#21 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P21(e#2)>, <P211(e#3)>, <P2111(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#11 -> e#3\n\
                       'sk#23 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P21(e#2)>, <P211(e#3)>, <P2112(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#11 -> e#3\n\
                       'sk#23 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P21(e#2)>, <P212(e#3)>, <P2121(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#11 -> e#3\n\
                       'sk#25 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P21(e#2)>, <P212(e#3)>, <P2122(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#11 -> e#3\n\
                       'sk#25 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P22(e#2)>, <P221(e#3)>, <P2211(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#13 -> e#3\n\
                       'sk#27 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P22(e#2)>, <P221(e#3)>, <P2212(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#13 -> e#3\n\
                       'sk#27 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P22(e#2)>, <P222(e#3)>, <P2221(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#13 -> e#3\n\
                       'sk#29 -> e#4\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#0)>, <P2(e#1)>, <P22(e#2)>, <P222(e#3)>, <P2222(e#4)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#5 -> e#2\n\
                       'sk#13 -> e#3\n\
                       'sk#29 -> e#4", print_models(solve_basic(read_theory_from_file("theories/core/thy35.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q11(e#4, e#5)>, <Q111(e#6, e#7)>, <Q1111(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#14 -> e#6\n\
                       'sk#15 -> e#7\n\
                       'sk#30 -> e#8\n\
                       'sk#31 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q11(e#4, e#5)>, <Q111(e#6, e#7)>, <Q1112(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#14 -> e#6\n\
                       'sk#15 -> e#7\n\
                       'sk#30 -> e#8\n\
                       'sk#31 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q11(e#4, e#5)>, <Q112(e#6, e#7)>, <Q1121(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#14 -> e#6\n\
                       'sk#15 -> e#7\n\
                       'sk#34 -> e#8\n\
                       'sk#35 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q11(e#4, e#5)>, <Q112(e#6, e#7)>, <Q1122(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#14 -> e#6\n\
                       'sk#15 -> e#7\n\
                       'sk#34 -> e#8\n\
                       'sk#35 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q12(e#4, e#5)>, <Q121(e#6, e#7)>, <Q1211(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#18 -> e#6\n\
                       'sk#19 -> e#7\n\
                       'sk#38 -> e#8\n\
                       'sk#39 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q12(e#4, e#5)>, <Q121(e#6, e#7)>, <Q1212(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#18 -> e#6\n\
                       'sk#19 -> e#7\n\
                       'sk#38 -> e#8\n\
                       'sk#39 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q12(e#4, e#5)>, <Q122(e#6, e#7)>, <Q1221(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#18 -> e#6\n\
                       'sk#19 -> e#7\n\
                       'sk#42 -> e#8\n\
                       'sk#43 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q1(e#2, e#3)>, <Q12(e#4, e#5)>, <Q122(e#6, e#7)>, <Q1222(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#6 -> e#4\n\
                       'sk#7 -> e#5\n\
                       'sk#18 -> e#6\n\
                       'sk#19 -> e#7\n\
                       'sk#42 -> e#8\n\
                       'sk#43 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q21(e#4, e#5)>, <Q211(e#6, e#7)>, <Q2111(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#22 -> e#6\n\
                       'sk#23 -> e#7\n\
                       'sk#46 -> e#8\n\
                       'sk#47 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q21(e#4, e#5)>, <Q211(e#6, e#7)>, <Q2112(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#22 -> e#6\n\
                       'sk#23 -> e#7\n\
                       'sk#46 -> e#8\n\
                       'sk#47 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q21(e#4, e#5)>, <Q212(e#6, e#7)>, <Q2121(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#22 -> e#6\n\
                       'sk#23 -> e#7\n\
                       'sk#50 -> e#8\n\
                       'sk#51 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q21(e#4, e#5)>, <Q212(e#6, e#7)>, <Q2122(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#22 -> e#6\n\
                       'sk#23 -> e#7\n\
                       'sk#50 -> e#8\n\
                       'sk#51 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q22(e#4, e#5)>, <Q221(e#6, e#7)>, <Q2211(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#26 -> e#6\n\
                       'sk#27 -> e#7\n\
                       'sk#54 -> e#8\n\
                       'sk#55 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q22(e#4, e#5)>, <Q221(e#6, e#7)>, <Q2212(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#26 -> e#6\n\
                       'sk#27 -> e#7\n\
                       'sk#54 -> e#8\n\
                       'sk#55 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q22(e#4, e#5)>, <Q222(e#6, e#7)>, <Q2221(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#26 -> e#6\n\
                       'sk#27 -> e#7\n\
                       'sk#58 -> e#8\n\
                       'sk#59 -> e#9\n\
                       -- -- -- -- -- -- -- -- -- --\n\
                       Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6, e#7, e#8, e#9}\n\
                       Facts: <Q(e#0, e#1)>, <Q2(e#2, e#3)>, <Q22(e#4, e#5)>, <Q222(e#6, e#7)>, <Q2222(e#8, e#9)>\n\
                       'sk#0 -> e#0\n\
                       'sk#1 -> e#1\n\
                       'sk#2 -> e#2\n\
                       'sk#3 -> e#3\n\
                       'sk#10 -> e#4\n\
                       'sk#11 -> e#5\n\
                       'sk#26 -> e#6\n\
                       'sk#27 -> e#7\n\
                       'sk#58 -> e#8\n\
                       'sk#59 -> e#9", print_models(solve_basic(read_theory_from_file("theories/core/thy36.raz"))));
        assert_eq!("", print_models(solve_basic(read_theory_from_file("theories/core/thy37.raz"))));
        assert_eq!("Domain: {e#0}\n\
                       Facts: <R(e#0, e#0, e#0)>\n\
                       'sk#0, 'sk#1, 'sk#2 -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy38.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2, e#3, e#4, e#5, e#6}\n\
                       Facts: <Q(e#1)>, <R(e#1, e#6)>\n\
                       'sk#0 -> e#0\n\
                       f[e#0] -> e#1\n\
                       f[e#1] -> e#2\n\
                       f[e#2] -> e#3\n\
                       f[e#3] -> e#4\n\
                       f[e#4] -> e#5\n\
                       f[e#5] -> e#6", print_models(solve_basic(read_theory_from_file("theories/core/thy39.raz"))));
        assert_eq!("Domain: {e#0, e#1, e#2, e#3, e#4}\n\
                       Facts: <P(e#1)>, <Q(e#1)>, <R(e#0, e#1)>, <R(e#1, e#3)>, <S(e#4)>\n\
                       'sk#0 -> e#0\n\
                       f[e#0] -> e#1\n\
                       f[e#1] -> e#2\n\
                       f[e#2] -> e#3\n\
                       'sk#1 -> e#4", print_models(solve_basic(read_theory_from_file("theories/core/thy40.raz"))));
        assert_eq!("Domain: {}\n\
                       Facts: \n", print_models(solve_basic(read_theory_from_file("theories/core/thy41.raz"))));
//        assert_eq!("Domain: {e#0}\n\
//                       Facts: \n\
//                       'sk#0, 'e, f[e#0, e#0], i[e#0] -> e#0", print_models(solve_basic(read_theory_from_file("theories/core/thy42.raz"))));
    }

    fn solve_basic(theory: Theory) -> Vec<BasicModel> {
        let geometric_theory = theory.gnf();
        let sequents: Vec<BasicSequent> = geometric_theory
            .formulas
            .iter()
            .map(|f| f.into()).collect();

        let evaluator = BasicEvaluator {};
        let selector = TopDown::new(sequents);
        let mut strategy = FIFO::new();
        let bounder: Option<&DomainSize> = None;
        strategy.add(StrategyNode::new(BasicModel::new(), selector));
        solve_all(Box::new(strategy), Box::new(evaluator), bounder)
    }
}