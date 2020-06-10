/*! Implements a number of common transformations on first-order terms and formulae. */
use super::syntax::{Formula::*, Term::*, *};
use itertools::Itertools;
use std::cmp::Ordering::Equal;
use std::collections::HashMap;

/// Is the trait of types that map variables to terms.
pub trait Substitution {
    /// Maps `v` to a [`Term`].
    ///
    /// [`Term`]: ../syntax/enum.Term.html
    fn apply(&self, v: &V) -> Term;
}

/// Any function from [`V`] to [`Term`] is a substitution.
///
/// [`V`]: ../syntax/struct.V.html
/// [`Term`]: ../syntax/enum.Term.html
impl<F> Substitution for F
where
    F: Fn(&V) -> Term,
{
    fn apply(&self, v: &V) -> Term {
        self(v)
    }
}

/// Any map from [`V`] to [`Term`] is a substitution.
///
/// [`V`]: ../syntax/struct.V.html
/// [`Term`]: ../syntax/enum.Term.html
impl Substitution for HashMap<&V, Term> {
    fn apply(&self, v: &V) -> Term {
        self.get(v).map(|t| t.clone()).unwrap_or(v.clone().into())
    }
}

/// Is the trait of types that map variables to variables.
///
/// **Note**: A variable renaming may be regarded as a special case of [`Substitution`].
///
/// [`Substitution`]: ../transform/trait.Substitution.html
pub trait VariableRenaming {
    /// Maps `v` to another [`V`].
    ///
    /// [`V`]: ../syntax/struct.V.html
    fn apply(&self, v: &V) -> V;
}

/// Any function from [`V`] to [`Term`] is a variable renaming.
///
/// [`V`]: ../syntax/struct.V.html
/// [`Term`]: ../syntax/enum.Term.html
impl<F> VariableRenaming for F
where
    F: Fn(&V) -> V,
{
    fn apply(&self, v: &V) -> V {
        self(v)
    }
}

/// Any map from [`V`] to [`Term`] is a variable renaming.
///
/// [`V`]: ../syntax/struct.V.html
/// [`Term`]: ../syntax/enum.Term.html
impl VariableRenaming for HashMap<&V, V> {
    fn apply(&self, v: &V) -> V {
        self.get(v)
            .map(|var| var.clone())
            .unwrap_or(v.clone().into())
    }
}

/// Is the trait of objects constructed atop [`Term`]s.
///
/// [`Term`]: ../syntax/enum.Term.html
pub trait TermBased {
    /// Applies a transformation function `f` on the [`Term`]s of the receiver.
    ///
    /// [`Term`]: ../syntax/enum.Term.html
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self;

    /// Applies a [`VariableRenaming`] on the variable sub-terms of the receiver.
    ///
    /// [`VariableRenaming`]: ../transform/trait.VariableRenaming.html
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{V, C, F, Term};
    /// use razor_fol::transform::TermBased;
    /// use std::collections::HashMap;
    ///
    /// // variable symbols:
    /// let x_sym = V::from("x");
    /// let y_sym = V::from("y");
    /// let z_sym = V::from("z");
    /// let a_sym = V::from("a");
    /// let b_sym = V::from("b");
    ///
    /// // A variable renaming map that renames variable `x` to `a` and variable `y` to `b`
    /// let mut renaming = HashMap::new();
    /// renaming.insert(&x_sym, a_sym);
    /// renaming.insert(&y_sym, b_sym);
    ///
    /// let x = Term::from(x_sym.clone());
    /// let y = Term::from(y_sym.clone());
    /// let z = Term::from(z_sym.clone());
    /// let f = F::from("f");
    /// let g = F::from("g");
    ///
    /// // t = f(x, z, g(x, y, x))
    /// let t = f.app3(x.clone(), z.clone(), g.app3(x.clone(), y.clone(), x.clone()));
    ///
    /// let s = t.rename_vars(&renaming); // s = f(a, z, g(a, b, a))
    /// assert_eq!("f(a, z, g(a, b, a))", s.to_string())
    /// ```
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self;

    /// Applies a [`Substitution`] on the variable sub-terms of the receiver.
    ///
    /// [`Substitution`]: ../transform/trait.Substitution.html
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::{V, C, F, Term};
    /// use razor_fol::transform::TermBased;
    ///
    /// // A substitution function that maps all variable symbols `x` to a constant term `c`.
    /// // Otherwise, wraps the variable symbol in a variable term.
    /// fn x_to_c(v: &V) -> Term {
    ///     let x = V::from("x");
    ///     let c = C::from("c");
    ///
    ///     if v == &x {
    ///         Term::from(c)
    ///     } else {
    ///         Term::from(v.clone())
    ///     }
    /// }
    ///
    /// let x = Term::from(V::from("x"));
    /// let y = Term::from(V::from("y"));
    /// let f = F::from("f");
    /// let g = F::from("g");
    ///
    /// let t = f.app2(x.clone(), g.app3(x.clone(), y.clone(), x.clone())); // t = f(x, g(x, y, x))
    ///
    /// let s = t.substitute(&x_to_c); // s = f('c, g('c, y, 'c))
    /// assert_eq!("f('c, g('c, y, 'c))", s.to_string())
    /// ```
    fn substitute(&self, sub: &impl Substitution) -> Self;
}

impl TermBased for Term {
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        f(self)
    }

    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => Term::from(renaming.apply(v)),
            App { function, terms } => {
                let terms = terms.iter().map(|t| t.rename_vars(renaming)).collect();
                function.clone().app(terms)
            }
        }
    }

    fn substitute(&self, sub: &impl Substitution) -> Self {
        match self {
            Const { .. } => self.clone(),
            Var { variable: v } => sub.apply(v),
            App { function, terms } => {
                let terms = terms.iter().map(|t| t.substitute(sub)).collect();
                function.clone().app(terms)
            }
        }
    }
}

impl TermBased for Formula {
    #[inline]
    fn transform(&self, f: &impl Fn(&Term) -> Term) -> Self {
        match self {
            Top | Bottom => self.clone(),
            Atom { predicate, terms } => predicate.clone().app(terms.iter().map(f).collect()),
            Equals { left, right } => f(left).equals(f(right)),
            Not { formula } => not(formula.transform(f)),
            And { left, right } => left.transform(f).and(right.transform(f)),
            Or { left, right } => left.transform(f).or(right.transform(f)),
            Implies { left, right } => left.transform(f).implies(right.transform(f)),
            Iff { left, right } => left.transform(f).iff(right.transform(f)),
            Exists { variables, formula } => exists(variables.clone(), formula.transform(f)),
            Forall { variables, formula } => forall(variables.clone(), formula.transform(f)),
        }
    }

    /// **Note**: Applies a [`VariableRenaming`] on the **free** variables of the formula, keeping
    /// the bound variables unchanged.
    ///
    /// [`VariableRenaming`]: ../transform/trait.VariableRenaming.html
    fn rename_vars(&self, renaming: &impl VariableRenaming) -> Self {
        // this does not rename bound variables of the formula
        self.transform(&|t: &Term| t.rename_vars(renaming))
    }

    /// **Note**: Applies a [`Substitution`] on the **free** variables of the formula, keeping the
    /// bound variables unchanged.
    ///
    /// [`Substitution`]: ../transform/trait.Substitution.html
    fn substitute(&self, substitution: &impl Substitution) -> Self {
        self.transform(&|t: &Term| t.substitute(substitution))
    }
}

/// Generates Skolem names in an incremental fashion in the context of any transformation that
/// involves Skolemization.
///
/// **Note**: To ensure all Skolem functions in a theory are unique, the same instance of
/// `SkolemGenerator` must be used when transforming all formulae of the theory.
#[derive(PartialEq, Debug)]
pub struct SkolemGenerator {
    /// Is a prefix for the names generated by the generator.
    prefix: String,
    /// Is the next index to be appended to `prefix`.
    index: i32,
}

impl SkolemGenerator {
    /// Creates a new `SkolemGenerator` with the default prefix `"sk#"`.
    pub fn new() -> Self {
        Self {
            prefix: "sk#".to_owned(),
            index: 0,
        }
    }

    /// Returns the next Skolem name.
    pub fn next(&mut self) -> String {
        let result = format!("{}{}", self.prefix, self.index);
        self.index += 1;
        result
    }
}

impl From<&str> for SkolemGenerator {
    /// Creates a `SkolemGenerator` instance with the given prefix.
    fn from(prefix: &str) -> Self {
        Self {
            prefix: prefix.to_owned(),
            index: 0,
        }
    }
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

    /// Returns a Skolem Normal Form (SNF) equivalent to the receiver.
    ///
    /// **Hint**: An SNF is a [PNF] with only universal quantifiers
    /// (see: <https://en.wikipedia.org/wiki/Skolem_normal_form>).
    ///
    /// [PNF]: ./enum.Formula.html#method.pnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "∃ y. P(x, y)".parse().unwrap();
    /// assert_eq!("P(x, sk#0(x))", formula.snf().to_string());
    /// ```
    pub fn snf(&self) -> Formula {
        self.snf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::snf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    ///
    /// [`Formula::snf`]: ./enum.Formula.html#method.snf
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("skolem");
    /// let formula: Formula = "∃ y. P(x, y)".parse().unwrap();
    /// assert_eq!("P(x, skolem0(x))", formula.snf_with(&mut generator).to_string());
    /// ```
    pub fn snf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        fn helper(
            formula: Formula,
            mut skolem_vars: Vec<V>,
            generator: &mut SkolemGenerator,
        ) -> Formula {
            match formula {
                Forall { variables, formula } => {
                    skolem_vars.append(&mut variables.clone());
                    forall(variables, helper(*formula, skolem_vars, generator))
                }
                Exists { variables, formula } => {
                    let mut map: HashMap<&V, Term> = HashMap::new();

                    variables.iter().for_each(|v| {
                        if skolem_vars.is_empty() {
                            map.insert(&v, C::from(&generator.next()).into());
                        } else {
                            let vars: Vec<Term> =
                                skolem_vars.iter().map(|v| v.clone().into()).collect();
                            map.insert(&v, F::from(&generator.next()).app(vars));
                        }
                    });

                    let substituted = formula.substitute(&map);
                    helper(substituted, skolem_vars, generator)
                }
                _ => formula,
            }
        }

        // Skolemization only makes sense for PNF formulae.
        let free_vars: Vec<V> = self.free_vars().into_iter().map(|v| v.clone()).collect();
        helper(self.pnf(), free_vars, generator)
    }

    /// Returns an Negation Normal Form (NNF) equivalent to the receiver.
    ///
    /// **Hint**: An NNF is a formula where negation is only applied to its atomic (including
    /// equations) sub-formulae.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "not (P(x) iff Q(y))".parse().unwrap();
    /// assert_eq!("(P(x) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ Q(y))", formula.nnf().to_string());
    /// ```
    pub fn nnf(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { ref formula } => match **formula {
                Top => Bottom,
                Bottom => Top,
                Atom { .. } | Equals { .. } => self.clone(),
                Not { ref formula } => *formula.clone(),
                And {
                    ref left,
                    ref right,
                } => not(*left.clone()).nnf().or(not(*right.clone()).nnf()),
                Or {
                    ref left,
                    ref right,
                } => not(*left.clone()).nnf().and(not(*right.clone()).nnf()),
                Implies {
                    ref left,
                    ref right,
                } => left.nnf().and(not(*right.clone()).nnf()),
                Iff {
                    ref left,
                    ref right,
                } => left
                    .nnf()
                    .and(not(*right.clone()).nnf())
                    .or(not(*left.clone()).nnf().and(right.nnf())),
                Exists {
                    ref variables,
                    ref formula,
                } => forall(variables.clone(), not(*formula.clone()).nnf()),
                Forall {
                    ref variables,
                    ref formula,
                } => exists(variables.clone(), not(*formula.clone()).nnf()),
            },
            And { left, right } => left.nnf().and(right.nnf()),
            Or { left, right } => left.nnf().or(right.nnf()),
            Implies { left, right } => not(*left.clone()).nnf().or(right.nnf()),
            Iff { left, right } => not(*left.clone())
                .nnf()
                .or(right.nnf())
                .and(left.nnf().or(not(*right.clone()).nnf())),
            Exists { variables, formula } => exists(variables.clone(), formula.nnf()),
            Forall { variables, formula } => forall(variables.clone(), formula.nnf()),
        }
    }

    /// Returns a Conjunctive Normal Form (CNF) equivalent to the receiver.
    ///
    /// **Hint**: A CNF is a formula that is a conjunction of zero or more clauses. A clause is a
    /// disjunction of atomic formulae (including equations).
    ///
    /// **Note**: All free variables are assumed to be universally quantified.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
    /// assert_eq!("((¬P(x)) ∨ Q(y)) ∧ ((¬Q(y)) ∨ P(x))", formula.cnf().to_string());
    /// ```
    pub fn cnf(&self) -> Formula {
        self.cnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::cnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The CNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::cnf`]: ./enum.Formula.html#method.cnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "exists x. ((forall y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
    /// assert_eq!("((¬P(\'s%1)) ∨ (¬Q(\'s%0, \'s%1))) ∨ R(\'s%0)",
    ///     formula.cnf_with(&mut generator).to_string());
    /// ```
    pub fn cnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        // The following distributes conjunctions in the given formula. The function assumes that
        // its input is an NNF.
        fn distribute_or(formula: &Formula) -> Formula {
            match formula {
                Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
                And { left, right } => distribute_or(left).and(distribute_or(right)),
                Or { left, right } => {
                    let left = distribute_or(left);
                    let right = distribute_or(right);
                    if let And { left: l, right: r } = left {
                        distribute_or(&l.or(right.clone())).and(distribute_or(&r.or(right)))
                    } else if let And { left: l, right: r } = right {
                        distribute_or(&left.clone().or(*l)).and(distribute_or(&left.or(*r)))
                    } else {
                        left.or(right)
                    }
                }
                Forall { variables, formula } => forall(variables.clone(), distribute_or(formula)),
                _ => panic!("something is wrong: expecting a formula in negation normal form"),
            }
        }

        // The following eliminates the existential quantifiers of the input formula.
        fn remove_forall(formula: Formula) -> Formula {
            if let Forall { formula, .. } = formula {
                remove_forall(*formula)
            } else {
                formula
            }
        }

        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_or(&nnf))
    }

    /// Returns a Disjunctive Normal Form (DNF) equivalent to the receiver.
    ///
    /// **Hint**: A DNF is a formula that is a disjunction of zero or more conjuncts. A conjunct
    /// is a conjunction of atomic formulae (including equations).
    ///
    /// **Note**: All of the free variables are assumed to be universally quantified.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) iff Q(y)".parse().unwrap();
    /// assert_eq!("(((¬P(x)) ∧ (¬Q(y))) ∨ ((¬P(x)) ∧ P(x))) ∨ ((Q(y) ∧ (¬Q(y))) ∨ (Q(y) ∧ P(x)))",
    ///     formula.dnf().to_string());
    /// ```
    pub fn dnf(&self) -> Formula {
        self.dnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::dnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The DNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::dnf`]: ./enum.Formula.html#method.dnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
    /// assert_eq!("((¬P(y, x)) ∧ (¬Q(x))) ∨ Q(y)", formula.dnf_with(&mut generator).to_string());
    /// ```
    pub fn dnf_with(&self, generator: &mut SkolemGenerator) -> Formula {
        // The following distributes disjunction in the given formula. The function assumes that
        // its input is an NNF.
        fn distribute_and(formula: &Formula) -> Formula {
            match formula {
                Top | Bottom | Atom { .. } | Equals { .. } | Not { .. } => formula.clone(),
                Or { left, right } => distribute_and(left).or(distribute_and(right)),
                And { left, right } => {
                    let left = distribute_and(left);
                    let right = distribute_and(right);
                    if let Or { left: l, right: r } = left {
                        distribute_and(&l.and(right.clone())).or(distribute_and(&r.and(right)))
                    } else if let Or { left: l, right: r } = right {
                        distribute_and(&left.clone().and(*l)).or(distribute_and(&left.and(*r)))
                    } else {
                        And {
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    }
                }
                Forall { variables, formula } => forall(variables.clone(), distribute_and(formula)),
                _ => panic!("Something is wrong: expecting a formula in negation normal form."),
            }
        }

        // The following eliminates the existential quantifiers of the input formula.
        fn remove_forall(formula: Formula) -> Formula {
            if let Forall { formula, .. } = formula {
                remove_forall(*formula)
            } else {
                formula
            }
        }

        let nnf = self.snf_with(generator).nnf();
        remove_forall(distribute_and(&nnf))
    }

    /// Applies a number of syntactic transformations to simplify the receiver formula.
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "not (not P())".parse().unwrap();
    /// assert_eq!("P()", formula.simplify().to_string());
    ///
    /// let formula: Formula = "forall x. (P() and true) | (Q(x) or false)".parse().unwrap();
    /// assert_eq!("∀ x. (P() ∨ Q(x))", formula.simplify().to_string());
    /// ```
    pub fn simplify(&self) -> Formula {
        match self {
            Top | Bottom | Atom { .. } | Equals { .. } => self.clone(),
            Not { formula } => {
                let formula = formula.simplify();
                match formula {
                    Top => Bottom,
                    Bottom => Top,
                    Not { formula } => formula.simplify(),
                    _ => not(formula),
                }
            }
            And { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Bottom
                } else if let Bottom = right {
                    Bottom
                } else if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else {
                    left.and(right)
                }
            }
            Or { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Bottom = left {
                    right
                } else if let Bottom = right {
                    left
                } else {
                    left.or(right)
                }
            }
            Implies { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Bottom = left {
                    Top
                } else if let Top = right {
                    Top
                } else if let Top = left {
                    right
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.implies(right)
                }
            }
            Iff { left, right } => {
                let left = left.simplify();
                let right = right.simplify();
                if let Top = left {
                    right
                } else if let Top = right {
                    left
                } else if let Bottom = left {
                    not(right).simplify()
                } else if let Bottom = right {
                    not(left).simplify()
                } else {
                    left.iff(right)
                }
            }
            Exists { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    exists(vs, formula)
                }
            }
            Forall { variables, formula } => {
                let formula = formula.simplify();
                let free_vars = formula.free_vars();
                let vs: Vec<V> = free_vars
                    .iter()
                    .filter(|v| variables.contains(v))
                    .map(|v| (*v).clone())
                    .collect();
                if vs.is_empty() {
                    formula
                } else {
                    forall(vs, formula)
                }
            }
        }
    }

    /// Returns a list of formulae in [Geometric Normal Form][gnf] (GNF), equivalent to the
    /// receiver.
    ///
    /// [gnf]: ../../chase/index.html#background
    ///
    /// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
    /// by Steve Vickers.
    ///
    /// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    ///
    /// let formula: Formula = "P(x) & (Q(x) | R(x))".parse().unwrap();
    /// let gnf_to_string: Vec<String> = formula.gnf().iter().map(|f| f.to_string()).collect();
    /// assert_eq!(vec!["⊤ → P(x)", "⊤ → (Q(x) ∨ R(x))"], gnf_to_string);
    /// ```
    pub fn gnf(&self) -> Vec<Formula> {
        self.gnf_with(&mut SkolemGenerator::new())
    }

    /// Is similar to [`Formula::gnf`] but uses an existing [`SkolemGenerator`] to avoid collision
    /// when generating Skolem function names (including Skolem constants).
    ///
    /// **Note**: The GNF transformation includes Skolemization.
    ///
    /// [`SkolemGenerator`]: ../transform/struct.SkolemGenerator.html
    /// [`Formula::gnf`]: ./enum.Formula.html#method.gnf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Formula;
    /// use razor_fol::transform::SkolemGenerator;
    ///
    /// let mut generator = SkolemGenerator::from("s%");
    /// let formula: Formula = "P(y) -> exists x. P(x) & Q(y)".parse().unwrap();
    /// let gnf_to_string: Vec<String> = formula.gnf().iter().map(|f| f.to_string()).collect();
    /// assert_eq!(vec!["P(y) → P(sk#0(y))", "P(y) → Q(y)"], gnf_to_string);
    /// ```
    pub fn gnf_with(&self, generator: &mut SkolemGenerator) -> Vec<Formula> {
        // For any disjunct of the CNF, the negative literals form the body of the geometric form
        // and the positive literals form its head:
        fn split_sides(disjunct: Formula) -> (Vec<Formula>, Vec<Formula>) {
            match disjunct {
                Or { left, right } => {
                    let (mut left_body, mut left_head) = split_sides(*left);
                    let (mut right_body, mut right_head) = split_sides(*right);

                    left_body.append(&mut right_body);
                    let body: Vec<Formula> = left_body.into_iter().unique().collect();

                    left_head.append(&mut right_head);
                    let head: Vec<Formula> = left_head.into_iter().unique().collect();

                    (body, head)
                }
                Not { formula } => (vec![*formula], vec![]),
                _ => (vec![], vec![disjunct]),
            }
        }

        // Convert the disjuncts of the CNF to an implication. These implications are geometric sequents.
        fn to_implication(disjunct: Formula) -> Formula {
            let (body, head) = split_sides(disjunct);
            let body = body.into_iter().fold(Top, |x, y| x.and(y)).simplify();
            let head = head.into_iter().fold(Bottom, |x, y| x.or(y)).simplify();
            body.implies(head)
        }

        // Split the CNF to a set of disjuncts.
        fn get_disjuncts(cnf: Formula) -> Vec<Formula> {
            match cnf {
                And { left, right } => {
                    let mut left = get_disjuncts(*left);
                    let mut right = get_disjuncts(*right);
                    left.append(&mut right);
                    left.into_iter().unique().collect()
                }
                _ => vec![cnf],
            }
        }

        get_disjuncts(self.cnf_with(generator))
            .into_iter()
            .map(to_implication)
            .collect()
    }
}

impl Theory {
    /// Transforms the given theory to a *geometric theory*, where all formulae are in
    /// [Geometric Normal Form][gnf] (GNF).
    ///
    /// [gnf]: ../../chase/index.html#background
    ///
    /// **Hint**: For mor information about GNF, see [Geometric Logic in Computer Science][glics]
    /// by Steve Vickers.
    ///
    /// [glics]: https://www.cs.bham.ac.uk/~sjv/GLiCS.pdf
    ///
    /// **Example**:
    /// ```rust
    /// # use razor_fol::syntax::Theory;
    ///
    /// let theory: Theory = r#"
    ///     not P(x) or Q(x);
    ///     Q(x) -> exists y. R(x, y);
    /// "#.parse().unwrap();
    /// assert_eq!(r#"P(x) → Q(x)
    /// Q(x) → R(x, sk#0(x))"#, theory.gnf().to_string());
    /// ```
    pub fn gnf(&self) -> Theory {
        use core::convert::TryFrom;

        let mut generator = SkolemGenerator::new();
        let formulae: Vec<Formula> = self
            .formulae
            .iter()
            .flat_map(|f| f.gnf_with(&mut generator))
            .collect();

        // assuming that conversion to gnf won't change the signature
        Theory::try_from(compress_geometric(formulae)).unwrap()
    }
}

// a helper to merge sequents with syntactically identical bodies
fn compress_geometric(formulae: Vec<Formula>) -> Vec<Formula> {
    formulae
        .into_iter()
        .sorted_by(|f1, f2| {
            // sort sequents by their body
            match (f1, f2) {
                (Implies { left: f1, .. }, Implies { left: f2, .. }) => f1.cmp(f2),
                _ => Equal,
            }
        })
        .into_iter()
        .coalesce(|f1, f2| {
            // merge the ones with the same body:
            match f1 {
                Implies {
                    left: ref l1,
                    right: ref r1,
                } => {
                    let l_vars = l1.free_vars();
                    let r_vars = r1.free_vars();
                    // compress sequents with no free variables that show up only in head:
                    if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                        match f2 {
                            Implies {
                                left: ref l2,
                                right: ref r2,
                            } => {
                                let l_vars = l2.free_vars();
                                let r_vars = r2.free_vars();
                                if r_vars.iter().all(|rv| l_vars.iter().any(|lv| lv == rv)) {
                                    if l1 == l2 {
                                        Ok(l2.clone().implies(r1.clone().and(*r2.clone())))
                                    } else {
                                        Err((f1, f2))
                                    }
                                } else {
                                    Err((f2, f1))
                                }
                            }
                            _ => Err((f2, f1)),
                        }
                    } else {
                        Err((f1, f2))
                    }
                }
                _ => Err((f1, f2)),
            }
        })
        .map(|f| {
            // convert the head to dnf and simplify it:
            match f {
                Implies { left, right: r } => left.implies(simplify_dnf(r.dnf())),
                _ => f,
            }
        })
        .collect()
}

// Simplifies the given DNF as a helper for compress geometric.
fn simplify_dnf(formula: Formula) -> Formula {
    fn disjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            Or { left, right } => {
                let mut lefts = disjunct_list(*left);
                let mut rights = disjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    fn conjunct_list(formula: Formula) -> Vec<Formula> {
        match formula {
            And { left, right } => {
                let mut lefts = conjunct_list(*left);
                let mut rights = conjunct_list(*right);
                lefts.append(&mut rights);
                lefts
            }
            _ => vec![formula],
        }
    }

    let disjuncts: Vec<Vec<Formula>> = disjunct_list(formula)
        .into_iter()
        .map(|d| conjunct_list(d).into_iter().unique().collect())
        .collect();

    let disjuncts: Vec<Vec<Formula>> = disjuncts
        .iter()
        .filter(|d| {
            !disjuncts.iter().any(|dd| {
                (dd.len() < d.len() || (dd.len() == d.len() && dd < d))
                    && dd.iter().all(|cc| d.iter().any(|c| cc == c))
            })
        })
        .map(|d| d.clone())
        .unique()
        .collect();

    disjuncts
        .into_iter()
        .map(|d| d.into_iter().fold1(|f1, f2| f1.and(f2)).unwrap())
        .fold1(|f1, f2| f1.or(f2))
        .unwrap()
}

#[cfg(test)]
mod test_transform {
    use super::*;
    use crate::test_prelude::*;
    use std::collections::HashMap;

    #[test]
    fn test_substitution_map() {
        {
            let map: HashMap<&V, Term> = HashMap::new();
            assert_eq!(x(), x().substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &_x();
            let y_var = y();

            map.insert(x_v, y_var);
            assert_eq!(y(), x().substitute(&map));
        }
        {
            let mut map: HashMap<&V, Term> = HashMap::new();
            let x_v = &_x();
            let y_v = &_y();
            let term_1 = g().app1(z());
            let term_2 = h().app2(z(), y());

            map.insert(x_v, term_1);
            map.insert(y_v, term_2);
            assert_eq!(
                f().app2(g().app1(z()), h().app2(z(), y())),
                f().app2(x(), y()).substitute(&map)
            );
        }
    }

    #[test]
    fn test_rename_term() {
        assert_eq!(x(), x().rename_vars(&|v: &V| v.clone()));
        assert_eq!(
            y(),
            x().rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            x(),
            x().rename_vars(&|v: &V| {
                if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            f().app1(y()),
            f().app1(x()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            f().app1(x()),
            f().app1(x()).rename_vars(&|v: &V| {
                if *v == _z() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            f().app2(z(), z()),
            f().app2(x(), y()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            f().app2(y(), g().app2(y(), h().app1(z()))),
            f().app2(x(), g().app2(x(), h().app1(y())))
                .rename_vars(&|v: &V| {
                    if *v == _x() {
                        _y()
                    } else if *v == _y() {
                        _z()
                    } else {
                        v.clone()
                    }
                })
        );
    }

    #[test]
    fn test_substitute_term() {
        assert_eq!(x(), x().substitute(&|v: &V| v.clone().into()));
        assert_eq!(
            a(),
            a().substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            y(),
            x().substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            a(),
            x().substitute(&|v: &V| {
                if *v == _x() {
                    a()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app1(z()),
            x().substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(z())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            x(),
            x().substitute(&|v: &V| {
                if *v == _y() {
                    z()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app1(y()),
            f().app1(x()).substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app1(g().app1(h().app2(y(), z()))),
            f().app1(x()).substitute(&|v: &V| {
                if *v == _x() {
                    g().app1(h().app2(y(), z()))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app1(x()),
            f().app1(x()).substitute(&|v: &V| {
                if *v == _y() {
                    z()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app2(g().app1(z()), h().app2(z(), y())),
            f().app2(x(), y()).substitute(&|v: &V| {
                if *v == _x() {
                    g().app1(z())
                } else if *v == _y() {
                    h().app2(z(), y())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app2(
                f().app1(f().app0()),
                g().app2(f().app1(f().app0()), h().app1(z()))
            ),
            f().app2(x(), g().app2(x(), h().app1(y())))
                .substitute(&|v: &V| {
                    if *v == _x() {
                        f().app1(f().app0())
                    } else if *v == _y() {
                        z()
                    } else {
                        v.clone().into()
                    }
                })
        );
        assert_eq!(
            f().app2(f().app1(a()), g().app2(f().app1(a()), h().app1(z()))),
            f().app2(x(), g().app2(x(), h().app1(y())))
                .substitute(&|v: &V| {
                    if *v == _x() {
                        f().app1(a())
                    } else if *v == _y() {
                        z()
                    } else {
                        v.clone().into()
                    }
                })
        );
    }

    #[test]
    fn test_skolem_generator() {
        assert_eq!(
            SkolemGenerator {
                prefix: "sk#".to_owned(),
                index: 0
            },
            SkolemGenerator::new()
        );
        {
            let mut gen = SkolemGenerator::new();
            assert_eq!("sk#0", gen.next());
            assert_eq!("sk#1", gen.next());
            assert_eq!("sk#2", gen.next());
        }
        {
            let mut gen = SkolemGenerator::from("razor");
            assert_eq!("razor0", gen.next());
            assert_eq!("razor1", gen.next());
            assert_eq!("razor2", gen.next());
        }
    }

    #[test]
    fn test_rename_formula() {
        assert_eq!(
            Top,
            Top.rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            Bottom,
            Bottom.rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            z().equals(z()),
            x().equals(y()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(x()),
            P().app1(x()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _x()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(y()),
            P().app1(x()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app3(y(), z(), y()),
            P().app3(x(), y(), x()).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            not(P().app3(y(), z(), y())),
            not(P().app3(x(), y(), x())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(z()).and(Q().app1(z())),
            P().app1(x()).and(Q().app1(y())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(z()).or(Q().app1(z())),
            P().app1(x()).or(Q().app1(y())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(z()).implies(Q().app1(z())),
            P().app1(x()).implies(Q().app1(y())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            P().app1(z()).iff(Q().app1(z())),
            P().app1(x()).iff(Q().app1(y())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _z()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            exists2(_x(), _y(), P().app3(y(), y(), y())),
            exists2(_x(), _y(), P().app3(x(), y(), z())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _z() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            forall2(_x(), _y(), P().app3(y(), y(), y())),
            forall2(_x(), _y(), P().app3(x(), y(), z())).rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _z() {
                    _y()
                } else {
                    v.clone()
                }
            })
        );
        assert_eq!(
            exists1(
                _x(),
                forall1(_y(), P().app1(y()).or(Q().app1(z()).and(R().app1(z()))),)
                    .and(not(z().equals(z())))
            ),
            exists1(
                _x(),
                forall1(_y(), P().app1(x()).or(Q().app1(y()).and(R().app1(z()))),)
                    .and(not(y().equals(y()))),
            )
            .rename_vars(&|v: &V| {
                if *v == _x() {
                    _y()
                } else if *v == _y() {
                    _z()
                } else {
                    v.clone()
                }
            })
        );
    }

    #[test]
    fn test_substitute_formula() {
        assert_eq!(
            Top,
            Top.substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            Bottom,
            Bottom.substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            f().app1(g().app1(z())).equals(g().app1(f().app1(z()))),
            x().equals(y()).substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(g().app1(z()))
                } else if *v == _y() {
                    g().app1(f().app1(z()))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(h().app1(y())),
            P().app1(x()).substitute(&|v: &V| {
                if *v == _x() {
                    h().app1(y())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(g().app1(g().app1(x()))),
            P().app1(x()).substitute(&|v: &V| {
                if *v == _x() {
                    g().app1(g().app1(x()))
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app3(y(), f().app1(z()), y()),
            P().app3(x(), y(), x()).substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else if *v == _y() {
                    f().app1(z())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            not(P().app3(h().app0(), z(), h().app0())),
            not(P().app3(x(), y(), x())).substitute(&|v: &V| {
                if *v == _x() {
                    h().app0()
                } else if *v == _y() {
                    z()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(f().app1(g().app0())).and(Q().app1(h().app1(z()))),
            P().app1(x()).and(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(g().app0())
                } else if *v == _y() {
                    h().app1(z())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(f().app1(g().app0())).or(Q().app1(h().app1(z()))),
            P().app1(x()).or(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(g().app0())
                } else if *v == _y() {
                    h().app1(z())
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(f().app0()).implies(Q().app1(g().app0())),
            P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app0()
                } else if *v == _y() {
                    g().app0()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(a()).implies(Q().app1(b())),
            P().app1(x()).implies(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    a()
                } else if *v == _y() {
                    b()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(f().app0()).iff(Q().app1(g().app0())),
            P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app0()
                } else if *v == _y() {
                    g().app0()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            P().app1(a()).iff(Q().app1(b())),
            P().app1(x()).iff(Q().app1(y())).substitute(&|v: &V| {
                if *v == _x() {
                    a()
                } else if *v == _y() {
                    b()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            exists2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
            exists2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(g().app1(y()))
                } else if *v == _z() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            forall2(_x(), _y(), P().app3(f().app1(g().app1(y())), y(), y())),
            forall2(_x(), _y(), P().app3(x(), y(), z())).substitute(&|v: &V| {
                if *v == _x() {
                    f().app1(g().app1(y()))
                } else if *v == _z() {
                    y()
                } else {
                    v.clone().into()
                }
            })
        );
        assert_eq!(
            exists1(
                _x(),
                forall1(_y(), P().app1(y()).or(Q().app1(z()).and(R().app1(z()))),)
                    .and(not(z().equals(z())))
            ),
            exists1(
                _x(),
                forall1(_y(), P().app1(x()).or(Q().app1(y()).and(R().app1(z()))),)
                    .and(not(y().equals(y()))),
            )
            .substitute(&|v: &V| {
                if *v == _x() {
                    y()
                } else if *v == _y() {
                    z()
                } else {
                    v.clone().into()
                }
            })
        );
    }

    #[test]
    fn test_pnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string("true", formula.pnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string("false", formula.pnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.pnf());
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string("x = y", formula.pnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string("P(x) -> Q(y)", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string("(P(x) -> Q(y)) & (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "? x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string("? x. ((P(x) & (~Q(y))) | R(z))", formula.pnf());
        }
        {
            let formula: Formula = "! x. P(x) & ~Q(y) | R(z)".parse().unwrap();
            assert_debug_string("! x. ((P(x) & (~Q(y))) | R(z))", formula.pnf());
        }
        // sanity checking:
        {
            let formula: Formula = "~? x. P(x)".parse().unwrap();
            assert_debug_string("! x. (~P(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string("! x. (P(x) & Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(y)".parse().unwrap();
            assert_debug_string("? x. (P(x) & Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string("! x`. (P(x`) & Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & Q(x)".parse().unwrap();
            assert_debug_string("? x`. (P(x`) & Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (P(x`, y`) & Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) & Q(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (P(x`, y`) & Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) & ! x. P(x)".parse().unwrap();
            assert_debug_string("! x. (Q(y) & P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) & ? x. P(x)".parse().unwrap();
            assert_debug_string("? x. (Q(y) & P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) & ! x. P(x)".parse().unwrap();
            assert_debug_string("! x`. (Q(x) & P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) & ? x. P(x)".parse().unwrap();
            assert_debug_string("? x`. (Q(x) & P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) & ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (Q(x, y) & P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) & ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (Q(x, y) & P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string("! x. (P(x) | Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(y)".parse().unwrap();
            assert_debug_string("? x. (P(x) | Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string("! x`. (P(x`) | Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | Q(x)".parse().unwrap();
            assert_debug_string("? x`. (P(x`) | Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (P(x`, y`) | Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) | Q(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (P(x`, y`) | Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) | ! x. P(x)".parse().unwrap();
            assert_debug_string("! x. (Q(y) | P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) | ? x. P(x)".parse().unwrap();
            assert_debug_string("? x. (Q(y) | P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) | ! x. P(x)".parse().unwrap();
            assert_debug_string("! x`. (Q(x) | P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) | ? x. P(x)".parse().unwrap();
            assert_debug_string("? x`. (Q(x) | P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) | ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (Q(x, y) | P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) | ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (Q(x, y) | P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string("? x. (P(x) -> Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(y)".parse().unwrap();
            assert_debug_string("! x. (P(x) -> Q(y))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string("? x`. (P(x`) -> Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_string("! x`. (P(x`) -> Q(x))", formula.pnf());
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (P(x`, y`) -> Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) -> Q(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (P(x`, y`) -> Q(x, y))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) -> ! x. P(x)".parse().unwrap();
            assert_debug_string("! x. (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(y) -> ? x. P(x)".parse().unwrap();
            assert_debug_string("? x. (Q(y) -> P(x))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) -> ! x. P(x)".parse().unwrap();
            assert_debug_string("! x`. (Q(x) -> P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x) -> ? x. P(x)".parse().unwrap();
            assert_debug_string("? x`. (Q(x) -> P(x`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) -> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string("! x`, y`. (Q(x, y) -> P(x`, y`))", formula.pnf());
        }
        {
            let formula: Formula = "Q(x, y) -> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string("? x`, y`. (Q(x, y) -> P(x`, y`))", formula.pnf());
        }

        {
            let formula: Formula = "(! x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string(
                "? x. (! x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(y)".parse().unwrap();
            assert_debug_string(
                "! x. (? x`. ((P(x) -> Q(y)) & (Q(y) -> P(x`))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string(
                "? x`. (! x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> Q(x)".parse().unwrap();
            assert_debug_string(
                "! x`. (? x``. ((P(x`) -> Q(x)) & (Q(x) -> P(x``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string(
                "? x`, y`. (! x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x, y. P(x, y)) <=> Q(x, y)".parse().unwrap();
            assert_debug_string(
                "! x`, y`. (? x``, y``. ((P(x`, y`) -> Q(x, y)) & (Q(x, y) -> P(x``, y``))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string(
                "! x. (? x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(y) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string(
                "? x. (! x`. ((Q(y) -> P(x)) & (P(x`) -> Q(y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ! x. P(x)".parse().unwrap();
            assert_debug_string(
                "! x`. (? x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x) <=> ? x. P(x)".parse().unwrap();
            assert_debug_string(
                "? x`. (! x``. ((Q(x) -> P(x`)) & (P(x``) -> Q(x))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ! x, y. P(x, y)".parse().unwrap();
            assert_debug_string(
                "! x`, y`. (? x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "Q(x, y) <=> ? x, y. P(x, y)".parse().unwrap();
            assert_debug_string(
                "? x`, y`. (! x``, y``. ((Q(x, y) -> P(x`, y`)) & (P(x``, y``) -> Q(x, y))))",
                formula.pnf(),
            );
        }
        //renaming tests
        assert_debug_string(
            "! x``, x`. (P(x``) & Q(x))",
            forall2(_x(), _x_1(), P().app1(x()))
                .and(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "? x``, x`. (P(x``) & Q(x))",
            exists2(_x(), _x_1(), P().app1(x()))
                .and(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "? x``. (P(x``) & Q(x, x`))",
            exists1(_x(), P().app1(x())).and(Q().app2(x(), x_1())).pnf(),
        );
        assert_debug_string(
            "? x``. (P(x``, x`) & Q(x))",
            exists1(_x(), P().app2(x(), x_1())).and(Q().app1(x())).pnf(),
        );
        assert_debug_string(
            "! x``, x`. (Q(x) & P(x``))",
            Q().app1(x())
                .and(forall2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``, x`. (Q(x) & P(x``))",
            Q().app1(x())
                .and(exists2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x, x`) & P(x``))",
            Q().app2(x(), x_1()).and(exists1(_x(), P().app1(x()))).pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x) & P(x``, x`))",
            Q().app1(x()).and(exists1(_x(), P().app2(x(), x_1()))).pnf(),
        );

        assert_debug_string(
            "! x``, x`. (P(x``) | Q(x))",
            forall2(_x(), _x_1(), P().app1(x())).or(Q().app1(x())).pnf(),
        );
        assert_debug_string(
            "? x``, x`. (P(x``) | Q(x))",
            exists2(_x(), _x_1(), P().app1(x())).or(Q().app1(x())).pnf(),
        );
        assert_debug_string(
            "? x``. (P(x``) | Q(x, x`))",
            exists1(_x(), P().app1(x())).or(Q().app2(x(), x_1())).pnf(),
        );
        assert_debug_string(
            "? x``. (P(x``, x`) | Q(x))",
            exists1(_x(), P().app2(x(), x_1())).or(Q().app1(x())).pnf(),
        );
        assert_debug_string(
            "! x``, x`. (Q(x) | P(x``))",
            Q().app1(x()).or(forall2(_x(), _x_1(), P().app1(x()))).pnf(),
        );
        assert_debug_string(
            "? x``, x`. (Q(x) | P(x``))",
            Q().app1(x()).or(exists2(_x(), _x_1(), P().app1(x()))).pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x, x`) | P(x``))",
            Q().app2(x(), x_1()).or(exists1(_x(), P().app1(x()))).pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x) | P(x``, x`))",
            Q().app1(x()).or(exists1(_x(), P().app2(x(), x_1()))).pnf(),
        );

        assert_debug_string(
            "? x``, x`. (P(x``) -> Q(x))",
            forall2(_x(), _x_1(), P().app1(x()))
                .implies(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "! x``, x`. (P(x``) -> Q(x))",
            exists2(_x(), _x_1(), P().app1(x()))
                .implies(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "! x``. (P(x``) -> Q(x, x`))",
            exists1(_x(), P().app1(x()))
                .implies(Q().app2(x(), x_1()))
                .pnf(),
        );
        assert_debug_string(
            "! x``. (P(x``, x`) -> Q(x))",
            exists1(_x(), P().app2(x(), x_1()))
                .implies(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "! x``, x`. (Q(x) -> P(x``))",
            Q().app1(x())
                .implies(forall2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``, x`. (Q(x) -> P(x``))",
            Q().app1(x())
                .implies(exists2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x, x`) -> P(x``))",
            Q().app2(x(), x_1())
                .implies(exists1(_x(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``. (Q(x) -> P(x``, x`))",
            Q().app1(x())
                .implies(exists1(_x(), P().app2(x(), x_1())))
                .pnf(),
        );

        assert_debug_string(
            "? x``, x`. (! x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            forall2(_x(), _x_1(), P().app1(x()))
                .iff(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "! x``, x`. (? x```, x`. ((P(x``) -> Q(x)) & (Q(x) -> P(x```))))",
            exists2(_x(), _x_1(), P().app1(x()))
                .iff(Q().app1(x()))
                .pnf(),
        );
        assert_debug_string(
            "! x``. (? x```. ((P(x``) -> Q(x, x`)) & (Q(x, x`) -> P(x```))))",
            exists1(_x(), P().app1(x())).iff(Q().app2(x(), x_1())).pnf(),
        );
        assert_debug_string(
            "! x``. (? x```. ((P(x``, x`) -> Q(x)) & (Q(x) -> P(x```, x`))))",
            exists1(_x(), P().app2(x(), x_1())).iff(Q().app1(x())).pnf(),
        );
        assert_debug_string(
            "! x``, x`. (? x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            Q().app1(x())
                .iff(forall2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``, x`. (! x```, x`. ((Q(x) -> P(x``)) & (P(x```) -> Q(x))))",
            Q().app1(x())
                .iff(exists2(_x(), _x_1(), P().app1(x())))
                .pnf(),
        );
        assert_debug_string(
            "? x``. (! x```. ((Q(x, x`) -> P(x``)) & (P(x```) -> Q(x, x`))))",
            Q().app2(x(), x_1()).iff(exists1(_x(), P().app1(x()))).pnf(),
        );
        assert_debug_string(
            "? x``. (! x```. ((Q(x) -> P(x``, x`)) & (P(x```, x`) -> Q(x))))",
            Q().app1(x()).iff(exists1(_x(), P().app2(x(), x_1()))).pnf(),
        );
        // both sides of binary formulae
        {
            let formula: Formula = "(! x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (! x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (? x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & (! x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (! x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) & (? x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (? x`. (P(x) & Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (! x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (? x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | (! x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (! x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) | (? x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (? x`. (P(x) | Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (! x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string("? x. (? x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> (! x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (! x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> (? x. Q(x))".parse().unwrap();
            assert_debug_string("! x. (? x`. (P(x) -> Q(x`)))", formula.pnf());
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string(
                "? x. (! x`. (? x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(! x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string(
                "? x. (? x`. (! x``. (! x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (! x. Q(x))".parse().unwrap();
            assert_debug_string(
                "! x. (! x`. (? x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "(? x. P(x)) <=> (? x. Q(x))".parse().unwrap();
            assert_debug_string(
                "! x. (? x`. (! x``. (? x```. ((P(x) -> Q(x`)) & (Q(x``) -> P(x```))))))",
                formula.pnf(),
            );
        }
        // multiple steps
        {
            let formula: Formula = "~~?x.P(x)".parse().unwrap();
            assert_debug_string("? x. (~(~P(x)))", formula.pnf());
        }
        {
            let formula: Formula = "~~!x.P(x)".parse().unwrap();
            assert_debug_string("! x. (~(~P(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & ((! x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string("! x`. (P(x) & (Q(x`) & R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) & ((? x. Q(x)) & R(x))".parse().unwrap();
            assert_debug_string("? x`. (P(x) & (Q(x`) & R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | ((! x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string("! x`. (P(x) | (Q(x`) | R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) | ((? x. Q(x)) | R(x))".parse().unwrap();
            assert_debug_string("? x`. (P(x) | (Q(x`) | R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> ((! x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string("? x`. (P(x) -> (Q(x`) -> R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) -> ((? x. Q(x)) -> R(x))".parse().unwrap();
            assert_debug_string("! x`. (P(x) -> (Q(x`) -> R(x)))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> ((! x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string("? x`. (! x``. (! x```. (? x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", formula.pnf());
        }
        {
            let formula: Formula = "P(x) <=> ((? x. Q(x)) <=> R(x))".parse().unwrap();
            assert_debug_string("! x`. (? x``. (? x```. (! x````. ((P(x) -> ((Q(x`) -> R(x)) & (R(x) -> Q(x``)))) & (((Q(x```) -> R(x)) & (R(x) -> Q(x````))) -> P(x))))))", formula.pnf());
        }
        // random formulae
        {
            let formula: Formula = "!x . (P(x) -> ?y . (P(y) & Q(x, y)))".parse().unwrap();
            assert_debug_string("! x. (? y. (P(x) -> (P(y) & Q(x, y))))", formula.pnf());
        }
        {
            let formula: Formula = "?x . (P(x) & !y . (P(y) -> Q(x, y)))".parse().unwrap();
            assert_debug_string("? x. (! y. (P(x) & (P(y) -> Q(x, y))))", formula.pnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> ~(!y . (P(y) -> Q(x, y))))".parse().unwrap();
            assert_debug_string("! x. (? y. (P(x) -> (~(P(y) -> Q(x, y)))))", formula.pnf());
        }
        {
            let formula: Formula = "(P() | ? x. Q(x)) -> !z. R(z)".parse().unwrap();
            assert_debug_string("! x. (! z. ((P() | Q(x)) -> R(z)))", formula.pnf());
        }
        {
            let formula: Formula = "!x.?y.(!z.Q(x) & ~?x.R(x)) | (~Q(y) -> !w. R(y))"
                .parse()
                .unwrap();
            assert_debug_string(
                "! x. (? y. (! z. (! x`. (! w. ((Q(x) & (~R(x`))) | ((~Q(y)) -> R(y)))))))",
                formula.pnf(),
            );
        }
        {
            let formula: Formula = "!x. (!y. P(x, y) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string("! x. (! y. (? y`. (P(x, y) -> Q(x, y`))))", formula.pnf());
        }
        {
            let formula: Formula = "!x. ((!y. P(x, y)) -> ?y. Q(x, y))".parse().unwrap();
            assert_debug_string("! x. (? y. (? y`. (P(x, y) -> Q(x, y`))))", formula.pnf());
        }
    }

    #[test]
    fn test_snf() {
        assert_debug_string("P('sk#0)", exists1(_x(), P().app1(x())).snf());
        assert_debug_string(
            "! x. P(x, sk#0(x))",
            forall1(_x(), exists1(_y(), P().app2(x(), y()))).snf(),
        );
        assert_debug_string("P(x, sk#0(x))", exists1(_y(), P().app2(x(), y())).snf());
        assert_debug_string(
            "! x. P(x, f(g(sk#0(x)), h(sk#0(x))))",
            forall1(
                _x(),
                exists1(_y(), P().app2(x(), f().app2(g().app1(y()), h().app1(y())))),
            )
            .snf(),
        );
        assert_debug_string(
            "('sk#0 = 'sk#1) & ('sk#1 = 'sk#2)",
            exists3(_x(), _y(), _z(), x().equals(y()).and(y().equals(z()))).snf(),
        );
        assert_debug_string(
            "! y. (Q('sk#0, y) | P(sk#1(y), y, sk#2(y)))",
            exists1(
                _x(),
                forall1(
                    _y(),
                    Q().app2(x(), y())
                        .or(exists2(_x(), _z(), P().app3(x(), y(), z()))),
                ),
            )
            .snf(),
        );
        assert_debug_string(
            "! x. (! z. P(x, sk#0(x), z))",
            forall1(_x(), exists1(_y(), forall1(_z(), P().app3(x(), y(), z())))).snf(),
        );
        assert_debug_string(
            "! x. (R(g(x)) | R(x, sk#0(x)))",
            forall1(
                _x(),
                R().app1(g().app1(x()))
                    .or(exists1(_y(), R().app2(x(), y()))),
            )
            .snf(),
        );
        assert_debug_string(
            "! y. (! z. (! v. P('sk#0, y, z, sk#1(y, z), v, sk#2(y, z, v))))",
            exists1(
                _x(),
                forall1(
                    _y(),
                    forall1(
                        _z(),
                        exists1(
                            _u(),
                            forall1(
                                _v(),
                                exists1(_w(), P().app(vec![x(), y(), z(), u(), v(), w()])),
                            ),
                        ),
                    ),
                ),
            )
            .snf(),
        );
        {
            let mut generator = SkolemGenerator::new();
            assert_debug_string(
                "P('sk#0)",
                exists1(_x(), P().app1(x())).snf_with(&mut generator),
            );
            assert_debug_string(
                "Q('sk#1)",
                exists1(_x(), Q().app1(x())).snf_with(&mut generator),
            );
        }
    }

    #[test]
    fn test_nnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string("true", formula.nnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string("false", formula.nnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.nnf());
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_string("x = y", formula.nnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string("(~P(x)) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", formula.nnf());
        }
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string("? x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string("! x. P(x)", formula.nnf());
        }
        // sanity checking
        {
            let formula: Formula = "~true".parse().unwrap();
            assert_debug_string("false", formula.nnf());
        }
        {
            let formula: Formula = "~false".parse().unwrap();
            assert_debug_string("true", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~~x = y".parse().unwrap();
            assert_debug_string("x = y", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) & Q(y))".parse().unwrap();
            assert_debug_string("(~P(x)) | (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) | Q(y))".parse().unwrap();
            assert_debug_string("(~P(x)) & (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) -> Q(y))".parse().unwrap();
            assert_debug_string("P(x) & (~Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(P(x) <=> Q(y))".parse().unwrap();
            assert_debug_string("(P(x) & (~Q(y))) | ((~P(x)) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string("((~P(x)) & (~Q(y))) | R(z)", formula.nnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string(
                "(((~P(x)) & (~Q(y))) | R(z)) & ((P(x) | Q(y)) | (~R(z)))",
                formula.nnf(),
            );
        }
        {
            let formula: Formula = "~?x. P(x)".parse().unwrap();
            assert_debug_string("! x. (~P(x))", formula.nnf());
        }
        {
            let formula: Formula = "~!x. P(x)".parse().unwrap();
            assert_debug_string("? x. (~P(x))", formula.nnf());
        }
        // recursive application
        {
            let formula: Formula = "~~P(x) & ~~Q(y)".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) | ~~Q(y)".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) -> ~~Q(y)".parse().unwrap();
            assert_debug_string("(~P(x)) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~~P(x) <=> ~~Q(y)".parse().unwrap();
            assert_debug_string("((~P(x)) | Q(y)) & (P(x) | (~Q(y)))", formula.nnf());
        }
        {
            let formula: Formula = "?x. ~~P(x)".parse().unwrap();
            assert_debug_string("? x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "!x. ~~P(x)".parse().unwrap();
            assert_debug_string("! x. P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~~~P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) & ~Q(y))".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) | ~Q(y))".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~P(x) -> ~Q(y))".parse().unwrap();
            assert_debug_string("(~P(x)) & Q(y)", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) & ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string("(P(x) & Q(x)) | (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) | ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string("(P(x) & Q(x)) & (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) -> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string("((~P(x)) | (~Q(x))) & (P(y) & Q(y))", formula.nnf());
        }
        {
            let formula: Formula = "~(~(P(x) & Q(x)) <=> ~(P(y) & Q(y)))".parse().unwrap();
            assert_debug_string(
                "(((~P(x)) | (~Q(x))) & (P(y) & Q(y))) | ((P(x) & Q(x)) & ((~P(y)) | (~Q(y))))",
                formula.nnf(),
            );
        }
        {
            let formula: Formula = "~?x. !y. (P(x) -> Q(y))".parse().unwrap();
            assert_debug_string("! x. (? y. (P(x) & (~Q(y))))", formula.nnf());
        }
        {
            let formula: Formula = "~((?x. P(x)) & (!y. Q(y)))".parse().unwrap();
            assert_debug_string("(! x. (~P(x))) | (? y. (~Q(y)))", formula.nnf());
        }
    }

    #[test]
    fn test_cnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string("true", formula.cnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string("false", formula.cnf());
        }
        {
            let formula: Formula = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string("P(f(), g(f(), f()))", formula.cnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.cnf());
        }
        {
            let formula: Formula = "x=y".parse().unwrap();
            assert_debug_string("x = y", formula.cnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string("(~P(x)) | Q(y)", formula.cnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string("((~P(x)) | Q(y)) & ((~Q(y)) | P(x))", formula.cnf());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.cnf());
        }
        {
            let formula: Formula = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string("P(f(), g(f(), x))", formula.cnf());
        }
        // quantifier-free formulae
        {
            let formula: Formula = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string("((~P(x1)) | (~Q(y))) & ((~P(x2)) | (~Q(y)))", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string("(P(x) | Q(x)) & (P(x) | (~Q(y)))", formula.cnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string("((~P(x)) | R(z)) & ((~Q(y)) | R(z))", formula.cnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string("((P(x) | (Q(x) | Q(y))) & (P(x) | (Q(x) | (~Q(x))))) & ((P(x) | ((~Q(y)) | Q(y))) & (P(x) | ((~Q(y)) | (~Q(x)))))",
                                formula.cnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string(
                "(((~P(x)) | R(z)) & ((~Q(y)) | R(z))) & ((~R(z)) | (P(x) | Q(y)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string(
                "(P(x) | (Q(x) | R(y))) & (P(x) | (Q(x) | R(z)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string(
                "((P(x1) | Q(x1)) & (P(x1) | Q(x2))) & ((P(x2) | Q(x1)) & (P(x2) | Q(x2)))",
                formula.cnf(),
            );
        }
        //random formulae
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string("P('sk#0)", formula.cnf());
        }
        {
            let formula: Formula = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string("P('sk#0) & Q(f(), 'sk#0)", formula.cnf());
        }
        {
            let formula: Formula = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string("((~P(y)) | (~Q(x, y))) | R(x)", formula.cnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string("(~P(x)) | ((~Q(y)) | (~R(x, y)))", formula.cnf());
        }
        {
            let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string("((~P(y, x)) | Q(y)) & ((~Q(x)) | Q(y))", formula.cnf());
        }
        {
            let formula: Formula = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string(
                "((~P(y, sk#0(y))) | Q(y)) & ((~Q(sk#0(y))) | Q(y))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string("P('sk#0, 'sk#1)", formula.cnf());
        }
        {
            let formula: Formula = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string("P('sk#0, 'sk#1)", formula.cnf());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string("P(x, sk#0(x))", formula.cnf());
        }
        {
            let formula: Formula =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string("((~R(z)) | P(sk#0(z), x)) & (((~R(z)) | (~Q(u`, x`, y))) & ((~R(z)) | (~(w = f(u`)))))",
                                formula.cnf());
        }
        {
            let formula: Formula = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string(
                "(P(y) | Q(sk#0(x, y), x)) & ((~Q(x, y)) | Q(sk#0(x, y), x))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string(
                "(P(sk#0(x)) | Q(sk#1(x), x)) & ((~Q(x, sk#0(x))) | Q(sk#1(x), x))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string(
                "P('sk#0) & (((~Q('sk#0, y)) | (y = z)) | (~Q('sk#0, z)))",
                formula.cnf(),
            );
        }
        {
            let formula: Formula =
                "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                    .parse()
                    .unwrap();
            assert_debug_string("((~P(x)) | ((~P(y)) | P(f(x, y)))) & (((~P(x)) | Q(x, sk#0(x, y))) & ((~P(x)) | (~P(sk#0(x, y)))))",
                                formula.cnf());
        }
    }

    #[test]
    fn test_dnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_string("true", formula.dnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_string("false", formula.dnf());
        }
        {
            let formula: Formula = "P(f(), g(f(), f()))".parse().unwrap();
            assert_debug_string("P(f(), g(f(), f()))", formula.dnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.dnf());
        }
        {
            let formula: Formula = "x=y".parse().unwrap();
            assert_debug_string("x = y", formula.dnf());
        }
        {
            let formula: Formula = "P(x) & Q(y)".parse().unwrap();
            assert_debug_string("P(x) & Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | Q(y)".parse().unwrap();
            assert_debug_string("P(x) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) -> Q(y)".parse().unwrap();
            assert_debug_string("(~P(x)) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) <=> Q(y)".parse().unwrap();
            assert_debug_string(
                "(((~P(x)) & (~Q(y))) | ((~P(x)) & P(x))) | ((Q(y) & (~Q(y))) | (Q(y) & P(x)))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. P(f(), g(f(), x))".parse().unwrap();
            assert_debug_string("P(f(), g(f(), x))", formula.dnf());
        }
        // quantifier-free formulae
        {
            let formula: Formula = "~((P(x1) | P(x2)) and Q(y))".parse().unwrap();
            assert_debug_string("((~P(x1)) & (~P(x2))) | (~Q(y))", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) -> Q(y))".parse().unwrap();
            assert_debug_string("P(x) | (Q(x) & (~Q(y)))", formula.dnf());
        }
        {
            let formula: Formula = "(P(x) | Q(y)) -> R(z)".parse().unwrap();
            assert_debug_string("((~P(x)) & (~Q(y))) | R(z)", formula.dnf());
        }
        {
            let formula: Formula = "P(x) | ~(Q(x) <=> Q(y))".parse().unwrap();
            assert_debug_string(
                "P(x) | ((Q(x) & (~Q(y))) | (Q(y) & (~Q(x))))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "(P(x) | Q(y)) <=> R(z)".parse().unwrap();
            assert_debug_string("((((~P(x)) & (~Q(y))) & (~R(z))) | ((((~P(x)) & (~Q(y))) & P(x)) | (((~P(x)) & (~Q(y))) & Q(y)))) | ((R(z) & (~R(z))) | ((R(z) & P(x)) | (R(z) & Q(y))))",
                                formula.dnf());
        }
        {
            let formula: Formula = "P(x) | (Q(x) | (R(y) & R(z)))".parse().unwrap();
            assert_debug_string("P(x) | (Q(x) | (R(y) & R(z)))", formula.dnf());
        }
        {
            let formula: Formula = "(P(x1) & P(x2)) | (Q(x1) & Q(x2))".parse().unwrap();
            assert_debug_string("(P(x1) & P(x2)) | (Q(x1) & Q(x2))", formula.dnf());
        }

        //random formulae
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string("P('sk#0)", formula.dnf());
        }
        {
            let formula: Formula = "?x. (P(x) & Q(f(), x))".parse().unwrap();
            assert_debug_string("P('sk#0) & Q(f(), 'sk#0)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ((? y. P(y) & Q(x, y))  -> R(x))".parse().unwrap();
            assert_debug_string("((~P(y)) | (~Q(x, y))) | R(x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> !y. (Q(y) -> ~R(x, y)))".parse().unwrap();
            assert_debug_string("(~P(x)) | ((~Q(y)) | (~R(x, y)))", formula.dnf());
        }
        {
            let formula: Formula = "!y. (!x. (P(y, x) | Q(x)) -> Q(y))".parse().unwrap();
            assert_debug_string("((~P(y, x)) & (~Q(x))) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "!y. ((!x. (P(y, x) | Q(x))) -> Q(y))".parse().unwrap();
            assert_debug_string("((~P(y, sk#0(y))) & (~Q(sk#0(y)))) | Q(y)", formula.dnf());
        }
        {
            let formula: Formula = "?x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string("P('sk#0, 'sk#1)", formula.dnf());
        }
        {
            let formula: Formula = "?x, y. P(x, y)".parse().unwrap();
            assert_debug_string("P('sk#0, 'sk#1)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y)".parse().unwrap();
            assert_debug_string("P(x, sk#0(x))", formula.dnf());
        }
        {
            let formula: Formula =
                "R(z) -> ?u. (!x, y. (P(u, x) & ~? u, x, w. (Q(u, x, y) | (w = f(u)))))"
                    .parse()
                    .unwrap();
            assert_debug_string(
                "(~R(z)) | (P(sk#0(z), x) & ((~Q(u`, x`, y)) & (~(w = f(u`)))))",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "!x. (!y. (P(y) -> Q(x, y)) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string("(P(y) & (~Q(x, y))) | Q(sk#0(x, y), x)", formula.dnf());
        }
        {
            let formula: Formula = "!x. ((!y. (P(y) -> Q(x, y))) -> ?y. Q(y, x))"
                .parse()
                .unwrap();
            assert_debug_string(
                "(P(sk#0(x)) & (~Q(x, sk#0(x)))) | Q(sk#1(x), x)",
                formula.dnf(),
            );
        }
        {
            let formula: Formula = "?x. (!y, z. (P(x) & ((Q(x, y) & ~(y = z)) -> ~Q(x, z))))"
                .parse()
                .unwrap();
            assert_debug_string("((P('sk#0) & (~Q('sk#0, y))) | (P('sk#0) & (y = z))) | (P('sk#0) & (~Q('sk#0, z)))",
                                formula.dnf());
        }
        {
            let formula: Formula =
                "!x. (P(x) -> (!y. (P(y) -> P(f(x, y))) & ~!y. (Q(x, y) -> P(y))))"
                    .parse()
                    .unwrap();
            assert_debug_string("(~P(x)) | (((~P(y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))) | (P(f(x, y)) & (Q(x, sk#0(x, y)) & (~P(sk#0(x, y))))))",
                                formula.dnf());
        }
    }

    #[test]
    fn test_simplify() {
        {
            let formula: Formula = "~true".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "~false".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true & true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false & false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "false & true".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "true & false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & true".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "false & P(x)".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "true & P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) & Q(x)".parse().unwrap();
            assert_debug_string("P(x) & Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true | true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false | false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "false | true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "true | false".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false | P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | false".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true | P(x)".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) | Q(x)".parse().unwrap();
            assert_debug_string("P(x) | Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true -> true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> false".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "true -> false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false -> P(x)".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> false".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true -> P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_string("P(x) -> Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "true <=> true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false <=> false".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false <=> true".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "true <=> false".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> true".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "false <=> P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> false".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "true <=> P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "P(x) <=> Q(x)".parse().unwrap();
            assert_debug_string("P(x) <=> Q(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x, y. P(y, z)".parse().unwrap();
            assert_debug_string("? y. P(y, z)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(x)".parse().unwrap();
            assert_debug_string("? x. P(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(y)".parse().unwrap();
            assert_debug_string("P(y)", formula.simplify());
        }
        {
            let formula: Formula = "!x, y. P(y, z)".parse().unwrap();
            assert_debug_string("! y. P(y, z)", formula.simplify());
        }
        {
            let formula: Formula = "!x. P(x)".parse().unwrap();
            assert_debug_string("! x. P(x)", formula.simplify());
        }
        {
            let formula: Formula = "!x. P(y)".parse().unwrap();
            assert_debug_string("P(y)", formula.simplify());
        }
        // random formulae
        {
            let formula: Formula = "~~P(x)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "~~~P(x)".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "~(true -> false)".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "false | (P(x) & true)".parse().unwrap();
            assert_debug_string("P(x)", formula.simplify());
        }
        {
            let formula: Formula = "?x. P(x) | true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "?y. (P(x) -> false) & (false -> Q(x))".parse().unwrap();
            assert_debug_string("~P(x)", formula.simplify());
        }
        {
            let formula: Formula = "!x. ?y. P(x, y) | true".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "(((x = y -> false) -> false) -> false) -> false"
                .parse()
                .unwrap();
            assert_debug_string("x = y", formula.simplify());
        }
        {
            let formula: Formula = "!x, y, z. ?z. P(x) | w = x".parse().unwrap();
            assert_debug_string("! x. (P(x) | (w = x))", formula.simplify());
        }
        {
            let formula: Formula = "(P(x) | false) | (P(x) | true)".parse().unwrap();
            assert_debug_string("true", formula.simplify());
        }
        {
            let formula: Formula = "(P(x) & false) & (P(x) & true)".parse().unwrap();
            assert_debug_string("false", formula.simplify());
        }
    }

    #[test]
    fn test_gnf() {
        {
            let formula: Formula = "true".parse().unwrap();
            assert_debug_strings("true -> true", formula.gnf());
        }
        {
            let formula: Formula = "false".parse().unwrap();
            assert_debug_strings("true -> false", formula.gnf());
        }
        {
            let formula: Formula = "P(x)".parse().unwrap();
            assert_debug_strings("true -> P(x)", formula.gnf());
        }
        {
            let formula: Formula = "x = y".parse().unwrap();
            assert_debug_strings("true -> (x = y)", formula.gnf());
        }
        {
            let formula: Formula = "~P(x)".parse().unwrap();
            assert_debug_strings("P(x) -> false", formula.gnf());
        }
        {
            let formula: Formula = "P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings("P(x) -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) & Q(x)".parse().unwrap();
            assert_debug_strings("true -> P(x)\ntrue -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) | Q(x)".parse().unwrap();
            assert_debug_strings("true -> (P(x) | Q(x))", formula.gnf());
        }
        {
            let formula: Formula = "! x. P(x)".parse().unwrap();
            assert_debug_strings("true -> P(x)", formula.gnf());
        }
        {
            let formula: Formula = "? x. P(x)".parse().unwrap();
            assert_debug_strings("true -> P('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "P(x) & Q(x) -> P(y) | Q(y)".parse().unwrap();
            assert_debug_strings("(P(x) & Q(x)) -> (P(y) | Q(y))", formula.gnf());
        }
        {
            let formula: Formula = "P(x) | Q(x) -> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "P(x) | Q(x) <=> P(y) & Q(y)".parse().unwrap();
            assert_debug_strings(
                "P(x) -> P(y)\n\
        P(x) -> Q(y)\n\
        Q(x) -> P(y)\n\
        Q(x) -> Q(y)\n\
        (P(y) & Q(y)) -> (P(x) | Q(x))",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "!x. (P(x) -> ?y. Q(x,y))".parse().unwrap();
            assert_debug_strings("P(x) -> Q(x, sk#0(x))", formula.gnf());
        }
        {
            let formula: Formula = "!x. (P(x) -> (?y. (Q(y) & R(x, y)) | ?y. (P(y) & S(x, y)))))"
                .parse()
                .unwrap();
            assert_debug_strings(
                "P(x) -> (Q(sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (Q(sk#0(x)) | S(x, sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | P(sk#1(x)))\n\
        P(x) -> (R(x, sk#0(x)) | S(x, sk#1(x)))",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "!x, y. ((P(x) & Q(y)) -> (R(x, y) -> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings("((P(x) & Q(y)) & R(x, y)) -> S(x, y)", formula.gnf());
        }
        {
            let formula: Formula = "!x, y. ((P(x) & Q(y)) <=> (R(x, y) <=> S(x, y)))"
                .parse()
                .unwrap();
            assert_debug_strings(
                "((P(x) & Q(y)) & R(x, y)) -> S(x, y)\n\
        ((P(x) & Q(y)) & S(x, y)) -> R(x, y)\n\
        true -> ((R(x, y) | S(x, y)) | P(x))\n\
        true -> ((R(x, y) | S(x, y)) | Q(y))\n\
        R(x, y) -> (R(x, y) | P(x))\n\
        R(x, y) -> (R(x, y) | Q(y))\n\
        S(x, y) -> (S(x, y) | P(x))\n\
        S(x, y) -> (S(x, y) | Q(y))\n\
        (S(x, y) & R(x, y)) -> P(x)\n\
        (S(x, y) & R(x, y)) -> Q(y)",
                formula.gnf(),
            );
        }
        {
            let formula: Formula = "? x. P(x) -> Q(x)".parse().unwrap();
            assert_debug_strings("P('sk#0) -> Q('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "(? x. P(x)) -> Q(x)".parse().unwrap();
            assert_debug_strings("P(x`) -> Q(x)", formula.gnf());
        }
        {
            let formula: Formula = "? x. (P(x) -> Q(x))".parse().unwrap();
            assert_debug_strings("P('sk#0) -> Q('sk#0)", formula.gnf());
        }
        {
            let formula: Formula = "false -> P(x)".parse().unwrap();
            assert_debug_strings("true -> true", formula.gnf());
        }
    }

    #[test]
    fn test_gnf_theory() {
        // mostly testing if compression of heads works properly:
        {
            let theory: Theory = "P('a); P('b);".parse().unwrap();
            assert_debug_strings("true -> (P('a) & P('b))", theory.gnf().formulae);
        }
        {
            let theory: Theory = "P('a); P(x);".parse().unwrap();
            assert_debug_strings("true -> P(x)\ntrue -> P('a)", theory.gnf().formulae);
        }
        {
            let theory: Theory = "P('a); P(x); P('b);".parse().unwrap();
            assert_debug_strings(
                "true -> P(x)\ntrue -> (P(\'a) & P(\'b))",
                theory.gnf().formulae,
            );
        }
        {
            let theory: Theory = "(T() and V()) or (U() and V());".parse().unwrap();
            assert_debug_strings("true -> ((T() & V()) | (U() & V()))", theory.gnf().formulae);
        }
    }
}
