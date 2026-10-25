//! Checks the conversion to geometric form against every structure on a tiny domain: a
//! structure for the signature of a formula satisfies the formula exactly when some expansion of
//! it over the symbols the conversion introduced satisfies the sequents. Functions and constants
//! are partial, as in the chase: an atom or an equation over an undefined term is false.
use razor_fol::{
    syntax::{term::Complex, Formula, Var, EQ_SYM, FOF},
    transform::{Geometrization, Symbols, ToGNF, ToPNF, GNF},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt,
    ops::Range,
};

const SIZES: [usize; 3] = [1, 2, 3];

// The most pairs of a structure and an expansion one domain size may enumerate.
const BUDGET: u128 = 1 << 14;

const FORMULAS: u64 = 300;

const POLICIES: [Geometrization; 3] = [
    Geometrization::Skolemize,
    Geometrization::Define,
    Geometrization::Hybrid,
];

// The number of formulas a sweep draws, `RAZOR_CHECK_FORMULAS` or `FORMULAS`.
fn formulas() -> u64 {
    std::env::var("RAZOR_CHECK_FORMULAS")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(FORMULAS)
}

// A seeded xorshift source of choices, so a formula is reproducible from its seed.
struct Dice(u64);

impl Dice {
    fn new(seed: u64) -> Self {
        Dice(seed.wrapping_mul(2_654_435_761).wrapping_add(12_345))
    }

    // A number in `0..n`.
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

// Draws the text of a formula over `P/1`, `Q/2`, `R/1`, `f/1` and `'a`, with the variables
// `x`, `y` and `z`, so bound names shadow each other and the free `x` sometimes.
struct Draw {
    dice: Dice,
    variables: Vec<&'static str>,
    quantifiers: usize,
}

impl Draw {
    const DEPTH: u32 = 4;
    const QUANTIFIERS: usize = 3;
    const NAMES: [&'static str; 3] = ["x", "y", "z"];

    fn new(seed: u64) -> Self {
        let mut dice = Dice::new(seed);
        let variables = if dice.below(3) == 0 {
            vec!["x"]
        } else {
            vec![]
        };
        Self {
            dice,
            variables,
            quantifiers: 0,
        }
    }

    fn formula(&mut self, depth: u32) -> String {
        if depth == 0 || self.dice.below(4) == 0 {
            return self.atom();
        }
        match self.dice.below(9) {
            0 => format!("~({})", self.formula(depth - 1)),
            1 => self.connective("&", depth),
            2 => self.connective("|", depth),
            3 => self.connective("->", depth),
            4..=6 => self.quantified("exists", depth),
            _ => self.quantified("forall", depth),
        }
    }

    fn connective(&mut self, connective: &str, depth: u32) -> String {
        let left = self.formula(depth - 1);
        let right = self.formula(depth - 1);
        format!("({}) {} ({})", left, connective, right)
    }

    fn quantified(&mut self, quantifier: &str, depth: u32) -> String {
        if self.quantifiers == Self::QUANTIFIERS {
            return self.atom();
        }
        let variable = Self::NAMES[self.dice.below(Self::NAMES.len())];
        self.variables.push(variable);
        self.quantifiers += 1;
        let scope = self.formula(depth - 1);
        self.quantifiers -= 1;
        self.variables.pop();
        format!("{} {}. ({})", quantifier, variable, scope)
    }

    fn atom(&mut self) -> String {
        match self.dice.below(12) {
            0 => "true".into(),
            1 => "false".into(),
            2 | 3 => format!("{} = {}", self.term(), self.term()),
            4..=6 => format!("P({})", self.term()),
            7 | 8 => format!("Q({}, {})", self.term(), self.term()),
            _ => format!("R({})", self.term()),
        }
    }

    fn term(&mut self) -> String {
        match self.dice.below(10) {
            0 => "'a".into(),
            1 => format!("f({})", self.variable()),
            _ => self.variable(),
        }
    }

    fn variable(&mut self) -> String {
        if self.variables.is_empty() || self.dice.below(8) == 0 {
            "'a".into()
        } else {
            self.variables[self.dice.below(self.variables.len())].into()
        }
    }
}

fn random_formula(seed: u64) -> FOF {
    let text = Draw::new(seed).formula(Draw::DEPTH);
    text.parse()
        .unwrap_or_else(|_| panic!("seed {} drew `{}`", seed, text))
}

// The universal closure of `formula`.
fn closure(formula: FOF) -> FOF {
    let free: Vec<Var> = formula.free_vars().into_iter().cloned().collect();
    if free.is_empty() {
        formula
    } else {
        FOF::forall(free, formula)
    }
}

// The relations, functions and constants a structure interprets, with their arities.
#[derive(Default)]
struct Vocabulary {
    relations: BTreeMap<String, usize>,
    functions: BTreeMap<String, usize>,
    constants: BTreeSet<String>,
}

impl Vocabulary {
    fn of(formulas: &[FOF]) -> Self {
        let mut vocabulary = Self::default();
        for formula in formulas {
            let sig = formula.signature().unwrap();
            for (name, predicate) in sig.predicates() {
                if name != EQ_SYM {
                    vocabulary
                        .relations
                        .insert(name.clone(), predicate.arity as usize);
                }
            }
            for (name, function) in sig.functions() {
                vocabulary
                    .functions
                    .insert(name.clone(), function.arity as usize);
            }
            for constant in sig.constants() {
                vocabulary.constants.insert(constant.name().to_string());
            }
        }
        vocabulary
    }

    // The symbols of `self` that `other` lacks.
    fn without(&self, other: &Self) -> Self {
        let missing = |map: &BTreeMap<String, usize>, known: &BTreeMap<String, usize>| {
            map.iter()
                .filter(|(name, _)| !known.contains_key(*name))
                .map(|(name, arity)| (name.clone(), *arity))
                .collect()
        };
        Self {
            relations: missing(&self.relations, &other.relations),
            functions: missing(&self.functions, &other.functions),
            constants: self
                .constants
                .difference(&other.constants)
                .cloned()
                .collect(),
        }
    }

    fn is_empty(&self) -> bool {
        self.relations.is_empty() && self.functions.is_empty() && self.constants.is_empty()
    }
}

#[derive(Clone, Copy)]
enum Kind {
    Relation,
    Function,
    Constant,
}

// The cells of one symbol: a cell per tuple of the domain, holding a truth value for a
// relation, and an element or `size` (undefined) for a function or a constant.
struct Table {
    kind: Kind,
    name: String,
    arity: usize,
    offset: usize,
}

// The structures for a source vocabulary over the domain `0..size`, each with the expansions
// over a second vocabulary, laid out as one vector of cells with the source's first.
struct Structures {
    size: usize,
    tables: Vec<Table>,
    offsets: [HashMap<String, usize>; 3],
    ranges: Vec<usize>,
    source: usize,
}

impl Structures {
    fn new(size: usize, source: &Vocabulary, expansion: &Vocabulary) -> Self {
        let mut structures = Self {
            size,
            tables: Vec::new(),
            offsets: Default::default(),
            ranges: Vec::new(),
            source: 0,
        };
        structures.add(source);
        structures.source = structures.ranges.len();
        structures.add(expansion);
        structures
    }

    fn add(&mut self, vocabulary: &Vocabulary) {
        let symbols = vocabulary
            .relations
            .iter()
            .map(|(name, arity)| (Kind::Relation, name, *arity))
            .chain(
                (vocabulary.functions.iter()).map(|(name, arity)| (Kind::Function, name, *arity)),
            )
            .chain((vocabulary.constants.iter()).map(|name| (Kind::Constant, name, 0)));
        for (kind, name, arity) in symbols {
            let range = match kind {
                Kind::Relation => 2,
                Kind::Function | Kind::Constant => self.size + 1,
            };
            self.offsets[kind as usize].insert(name.clone(), self.ranges.len());
            self.tables.push(Table {
                kind,
                name: name.clone(),
                arity,
                offset: self.ranges.len(),
            });
            let cells = self.size.pow(arity as u32);
            self.ranges.extend(std::iter::repeat_n(range, cells));
        }
    }

    // The number of pairs of a structure and an expansion, saturating.
    fn count(&self) -> u128 {
        (self.ranges.iter()).fold(1u128, |count, range| count.saturating_mul(*range as u128))
    }

    // The cell of the tuple numbered `code` in the table of `name`.
    fn cell(&self, kind: Kind, name: &str, code: usize) -> usize {
        self.offsets[kind as usize][name] + code
    }

    // Steps the cells in `range` to their next combination of values, the first fastest; false
    // when they wrap around to all zeros.
    fn advance(&self, cells: &mut [usize], range: Range<usize>) -> bool {
        for i in range {
            cells[i] += 1;
            if cells[i] < self.ranges[i] {
                return true;
            }
            cells[i] = 0;
        }
        false
    }

    // The first source structure whose truth of `formula` differs from whether one of its
    // expansions satisfies every sequent of `sequents`.
    fn mismatch(&self, formula: &FOF, sequents: &[FOF]) -> Option<Mismatch> {
        let mut cells = vec![0; self.ranges.len()];
        loop {
            let holds = self.structure(&cells).satisfies(formula);
            if holds != self.expands(&mut cells, sequents) {
                return Some(Mismatch {
                    holds,
                    structure: self.structure(&cells).to_string(),
                });
            }
            if !self.advance(&mut cells, 0..self.source) {
                return None;
            }
        }
    }

    // Whether an expansion of the source structure in `cells` satisfies every sequent; leaves
    // the expansion's cells at zero.
    fn expands(&self, cells: &mut [usize], sequents: &[FOF]) -> bool {
        loop {
            if sequents.iter().all(|s| self.structure(cells).satisfies(s)) {
                cells[self.source..].fill(0);
                return true;
            }
            if !self.advance(cells, self.source..self.ranges.len()) {
                return false;
            }
        }
    }

    // The number of source structures that satisfy `formula`.
    fn models(&self, formula: &FOF) -> usize {
        let mut cells = vec![0; self.ranges.len()];
        let mut models = 0;
        loop {
            if self.structure(&cells).satisfies(formula) {
                models += 1;
            }
            if !self.advance(&mut cells, 0..self.source) {
                return models;
            }
        }
    }

    fn structure<'s>(&'s self, cells: &'s [usize]) -> Structure<'s> {
        Structure {
            structures: self,
            cells,
        }
    }
}

#[derive(Clone, Copy)]
enum Quantifier {
    Exists,
    Forall,
}

// One structure of a `Structures`: the truth of a formula and the value of a term in it.
struct Structure<'s> {
    structures: &'s Structures,
    cells: &'s [usize],
}

impl Structure<'_> {
    fn satisfies(&self, formula: &FOF) -> bool {
        self.holds(formula, &mut Vec::new())
    }

    fn holds<'f>(&self, formula: &'f FOF, env: &mut Vec<(&'f Var, usize)>) -> bool {
        match formula {
            FOF::Top => true,
            FOF::Bottom => false,
            FOF::Atom(atom) => self.code(&atom.terms, env).is_some_and(|code| {
                let cell = (self.structures).cell(Kind::Relation, atom.predicate.name(), code);
                self.cells[cell] == 1
            }),
            FOF::Equals(equals) => match (
                self.value(&equals.left, env),
                self.value(&equals.right, env),
            ) {
                (Some(left), Some(right)) => left == right,
                _ => false,
            },
            FOF::Not(not) => !self.holds(&not.formula, env),
            FOF::And(and) => self.holds(&and.left, env) && self.holds(&and.right, env),
            FOF::Or(or) => self.holds(&or.left, env) || self.holds(&or.right, env),
            FOF::Implies(implies) => {
                !self.holds(&implies.premise, env) || self.holds(&implies.consequence, env)
            }
            FOF::Iff(iff) => self.holds(&iff.left, env) == self.holds(&iff.right, env),
            FOF::Exists(exists) => {
                self.quantified(Quantifier::Exists, &exists.variables, &exists.formula, env)
            }
            FOF::Forall(forall) => {
                self.quantified(Quantifier::Forall, &forall.variables, &forall.formula, env)
            }
        }
    }

    fn quantified<'f>(
        &self,
        quantifier: Quantifier,
        variables: &'f [Var],
        scope: &'f FOF,
        env: &mut Vec<(&'f Var, usize)>,
    ) -> bool {
        let Some((variable, rest)) = variables.split_first() else {
            return self.holds(scope, env);
        };
        for element in 0..self.structures.size {
            env.push((variable, element));
            let holds = self.quantified(quantifier, rest, scope, env);
            env.pop();
            match (quantifier, holds) {
                (Quantifier::Exists, true) => return true,
                (Quantifier::Forall, false) => return false,
                _ => {}
            }
        }
        matches!(quantifier, Quantifier::Forall)
    }

    // The value of `term`, or none where it applies a function or names a constant outside its
    // domain of definition.
    fn value(&self, term: &Complex, env: &[(&Var, usize)]) -> Option<usize> {
        let cell = match term {
            Complex::Var(variable) => {
                let bound = env.iter().rev().find(|(v, _)| *v == variable);
                return Some(bound.unwrap_or_else(|| panic!("`{}` is free", variable)).1);
            }
            Complex::Const(constant) => (self.structures).cell(Kind::Constant, constant.name(), 0),
            Complex::App { function, terms } => {
                let code = self.code(terms, env)?;
                (self.structures).cell(Kind::Function, function.name(), code)
            }
        };
        Some(self.cells[cell]).filter(|element| *element < self.structures.size)
    }

    // The number of the tuple of the values of `terms`, the last digit fastest.
    fn code(&self, terms: &[Complex], env: &[(&Var, usize)]) -> Option<usize> {
        terms.iter().try_fold(0, |code, term| {
            Some(code * self.structures.size + self.value(term, env)?)
        })
    }
}

impl fmt::Display for Structure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let size = self.structures.size;
        for table in &self.structures.tables {
            let tuples = (0..size.pow(table.arity as u32)).map(|code| {
                let tuple: Vec<usize> = (0..table.arity)
                    .rev()
                    .map(|i| code / size.pow(i as u32) % size)
                    .collect();
                (tuple, self.cells[table.offset + code])
            });
            let entries: Vec<String> = match table.kind {
                Kind::Relation => tuples
                    .filter(|(_, cell)| *cell == 1)
                    .map(|(tuple, _)| format!("{:?}", tuple))
                    .collect(),
                Kind::Function | Kind::Constant => tuples
                    .filter(|(_, cell)| *cell < size)
                    .map(|(tuple, cell)| format!("{:?} -> {}", tuple, cell))
                    .collect(),
            };
            write!(f, "{}: {{{}}} ", table.name, entries.join(", "))?;
        }
        Ok(())
    }
}

// A source structure on which a formula and its sequents disagree.
struct Mismatch {
    holds: bool,
    structure: String,
}

// A formula and the sequents a route converted it to, both read as closed formulae.
struct Conversion {
    formula: FOF,
    sequents: Vec<FOF>,
    source: Vocabulary,
    introduced: Vocabulary,
}

impl Conversion {
    fn new(formula: &FOF, sequents: &[GNF]) -> Self {
        let formula = closure(formula.clone());
        let sequents: Vec<FOF> = (sequents.iter())
            .map(|sequent| closure(sequent.clone().into()))
            .collect();
        let source = Vocabulary::of(std::slice::from_ref(&formula));
        let introduced = Vocabulary::of(&sequents).without(&source);
        Self {
            formula,
            sequents,
            source,
            introduced,
        }
    }

    // The largest domain size checked within `BUDGET`, or the first mismatch.
    fn check(&self) -> Result<usize, String> {
        let mut checked = 0;
        for size in SIZES {
            let structures = Structures::new(size, &self.source, &self.introduced);
            if structures.count() > BUDGET {
                break;
            }
            if let Some(mismatch) = structures.mismatch(&self.formula, &self.sequents) {
                return Err(format!(
                    "size {}: the formula is {} but {} expansion satisfies the sequents\n  \
                     structure: {}\n  sequents:\n    {}",
                    size,
                    mismatch.holds,
                    if mismatch.holds { "no" } else { "some" },
                    mismatch.structure,
                    (self.sequents.iter().map(|s| s.to_string()))
                        .collect::<Vec<_>>()
                        .join("\n    "),
                ));
            }
            checked = size;
        }
        Ok(checked)
    }
}

// The way a formula reaches geometric form.
#[derive(Clone, Copy, Debug)]
enum Route {
    Direct(Geometrization),
    Prenex,
}

impl Route {
    fn convert(self, formula: &FOF) -> Vec<GNF> {
        let mut symbols = Symbols::default();
        match self {
            Route::Direct(policy) => formula.gnf_with(policy, &mut symbols),
            Route::Prenex => formula
                .pnf()
                .gnf_with(Geometrization::Skolemize, &mut symbols),
        }
    }
}

// The outcome of checking a route on the drawn formulas: how many reached each largest domain
// size within the budget (none at index 0), and the mismatches.
struct Sweep {
    route: Route,
    reached: [usize; 4],
    mismatches: Vec<String>,
}

impl Sweep {
    // Checks `route` on every drawn formula that `selects` its conversion.
    fn run(route: Route, selects: impl Fn(&Conversion) -> bool) -> Self {
        let mut sweep = Self {
            route,
            reached: [0; 4],
            mismatches: Vec::new(),
        };
        for seed in 1..=formulas() {
            let formula = random_formula(seed);
            let conversion = Conversion::new(&formula, &route.convert(&formula));
            if !selects(&conversion) {
                continue;
            }
            match conversion.check() {
                Ok(size) => sweep.reached[size] += 1,
                Err(mismatch) => {
                    (sweep.mismatches).push(format!("seed {}: {}\n  {}", seed, formula, mismatch))
                }
            }
        }
        println!("{}", sweep);
        sweep
    }

    fn checked(&self) -> usize {
        self.reached[1..].iter().sum()
    }

    fn assert_agrees(&self) {
        assert!(
            self.mismatches.is_empty(),
            "{:?}:\n{}",
            self.route,
            self.mismatches.join("\n")
        );
    }
}

impl fmt::Display for Sweep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}: checked through size 3: {}, 2: {}, 1: {}; over budget at every size: {}; mismatches: {}",
            self.route,
            self.reached[3],
            self.reached[2],
            self.reached[1],
            self.reached[0],
            self.mismatches.len()
        )
    }
}

fn conversion(route: Route, text: &str) -> Conversion {
    let formula: FOF = text.parse().unwrap();
    Conversion::new(&formula, &route.convert(&formula))
}

fn models(text: &str, size: usize) -> usize {
    let formula: FOF = text.parse().unwrap();
    let vocabulary = Vocabulary::of(std::slice::from_ref(&formula));
    Structures::new(size, &vocabulary, &Vocabulary::default()).models(&formula)
}

#[test]
fn a_seed_draws_the_same_formula() {
    assert_eq!(random_formula(7), random_formula(7));
    assert_eq!("∃ y. ((∃ z. P(y)) ∨ P(y))", random_formula(7).to_string());
}

#[test]
fn a_satisfiable_formula_has_a_model_on_every_domain() {
    assert!(SIZES.iter().all(|size| models("exists x. P(x)", *size) > 0));
}

#[test]
fn an_unsatisfiable_formula_has_no_model() {
    assert!(SIZES
        .iter()
        .all(|size| models("P('a) & ~P('a)", *size) == 0));
}

#[test]
fn only_the_empty_structure_satisfies_a_formula_that_denies_every_fact() {
    let text = "forall x. (~P(x) & ~(x = 'a))";
    assert!(SIZES.iter().all(|size| models(text, *size) == 1));
}

#[test]
fn a_conversion_that_drops_a_conjunct_is_caught() {
    let formula: FOF = "P('a) & Q('a, 'a)".parse().unwrap();
    let dropped: FOF = "P('a)".parse().unwrap();
    assert!(Conversion::new(&formula, &formula.gnf()).check().is_ok());
    assert!(Conversion::new(&formula, &dropped.gnf()).check().is_err());
}

#[test]
fn the_conversion_is_equisatisfiable_under_every_policy() {
    for policy in POLICIES {
        Sweep::run(Route::Direct(policy), |_| true).assert_agrees();
    }
}

#[test]
fn the_conversion_is_equivalent_when_nothing_is_removed() {
    for policy in POLICIES {
        let sweep = Sweep::run(Route::Direct(policy), |c| c.introduced.is_empty());
        sweep.assert_agrees();
        assert!(sweep.checked() > 0);
    }
}

#[test]
fn the_prenex_route_is_equisatisfiable() {
    Sweep::run(Route::Prenex, |_| true).assert_agrees();
}

#[test]
fn the_prenex_route_keeps_a_shadowing_universal_bound() {
    let conversion = conversion(Route::Prenex, "(exists x. forall x. P(x)) | R(x)");
    assert!(conversion.check().is_ok());
}

#[test]
fn the_prenex_route_is_equisatisfiable_on_a_denial_of_two_universals() {
    let text = "((forall y. P(y)) & (forall z. R(z))) -> false";
    assert!(conversion(Route::Prenex, text).check().is_ok());
}

#[test]
fn the_prenex_route_keeps_a_skolem_term_apart_from_a_shadowing_universal() {
    let text = "forall x. exists y. forall x. Q(x, y)";
    assert!(conversion(Route::Prenex, text).check().is_ok());
}
