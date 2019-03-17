use criterion::{Criterion, criterion_group, criterion_main};
use rusty_razor::{
    chase::{
        SelectorTrait,
        StrategyTrait,
        bounder::DomainSize,
        r#impl,
        selector::{Bootstrap, Fair, Linear},
        solve_all,
        strategy::FIFO,
    },
    formula::{parser::parse_theory, syntax::Theory},
};
use std::{fs, io::Read};

fn basic_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("theories/core").unwrap()
        .map(|item| read_theory_from_file(item.unwrap()
            .path().display().to_string().as_str())
            .gnf()
        ).collect();
    c.bench_function("basic", |b| b.iter(|| time_basic(theories)));
}

fn bootstrap_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("theories/core").unwrap()
        .map(|item| read_theory_from_file(item.unwrap()
            .path().display().to_string().as_str())
            .gnf()
        ).collect();
    c.bench_function("bootstrap", |b| b.iter(|| time_bootstrap(theories)));
}

fn referenced_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("theories/core").unwrap()
        .map(|item| read_theory_from_file(item.unwrap()
            .path().display().to_string().as_str())
            .gnf()
        ).collect();
    c.bench_function("referenced", |b| b.iter(|| time_referenced(theories)));
}

fn time_basic(theories: &Vec<Theory>) {
    for theory in theories {
        solve_basic(&theory);
    }
}

fn solve_basic(theory: &Theory) -> Vec<r#impl::basic::Model> {
    let sequents: Vec<r#impl::basic::Sequent> = theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = r#impl::basic::Evaluator {};
    let selector = Linear::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::basic::Model::new(), selector);
    solve_all(Box::new(strategy), Box::new(evaluator), bounder)
}

fn time_bootstrap(theories: &Vec<Theory>) {
    for theory in theories {
        solve_bootstrap(&theory);
    }
}

fn solve_bootstrap(theory: &Theory) -> Vec<r#impl::basic::Model> {
    let sequents: Vec<r#impl::basic::Sequent> = theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = r#impl::basic::Evaluator {};
    let selector: Bootstrap<r#impl::basic::Sequent, Fair<r#impl::basic::Sequent>> = Bootstrap::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::basic::Model::new(), selector);
    solve_all(Box::new(strategy), Box::new(evaluator), bounder)
}

fn time_referenced(theories: &Vec<Theory>) {
    for theory in theories {
        solve_referenced(&theory);
    }
}

fn solve_referenced(theory: &Theory) -> Vec<r#impl::reference::Model> {
    let sequents: Vec<r#impl::reference::Sequent> = theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = r#impl::reference::Evaluator {};
    let selector: Bootstrap<r#impl::reference::Sequent, Fair<r#impl::reference::Sequent>> = Bootstrap::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::reference::Model::new(), selector);
    solve_all(Box::new(strategy), Box::new(evaluator), bounder)
}

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = fs::File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    parse_theory(contents.as_str())
}

criterion_group!(benches, basic_benchmark, bootstrap_benchmark, referenced_benchmark);
criterion_main!(benches);