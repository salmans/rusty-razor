use criterion::{Criterion, criterion_group, criterion_main};
use rusty_razor::{
    chase::{
        Selector,
        Strategy,
        StrategyNode,
        bounder::DomainSize,
        r#impl::basic::{BasicEvaluator, BasicModel, BasicSequent},
        selector::{Bootstrap, Fair, Linear},
        solve_all,
        strategy::FIFO,
    },
    formula::{parser::parse_theory, syntax::Theory},
};
use std::{fs, io::Read};

fn basic_benchmark(c: &mut Criterion) {
    c.bench_function("basic", |b| b.iter(|| time_basic()));
}

fn bootstrap_benchmark(c: &mut Criterion) {
    c.bench_function("bootstrap", |b| b.iter(|| time_bootstrap()));
}

fn time_basic() {
    for item in fs::read_dir("theories/core").unwrap() {
        let theory = read_theory_from_file(item.unwrap().path().display().to_string().as_str());
        solve_basic(&theory);
    }
}

fn solve_basic(theory: &Theory) -> Vec<BasicModel> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<BasicSequent> = geometric_theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = BasicEvaluator {};
    let selector = Linear::new(sequents);
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(StrategyNode::new(BasicModel::new(), selector));
    solve_all(Box::new(strategy), Box::new(evaluator), bounder)
}

fn time_bootstrap() {
    for item in fs::read_dir("theories/core").unwrap() {
        let theory = read_theory_from_file(item.unwrap().path().display().to_string().as_str());
        solve_bootstrap(&theory);
    }
}

fn solve_bootstrap(theory: &Theory) -> Vec<BasicModel> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<BasicSequent> = geometric_theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = BasicEvaluator {};
    let selector: Bootstrap<BasicSequent, Fair<BasicSequent>> = Bootstrap::new(sequents);
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(StrategyNode::new(BasicModel::new(), selector));
    solve_all(Box::new(strategy), Box::new(evaluator), bounder)
}

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = fs::File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    parse_theory(contents.as_str())
}

criterion_group!(benches, basic_benchmark, bootstrap_benchmark);
criterion_main!(benches);