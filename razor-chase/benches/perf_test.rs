use criterion::{criterion_group, criterion_main, Criterion};
use razor_chase::chase::{
    bounder::DomainSize,
    chase_all, r#impl,
    scheduler::FIFO,
    strategy::{Bootstrap, Fair, Linear},
    SchedulerTrait, StrategyTrait,
};
use razor_fol::syntax::Theory;
use std::{fs, io::Read};

fn basic_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("../theories/core")
        .unwrap()
        .map(|item| {
            read_theory_from_file(item.unwrap().path().display().to_string().as_str()).gnf()
        })
        .collect();
    c.bench_function("basic", |b| b.iter(|| time_basic(theories)));
}

fn bootstrap_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("../theories/core")
        .unwrap()
        .map(|item| {
            read_theory_from_file(item.unwrap().path().display().to_string().as_str()).gnf()
        })
        .collect();
    c.bench_function("bootstrap", |b| b.iter(|| time_bootstrap(theories)));
}

fn reference_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("../theories/core")
        .unwrap()
        .map(|item| {
            read_theory_from_file(item.unwrap().path().display().to_string().as_str()).gnf()
        })
        .collect();
    c.bench_function("reference", |b| b.iter(|| time_reference(theories)));
}

fn batch_benchmark(c: &mut Criterion) {
    let theories = &fs::read_dir("../theories/core")
        .unwrap()
        .map(|item| {
            read_theory_from_file(item.unwrap().path().display().to_string().as_str()).gnf()
        })
        .collect();
    c.bench_function("batch", |b| b.iter(|| time_batch(theories)));
}

fn time_basic(theories: &Vec<Theory>) {
    for theory in theories {
        solve_basic(&theory);
    }
}

fn solve_basic(theory: &Theory) -> Vec<r#impl::basic::Model> {
    let sequents: Vec<r#impl::basic::Sequent> = theory.formulae.iter().map(|f| f.into()).collect();

    let evaluator = r#impl::basic::Evaluator {};
    let selector = Linear::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::basic::Model::new(), selector);
    chase_all(&mut strategy, &evaluator, bounder)
}

fn time_bootstrap(theories: &Vec<Theory>) {
    for theory in theories {
        solve_bootstrap(&theory);
    }
}

fn solve_bootstrap(theory: &Theory) -> Vec<r#impl::basic::Model> {
    let sequents: Vec<r#impl::basic::Sequent> = theory.formulae.iter().map(|f| f.into()).collect();

    let evaluator = r#impl::basic::Evaluator {};
    let selector: Bootstrap<r#impl::basic::Sequent, Fair<r#impl::basic::Sequent>> =
        Bootstrap::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::basic::Model::new(), selector);
    chase_all(&mut strategy, &evaluator, bounder)
}

fn time_reference(theories: &Vec<Theory>) {
    for theory in theories {
        solve_reference(&theory);
    }
}

fn solve_reference(theory: &Theory) -> Vec<r#impl::reference::Model> {
    let sequents: Vec<r#impl::reference::Sequent> =
        theory.formulae.iter().map(|f| f.into()).collect();

    let evaluator = r#impl::reference::Evaluator {};
    let selector: Bootstrap<r#impl::reference::Sequent, Fair<r#impl::reference::Sequent>> =
        Bootstrap::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::reference::Model::new(), selector);
    chase_all(&mut strategy, &evaluator, bounder)
}

fn time_batch(theories: &Vec<Theory>) {
    for theory in theories {
        solve_batch(&theory);
    }
}

fn solve_batch(theory: &Theory) -> Vec<r#impl::reference::Model> {
    let sequents: Vec<r#impl::reference::Sequent> =
        theory.formulae.iter().map(|f| f.into()).collect();

    let evaluator = r#impl::batch::Evaluator {};
    let selector: Bootstrap<r#impl::reference::Sequent, Fair<r#impl::reference::Sequent>> =
        Bootstrap::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(r#impl::reference::Model::new(), selector);
    chase_all(&mut strategy, &evaluator, bounder)
}

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = fs::File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    contents.parse().unwrap()
}

criterion_group!(
    benches,
    basic_benchmark,
    bootstrap_benchmark,
    reference_benchmark,
    batch_benchmark
);
criterion_main!(benches);
