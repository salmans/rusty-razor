use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use itertools::Itertools;
use razor_chase::chase::{
    chase_all,
    r#impl::*,
    scheduler::FIFO,
    strategy::{Bootstrap, Fair},
    PreProcessor, Scheduler, Unbounded,
};
use razor_fol::{
    syntax::{Theory, FOF},
    transform::Geometrization,
};
use std::{fs, io::Read};

macro_rules! read_theory {
    ($file_name: expr) => {{
        let mut f = fs::File::open($file_name).expect("file not found");
        let mut contents = String::new();
        f.read_to_string(&mut contents)
            .expect("something went wrong reading the file");

        contents.parse::<Theory<FOF>>().unwrap()
    }};
}

/// The core fixtures every bench skips: thy50 does not terminate under
/// `Geometrization::Define`, and the sets must be equal for the benches to be comparable.
const SKIPPED: [&str; 1] = ["thy50.raz"];

macro_rules! run_unbounded {
    (
        $name: literal,
        pre_processor = $prep: expr,
        evaluator = $eval: expr,
        sequent = $seq: path,
        model = $model: path,
        $crit: ident
    ) => {{
        fn solve(theory: &Theory<FOF>) -> Vec<$model> {
            let (sequents, init_model) = $prep.pre_process(theory);
            let evaluator = $eval;
            let selector: Bootstrap<&$seq, Fair<$seq>> = sequents.iter().collect();
            let mut strategy = FIFO::new();
            strategy.add(init_model, selector);
            chase_all(&mut strategy, &evaluator, &Unbounded)
        }

        fn run_bench(b: &mut Bencher) {
            let theories = &fs::read_dir("../theories/core")
                .unwrap()
                .map(|item| item.unwrap().path())
                .filter(|p| p.extension().map_or(false, |e| e == "raz"))
                .filter(|p| !SKIPPED.iter().any(|s| p.ends_with(s)))
                .map(|p| read_theory!(p.display().to_string()))
                .collect_vec();

            b.iter(|| {
                for theory in theories {
                    solve(&theory);
                }
            })
        }
        $crit.bench_function($name, run_bench);
    }};
}

fn bench_relational(c: &mut Criterion) {
    run_unbounded!(
        "relational_skolemize",
        pre_processor = relational::RelPreProcessor::new(Geometrization::Skolemize),
        evaluator = relational::RelEvaluator,
        sequent = relational::RelSequent,
        model = relational::RelModel,
        c
    );
    run_unbounded!(
        "relational_define",
        pre_processor = relational::RelPreProcessor::new(Geometrization::Define),
        evaluator = relational::RelEvaluator,
        sequent = relational::RelSequent,
        model = relational::RelModel,
        c
    );
    run_unbounded!(
        "relational_hybrid",
        pre_processor = relational::RelPreProcessor::new(Geometrization::default()),
        evaluator = relational::RelEvaluator,
        sequent = relational::RelSequent,
        model = relational::RelModel,
        c
    );
}

criterion_group!(benches, bench_relational);
criterion_main!(benches);
