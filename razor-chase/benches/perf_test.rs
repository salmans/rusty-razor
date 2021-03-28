use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use itertools::Itertools;
use razor_chase::chase::{
    bounder::DomainSize,
    chase_all,
    r#impl::*,
    scheduler::FIFO,
    strategy::{Bootstrap, Fair},
    PreProcessor, Scheduler, Strategy,
};
use razor_fol::syntax::Theory;
use std::{fs, io::Read};

macro_rules! read_theory {
    ($file_name: expr) => {{
        let mut f = fs::File::open($file_name).expect("file not found");
        let mut contents = String::new();
        f.read_to_string(&mut contents)
            .expect("something went wrong reading the file");

        contents.parse::<Theory>().unwrap()
    }};
}

macro_rules! run_unbounded {
    (
        $name: literal,
        pre_processor = $prep: expr,
        evaluator = $eval: path,
        sequent = $seq: path,
        model = $model: path,
        $crit: ident
    ) => {{
        fn solve(theory: &Theory) -> Vec<$model> {
            let (sequents, init_model) = $prep.pre_process(theory);
            let evaluator = $eval;
            let selector: Bootstrap<$seq, Fair<$seq>> = Bootstrap::new(sequents.iter());
            let mut strategy = FIFO::new();
            let bounder: Option<&DomainSize> = None;
            strategy.add(init_model, selector);
            chase_all(&mut strategy, &evaluator, bounder)
        }

        fn run_bench(b: &mut Bencher) {
            let theories = &fs::read_dir("../theories/core")
                .unwrap()
                .map(|item| read_theory!(item.unwrap().path().display().to_string()).gnf())
                .collect_vec();

            b.iter(|| {
                for theory in theories {
                    solve(&theory);
                }
            })
        }
        $crit.bench_function(stringify!($name), run_bench);
    }};
}

fn bench_batch(c: &mut Criterion) {
    run_unbounded!(
        "batch",
        pre_processor = collapse::ColPreProcessor,
        evaluator = batch::BatchEvaluator,
        sequent = collapse::ColSequent,
        model = collapse::ColModel,
        c
    );
}

fn bench_relational(c: &mut Criterion) {
    run_unbounded!(
        "relational",
        pre_processor = relational::RelPreProcessor::new(false),
        evaluator = relational::RelEvaluator,
        sequent = relational::RelSequent,
        model = relational::RelModel,
        c
    );
}

fn bench_relational_memoized(c: &mut Criterion) {
    run_unbounded!(
        "relational_memoized",
        pre_processor = relational::RelPreProcessor::new(true),
        evaluator = relational::RelEvaluator,
        sequent = relational::RelSequent,
        model = relational::RelModel,
        c
    );
}

criterion_group!(
    benches,
    bench_batch,
    bench_relational,
    bench_relational_memoized
);
criterion_main!(benches);
