use crate::terminal::Stylus;
use crate::{constants::*, utils::*};
use anyhow::Error;
use clap::{ArgAction, Parser, Subcommand, ValueEnum};
use razor_chase::{
    chase::{
        chase_step,
        r#impl::relational::{RelEvaluator, RelPreProcessor},
        scheduler::Dispatch,
        strategy::{Bootstrap, FailFast, Fair},
        Bounder, Depth, DepthMode, DomainSize, Model, PreProcessor, Scheduler, Unbounded,
    },
    trace::{subscriber::JsonLogger, DEFAULT_JSON_LOG_FILE, EXTEND},
};
use razor_fol::{syntax::Formula, transform::Geometrization};
use std::{fs, path::PathBuf};

/// A bound on the models constructed by the chase.
#[derive(Clone, Debug)]
enum BoundCommand {
    /// Bound models by their domain size; models beyond the bound are reported incomplete.
    Domain { size: usize },
    /// Bound the Skolem depth of elements. With `reuse` (the default) a term beyond the bound
    /// denotes its deepest argument, so models stay complete; with `pure` the element is
    /// created and the model is reported incomplete.
    Depth { depth: u32, mode: DepthMode },
}

impl std::str::FromStr for BoundCommand {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_lowercase();
        if let Some(size) = s.strip_prefix("domain=") {
            size.parse::<usize>()
                .map(|size| BoundCommand::Domain { size })
                .map_err(|_| format!("invalid bound size '{}'", size))
        } else if let Some(rest) = s.strip_prefix("depth=") {
            let (depth, mode) = match rest.split_once(':') {
                Some((d, "pure")) => (d, DepthMode::Pure),
                Some((d, "reuse")) | Some((d, "")) => (d, DepthMode::Reuse),
                Some((_, m)) => return Err(format!("invalid depth mode '{}'", m)),
                None => (rest, DepthMode::Reuse),
            };
            depth
                .parse::<u32>()
                .map(|depth| BoundCommand::Depth { depth, mode })
                .map_err(|_| format!("invalid depth '{}'", depth))
        } else {
            Err(format!(
                "invalid bound '{}' (expected domain=N or depth=N[:pure|reuse])",
                s
            ))
        }
    }
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum SchedulerOption {
    /// When branching, process new models first.
    Lifo,
    /// When branching, process new models last.
    Fifo,
}

/// How the conversion to geometric form removes an existential whose scope is not positive.
#[derive(Clone, Copy, Debug, ValueEnum)]
enum GeometrizeOption {
    /// Replace it by a Skolem term over the variables in scope.
    Skolemize,
    /// Name its scope by a fresh predicate and define the predicate. Can run forever on a
    /// theory whose removed scope is unconditional, such as `forall x. exists y. ((P(x) -> Q(y))
    /// & (R(x) -> S(y)))` (core fixture thy50), which claims a new element for every element.
    Define,
    /// Skolemize where the Skolem term occurs only in heads, and define elsewhere. The default,
    /// as it terminates wherever Skolemizing does.
    Hybrid,
}

impl GeometrizeOption {
    fn policy(self) -> Geometrization {
        match self {
            GeometrizeOption::Skolemize => Geometrization::Skolemize,
            GeometrizeOption::Define => Geometrization::Define,
            GeometrizeOption::Hybrid => Geometrization::Hybrid,
        }
    }
}

#[derive(Subcommand)]
enum ProcessCommand {
    /// Find models for the input theory
    Solve {
        /// Path to the input theory file
        #[arg(short = 'i', long = "input")]
        input: Option<PathBuf>,
        /// Number of models to return
        #[arg(long = "count")]
        count: Option<i32>,
        /// Bound the search: `domain=N` or `depth=N[:pure|reuse]`
        #[arg(short = 'b', long = "bound", value_name = "bound")]
        bound: Option<BoundCommand>,
        /// Show incomplete models
        #[arg(long = "show-incomplete", default_value_t = true, action = ArgAction::Set)]
        show_incomplete: bool,
        #[arg(short = 's', long = "scheduler", value_enum, default_value_t = SchedulerOption::Fifo)]
        scheduler: SchedulerOption,
        /// Remove an existential whose scope is not positive by Skolemizing, by definition, or by
        /// Skolemizing where its term occurs only in heads and defining elsewhere
        #[arg(long = "geometrize", value_enum, default_value_t = GeometrizeOption::Hybrid)]
        geometrize: GeometrizeOption,
    },
}

impl ProcessCommand {
    fn run(self, stylus: &Stylus) -> Result<(), Error> {
        match self {
            ProcessCommand::Solve {
                input,
                count,
                bound,
                show_incomplete,
                scheduler,
                geometrize,
            } => {
                let theory = if let Some(input) = input {
                    read_theory_from_file(input.to_str().unwrap_or("."))?
                } else {
                    read_theory_from_stdin()?
                };

                stylus.set(STYLE_INFO);
                println!("Finding models for theory:");

                stylus.set(STYLE_THEORY);
                theory.formulae().iter().for_each(|f| println!("{}", f));

                println!();
                println!();

                let signature = theory.signature()?;
                let (sequents, init_model) =
                    RelPreProcessor::new(geometrize.policy()).pre_process(&theory);

                let bound: Box<dyn Bounder> = match bound {
                    None => Box::new(Unbounded),
                    Some(BoundCommand::Domain { size }) => Box::new(DomainSize(size)),
                    Some(BoundCommand::Depth { depth, mode }) => {
                        Box::new(Depth { max: depth, mode })
                    }
                };
                let strategy: Bootstrap<_, FailFast<_, Fair<_>>> = sequents.iter().collect();
                let mut complete_count = 0;
                let mut incomplete_count = 0;

                let mut scheduler = match scheduler {
                    SchedulerOption::Fifo => Dispatch::new_fifo(),
                    SchedulerOption::Lifo => Dispatch::new_lifo(),
                };

                info!(
                    event = EXTEND,
                    model_id = &init_model.get_id(),
                    model = ?init_model,
                );
                scheduler.add(init_model, strategy);
                while !scheduler.empty() {
                    if count.is_some() && complete_count >= count.unwrap() {
                        break;
                    }
                    chase_step(
                        &mut scheduler,
                        &RelEvaluator,
                        bound.as_ref(),
                        |m| {
                            print_model(
                                m.finalize(),
                                &sequents,
                                &signature,
                                stylus,
                                &mut complete_count,
                            )
                        },
                        |m| {
                            if show_incomplete {
                                print_model(
                                    m.finalize(),
                                    &sequents,
                                    &signature,
                                    stylus,
                                    &mut incomplete_count,
                                );
                            }
                        },
                    )
                }

                println!();

                stylus.set(STYLE_INFO);
                println!(
                    "{} complete and {} incomplete models were found.",
                    complete_count, incomplete_count
                );
                println!();
                Ok(())
            }
        }
    }
}

/// A tool for exploring finite models of first-order theories
#[derive(Parser)]
#[command(name = "Rusty Razor")]
pub(super) struct Command {
    #[command(subcommand)]
    command: ProcessCommand,
    /// Disable colored output.
    #[arg(long = "no-color")]
    no_color: bool,
    /// Path to the log file.
    #[arg(short = 'l', long = "log")]
    log: Option<PathBuf>,
}

impl Command {
    pub fn run(self) -> Result<(), Error> {
        let process = self.command;
        let stylus = stylus(!self.no_color);

        let log = self
            .log
            .map(|l| l.to_str().unwrap_or(DEFAULT_JSON_LOG_FILE).to_owned());

        if !self.no_color {
            stylus.set(STYLE_LOGO);
            println!("{}", ASCII_ART);
        }

        let run = || process.run(&stylus);

        if let Some(log) = log {
            let log = fs::File::create(log).expect("cannot create the log file");
            let logger = JsonLogger::new(log);
            tracing::subscriber::with_default(logger, run)
        } else {
            run()
        }
    }
}
