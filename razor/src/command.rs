use crate::terminal::Stylus;
use crate::{constants::*, utils::*};
use anyhow::Error;
use razor_chase::{
    chase::{
        bounder::DomainSize,
        chase_step,
        r#impl::relational::{RelEvaluator, RelPreProcessor},
        scheduler::Dispatch,
        strategy::{Bootstrap, FailFast, Fair},
        Model, PreProcessor, Scheduler,
    },
    trace::{subscriber::JsonLogger, DEFAULT_JSON_LOG_FILE, EXTEND},
};
use std::fs;
use structopt::StructOpt;

#[derive(StructOpt)]
enum BoundCommand {
    #[structopt(about = "Bound models by their domain size.")]
    Domain { size: usize },
}

impl std::str::FromStr for BoundCommand {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let domain_str: &'static str = "domain=";
        if s.to_lowercase().starts_with(&domain_str) {
            let size_str = &s[domain_str.len()..];
            if let Ok(size) = size_str.parse::<usize>() {
                Ok(BoundCommand::Domain { size })
            } else {
                Err(format!("invalid bound size '{}'", &size_str))
            }
        } else {
            Err(format!("invalid bound '{}'", s))
        }
    }
}

#[derive(StructOpt)]
enum SchedulerOption {
    #[structopt(about = "When branching, process new models first.")]
    LIFO,
    #[structopt(about = "When branching, process new models last.")]
    FIFO,
}

impl std::str::FromStr for SchedulerOption {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if &s.to_lowercase() == "lifo" {
            Ok(SchedulerOption::LIFO)
        } else if &s.to_lowercase() == "fifo" {
            Ok(SchedulerOption::FIFO)
        } else {
            Err("invalid scheduler")
        }
    }
}

#[derive(StructOpt)]
enum ProcessCommand {
    #[structopt(name = "solve", about = "Find models for the input theory")]
    Solve {
        #[structopt(
            short = "i",
            long = "input",
            parse(from_os_str),
            help = "Path to the input theory file"
        )]
        input: Option<std::path::PathBuf>,
        #[structopt(long = "count", help = "Number of models to return")]
        count: Option<i32>,
        #[structopt(
            short = "b",
            long = "bound",
            name = "bound",
            help = "Bound the size of models."
        )]
        bound: Option<BoundCommand>,
        #[structopt(
            long = "show-incomplete",
            help = "Show incomplete models.",
            parse(try_from_str),
            default_value = "true"
        )]
        show_incomplete: bool,
        #[structopt(short = "s", long = "scheduler", default_value = "fifo")]
        scheduler: SchedulerOption,
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

                let pre_processor = RelPreProcessor::new(true);
                let (sequents, init_model) = pre_processor.pre_process(&theory);

                let evaluator = RelEvaluator;
                let strategy: Bootstrap<_, FailFast<_, Fair<_>>> = sequents.iter().collect();
                let bounder = bound.map(|b| match b {
                    BoundCommand::Domain { size } => DomainSize::from(size),
                });
                let mut complete_count = 0;
                let mut incomplete_count = 0;

                let mut scheduler = match scheduler {
                    SchedulerOption::FIFO => Dispatch::new_fifo(),
                    SchedulerOption::LIFO => Dispatch::new_lifo(),
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
                        &evaluator,
                        bounder.as_ref(),
                        |m| print_model(m.finalize(), stylus, &mut complete_count),
                        |m| {
                            if show_incomplete {
                                print_model(m.finalize(), stylus, &mut incomplete_count);
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

#[derive(StructOpt)]
#[structopt(
    name = "Rusty Razor",
    about = "A tool for exploring finite models of first-order theories"
)]
#[structopt(raw(setting = "structopt::clap::AppSettings::ColoredHelp"))]
pub(super) struct Command {
    #[structopt(subcommand, name = "command")]
    command: ProcessCommand,
    #[structopt(long = "no-color", help = "Disable colored output.")]
    no_color: bool,
    #[structopt(
        short = "l",
        long = "log",
        parse(from_os_str),
        help = "Path to the log file."
    )]
    log: Option<std::path::PathBuf>,
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
