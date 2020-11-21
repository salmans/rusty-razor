pub mod utils;

use crate::utils::terminal::{
    Terminal, INFO_ATTRIBUTE, INFO_COLOR, LOGO_TOP_COLOR, MODEL_DOMAIN_COLOR, MODEL_ELEMENTS_COLOR,
    MODEL_FACTS_COLOR,
};
use anyhow::Error;
use itertools::Itertools;
use razor_chase::{
    chase::{
        bounder::DomainSize,
        chase_step,
        r#impl::relational::{Evaluator, Model, PreProcessor, Sequent},
        scheduler::Dispatch,
        strategy::{Bootstrap, Fair},
        ModelTrait, Observation, PreProcessorEx, SchedulerTrait, StrategyTrait,
    },
    trace::{subscriber::JsonLogger, DEFAULT_JSON_LOG_FILE, EXTEND},
};
use razor_fol::syntax::Theory;
use std::io;
use std::{fs, io::Read};
use structopt::StructOpt;

#[macro_use]
extern crate tracing;

const ASCII_ART: &str = r#"
      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓
      ╟▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▌
   ╫▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▌
   ╫▓▓▀▀▓   ▓▓▀▀▓▓▓▓▓▀▀▀▓▓▓▓▓▀▀▓   ▓▓▀▀▓▓▌
   ╫▓▓                                 ▓▓▌
   ╫▓▓▄▄▓   ▓▓▄▄▓▓▓▓▓▄▄▄▓▓▓▓▓▄▄▓   ▓▓▄▄▓▓▌
   ╟▓▓▓▓▓▓▓▓▓▓▓▓ Rusty Razor ▓▓▓▓▓▓▓▓▓▓▓▓▌
      ╫▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▌
      ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓
            "#;

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

#[derive(StructOpt)]
#[structopt(
    name = "Rusty Razor",
    about = "A tool for exploring finite models of first-order theories"
)]
#[structopt(raw(setting = "structopt::clap::AppSettings::ColoredHelp"))]
struct Command {
    #[structopt(subcommand, name = "command")]
    command: ProcessCommand,
    #[structopt(long = "no-color", help = "Makes it dim.")]
    no_color: bool,
    #[structopt(
        short = "l",
        long = "log",
        parse(from_os_str),
        help = "Path to the log file."
    )]
    log: Option<std::path::PathBuf>,
}

fn main() -> Result<(), Error> {
    let args = Command::from_args();

    let command = args.command;
    let color = !args.no_color;
    let log = args
        .log
        .map(|l| l.to_str().unwrap_or(DEFAULT_JSON_LOG_FILE).to_owned());

    if color {
        let mut term = Terminal::new(color);
        term.foreground(LOGO_TOP_COLOR)
            .apply(|| {
                println!("{}", ASCII_ART);
            })
            .reset();
    }

    match command {
        ProcessCommand::Solve {
            input,
            count,
            bound,
            show_incomplete,
            scheduler,
        } => {
            let theory: Theory;
            if let Some(input) = input {
                theory = read_theory_from_file(input.to_str().unwrap_or("."))?
            } else {
                // input from the pipe
                let mut buf: Vec<u8> = Vec::new();
                io::stdin().read_to_end(&mut buf)?;
                let s = String::from_utf8(buf)?;
                theory = s.parse()?;
            }
            process_solve(
                &theory,
                bound,
                show_incomplete,
                scheduler,
                log,
                count,
                color,
            )?;
        }
    }
    Ok(())
}

fn process_solve(
    theory: &Theory,
    bound: Option<BoundCommand>,
    show_incomplete: bool,
    scheduler: SchedulerOption,
    log: Option<String>,
    count: Option<i32>,
    color: bool,
) -> Result<(), Error> {
    let mut term = Terminal::new(color);

    term.foreground(INFO_COLOR)
        .attribute(INFO_ATTRIBUTE)
        .apply(|| {
            println!("Finding models for theory:");
        })
        .reset();

    theory.formulae().iter().for_each(|f| println!("  {}", f));

    println!();
    println!();

    let pre_processor = PreProcessor::new(false);
    let (sequents, init_model) = pre_processor.pre_process(&theory);

    let evaluator = Evaluator;
    let strategy: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter());
    let bounder = bound.map(|b| match b {
        BoundCommand::Domain { size } => DomainSize::from(size),
    });
    let mut complete_count = 0;
    let mut incomplete_count = 0;

    let mut scheduler = match scheduler {
        SchedulerOption::FIFO => Dispatch::new_fifo(),
        SchedulerOption::LIFO => Dispatch::new_lifo(),
    };

    let run = || {
        info!(
            event = EXTEND,
            model_id = &init_model.get_id(),
            model = %init_model,
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
                |m| print_model(m.finalize(), color, &mut complete_count),
                |m| {
                    if show_incomplete {
                        print_model(m.finalize(), color, &mut incomplete_count);
                    }
                },
            )
        }
    };

    if let Some(log) = log {
        let log = fs::File::create(log).expect("cannot create the log file");
        let logger = JsonLogger::new(log);
        tracing::subscriber::with_default(logger, run);
    } else {
        run();
    }

    println!();

    term.foreground(INFO_COLOR)
        .attribute(INFO_ATTRIBUTE)
        .apply(|| {
            println!(
                "{} complete and {} incomplete models were found.",
                complete_count, incomplete_count
            );
        })
        .reset();

    println!();
    Ok(())
}

pub fn read_theory_from_file(filename: &str) -> Result<Theory, Error> {
    let mut f = fs::File::open(filename)
        .map_err(|e| Error::new(e).context("failed to find the input file"))?;

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .map_err(|e| Error::new(e).context("failed to read the input file"))?;

    contents
        .parse()
        .map_err(|e| Error::new(e).context("failed to parse the input theory"))
}

fn print_model(model: Model, color: bool, count: &mut i32) {
    *count += 1;

    let mut term = Terminal::new(color);
    term.foreground(INFO_COLOR)
        .attribute(INFO_ATTRIBUTE)
        .apply(|| {
            print!("Domain: ");
        })
        .reset();
    let domain = model.domain().iter().map(|e| e.to_string()).collect_vec();
    print_list(color, MODEL_DOMAIN_COLOR, &domain);
    println!("\n");

    let elements: Vec<String> = model
        .domain()
        .iter()
        .sorted()
        .iter()
        .map(|e| {
            let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
            let witnesses = witnesses.into_iter().sorted();
            format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
        })
        .collect();

    term.apply(|| print!("Elements: "));
    print_list(color, MODEL_ELEMENTS_COLOR, &elements);
    println!("\n");

    let facts: Vec<String> = model
        .facts()
        .iter()
        .map(|f| match f {
            Observation::Fact { relation, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                format!("{}({})", relation, ts.join(", "))
            }
            Observation::Identity { left, right } => format!("{} = {}", left, right),
        })
        .collect();

    term.apply(|| print!("Facts: "));
    print_list(color, MODEL_FACTS_COLOR, &facts);
    println!("\n");

    term.foreground(INFO_COLOR)
        .attribute(INFO_ATTRIBUTE)
        .apply(|| {
            println!("\n- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -\n");
        })
        .reset();
}

fn print_list<T: std::fmt::Display>(color: bool, text_color: term::color::Color, list: &[T]) {
    let mut term = Terminal::new(color);
    term.foreground(text_color)
        .attribute(term::Attr::Bold)
        .apply(|| {
            let last = list.len() - 1;
            let mut index = 0;
            for x in list {
                print!("{}", x);
                if index != last {
                    print!(", ");
                    index += 1;
                }
            }
        })
        .reset();
}
