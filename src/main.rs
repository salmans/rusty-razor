use structopt::StructOpt;
use rusty_razor::formula::{parser::parse_theory, syntax::Theory};
use rusty_razor::chase::{r#impl::batch::{Sequent, Model, Evaluator},
                         ModelTrait, SelectorTrait, StrategyTrait,
                         selector::{Fair, Bootstrap},
                         strategy::Dispatch,
                         bounder::DomainSize,
                         Observation,
                         solve};
use rusty_razor::trace::{subscriber::JsonLogger, DEFAULT_JSON_LOG_FILE, EXTEND};
use term::{color::{WHITE, BRIGHT_RED, GREEN, BRIGHT_YELLOW, BRIGHT_BLUE}};
use std::{io::Read, fs, path::PathBuf, process::exit};
use failure::Error;
use itertools::Itertools;

#[macro_use]
extern crate tracing;

const INFO_COLOR: term::color::Color = 27;
const LOGO_TOP_COLOR: term::color::Color = 136;
const LOGO_BOTTOM_COLOR: term::color::Color = WHITE;
const ERROR_COLOR: term::color::Color = BRIGHT_RED;
const MODEL_DOMAIN_COLOR: term::color::Color = GREEN;
const MODEL_ELEMENTS_COLOR: term::color::Color = BRIGHT_YELLOW;
const MODEL_FACTS_COLOR: term::color::Color = BRIGHT_BLUE;
const INFO_ATTRIBUTE: term::Attr = term::Attr::Bold;

#[derive(StructOpt)]
enum BoundCommand {
    #[structopt(about = "Bound models by their domain size.")]
    Domain {
        size: usize,
    },
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

impl Default for BoundCommand {
    fn default() -> Self {
        BoundCommand::Domain { size: 10 }
    }
}

#[derive(StructOpt)]
enum StrategyOption {
    #[structopt(about = "When branching, process new models first.")]
    LIFO,
    #[structopt(about = "When branching, process new models last.")]
    FIFO,
}

impl std::str::FromStr for StrategyOption {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.to_lowercase() == "lifo" {
            Ok(StrategyOption::LIFO)
        } else if s.to_lowercase() == "fifo" {
            Ok(StrategyOption::FIFO)
        } else {
            Err("invalid strategy")
        }
    }
}

impl Default for StrategyOption {
    fn default() -> Self {
        StrategyOption::FIFO
    }
}


#[derive(StructOpt)]
enum ProcessCommand {
    #[structopt(name = "solve", about = "Find models for the input theory")]
    Solve {
        #[structopt(short = "i", long = "input", parse(from_os_str), help = "Path to the input theory file")]
        input: std::path::PathBuf,
        #[structopt(long = "count", help = "Number of models to return")]
        count: Option<i32>,
        #[structopt(short = "b", long = "bound", name = "bound")]
        bound: Option<BoundCommand>,
        #[structopt(short = "s", long = "strategy", default_value = "fifo")]
        strategy: StrategyOption,
    }
}

impl Default for ProcessCommand {
    fn default() -> Self {
        ProcessCommand::Solve {
            input: PathBuf::from("theory.raz"),
            count: None,
            bound: None,
            strategy: StrategyOption::FIFO,
        }
    }
}

#[derive(StructOpt)]
#[structopt(name = "Rusty Razor", about = "A tool for exploring finite models of first-order theories")]
#[structopt(raw(setting = "structopt::clap::AppSettings::ColoredHelp"))]
struct Command {
    #[structopt(subcommand, name = "command")]
    command: ProcessCommand,
    #[structopt(long = "no-color", help = "Makes it dim.")]
    no_color: bool,
    #[structopt(short = "l", long = "log", parse(from_os_str), help = "Path to the log file.")]
    log: Option<std::path::PathBuf>,
}

impl Default for Command {
    fn default() -> Self {
        Command {
            command: ProcessCommand::default(),
            no_color: false,
            log: None,
        }
    }
}

struct Terminal {
    term: Box<term::StdoutTerminal>,
    color: Option<term::color::Color>,
    attribute: Option<term::Attr>,
}

impl Terminal {
    fn new() -> Terminal {
        Self {
            term: term::stdout().unwrap(),
            color: None,
            attribute: None,
        }
    }

    fn foreground(&mut self, color: Option<term::color::Color>) -> &mut Self {
        self.color = color;
        self
    }

    fn attribute(&mut self, attribute: Option<term::Attr>) -> &mut Self {
        self.attribute = attribute;
        self
    }

    fn apply(&mut self, closure: impl Fn() -> ()) -> &mut Self {
        if let Some(color) = self.color {
            self.term.fg(color).unwrap();
        }
        if let Some(attribute) = self.attribute {
            self.term.attr(attribute).unwrap();
        }
        closure();
        self
    }

    fn reset(&mut self) {
        if self.color.is_some() || self.attribute.is_some() {
            self.term.reset().unwrap();
        }
    }
}

fn main() {
    let args = Command::from_args();
    let command = args.command;
    let color = !args.no_color;
    let log = args.log.map(|l| l.to_str().unwrap_or(DEFAULT_JSON_LOG_FILE).to_owned());

    let (logo_top_color, logo_bottom_color, error_color) = if color {
        (Some(LOGO_TOP_COLOR), Some(LOGO_BOTTOM_COLOR), Some(ERROR_COLOR))
    } else {
        (None, None, None)
    };

    let mut term = Terminal::new();
    term.foreground(logo_top_color)
        .apply(|| {
            println!("\n\
   ┌════════════════════════════════┐\n\
   │╤═╕╤ ╤╒═╕╒╤╕╤ ╤  ╦═╗╔═╗╔═╗╔═╗╦═╗│\n\
   │├┬┘│ │└─┐ │ └┬┘  ╠╦╝╠═╣╔═╝║ ║╠╦╝│\n\
   │┴└─└─┘└─┘ ┴  ┴   ╩╚═╩ ╩╚═╝╚═╝╩╚═│\n\
   └═══════════╦-------╦════════════┘");
        }).foreground(logo_bottom_color)
        .apply(|| {
            println!("            ╟-------╢             ");
            println!("            ╟-------╢             ");
            println!("            ╟-------╢             \n");
        })
        .reset();

    match command {
        ProcessCommand::Solve { input, count, bound, strategy } => {
            if let Some(input) = input.to_str() {
                let theory = read_theory_from_file(input);

                if theory.is_ok() {
                    process_solve(&theory.unwrap(), bound, strategy, log, count, color)
                } else {
                    let message = format!("Parser error: {}", theory.err().unwrap().to_string());
                    term.foreground(error_color)
                        .apply(|| {
                            println!("{}", message.clone());
                        })
                        .reset();
                    println!();
                    exit(1);
                }
            }
        }
    }
}

fn process_solve(
    theory: &Theory,
    bound: Option<BoundCommand>,
    strategy: StrategyOption,
    log: Option<String>,
    count: Option<i32>,
    color: bool,
) {
    let mut term = Terminal::new();
    let (info_color, info_attribute) = if color {
        (Some(INFO_COLOR), Some(INFO_ATTRIBUTE))
    } else {
        (None, None)
    };

    term.foreground(info_color)
        .attribute(info_attribute)
        .apply(|| {
            println!("Finding models for theory:");
        })
        .reset();

    theory.formulae.iter().for_each(|f| println!("  {}", f));

    println!();
    println!();

    let theory = theory.gnf();
    let sequents: Vec<Sequent> = theory
        .formulae
        .iter()
        .map(|f| f.into()).collect();
    let evaluator = Evaluator {};
    let selector: Bootstrap<Sequent, Fair<Sequent>> = Bootstrap::new(sequents.iter().collect());

    let bounder = if let Some(bound) = bound {
        match bound {
            BoundCommand::Domain { size } => Some(DomainSize::new(size)),
        }
    } else {
        None
    };

    let mut found = 0;

    let mut strategy = match strategy {
        StrategyOption::FIFO => Dispatch::new_fifo(),
        StrategyOption::LIFO => Dispatch::new_lifo(),
    };

    let initial_model = Model::new();
    let run = || {
        info!(
            event = EXTEND,
            model_id = &initial_model.get_id(),
            model = %initial_model,
        );
        strategy.add(initial_model, selector);
        while !strategy.empty() {
            if count.is_some() && found >= count.unwrap() {
                break;
            }
            solve(&mut strategy, &evaluator, bounder.as_ref(), |m| print_model(m, color, &mut found))
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

    term.foreground(info_color)
        .attribute(info_attribute)
        .apply(|| {
            let grammar = if found == 1 { ("", "was") } else { ("s", "were") };
            println!("{} model{} {} found.", found, grammar.0, grammar.1);
        })
        .reset();

    println!();
}


pub fn read_theory_from_file(filename: &str) -> Result<Theory, Error> {
    let mut f = fs::File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    parse_theory(contents.as_str())
}

fn print_model(model: Model, color: bool, count: &mut i32) {
    let (info_color, info_attribute, domain_color, elements_color, facts_color) = if color {
        (
            Some(INFO_COLOR),
            Some(INFO_ATTRIBUTE),
            Some(MODEL_DOMAIN_COLOR),
            Some(MODEL_ELEMENTS_COLOR),
            Some(MODEL_FACTS_COLOR),
        )
    } else {
        (None, None, None, None, None)
    };

    *count += 1;

    let mut term = Terminal::new();
    term.foreground(info_color)
        .attribute(info_attribute)
        .apply(|| {
            print!("Domain: ");
        })
        .reset();
    let domain = model.domain().iter().map(|e| e.get().to_string()).collect();
    print_list(&domain, domain_color);
    println!("\n");

    let elements: Vec<String> = model.domain().iter().sorted().iter().map(|e| {
        let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
        let witnesses = witnesses.into_iter().sorted();
        format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e.get())
    }).collect();

    term.apply(|| print!("Elements: "));
    print_list(&elements, elements_color);
    println!("\n");

    let facts: Vec<String> = model.facts().iter().map(|f| {
        match f {
            Observation::Fact { relation, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                format!("{}({})", relation, ts.join(", "))
            }
            Observation::Identity { left, right } => format!("{} = {}", left, right),
        }
    }).collect();

    term.apply(|| print!("Facts: "));
    print_list(&facts, facts_color);
    println!("\n");

    term.foreground(info_color)
        .attribute(info_attribute)
        .apply(|| {
            println!("\n- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -\n");
        })
        .reset();
}

fn print_list<T: std::fmt::Display>(list: &Vec<T>, color: Option<term::color::Color>) {
    let item_attribute = if color.is_some() { Some(term::Attr::Bold) } else { None };

    Terminal::new()
        .foreground(color)
        .attribute(item_attribute)
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
