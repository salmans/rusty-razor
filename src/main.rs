use structopt::StructOpt;
use std::fs;
use std::io::Read;
use rusty_razor::formula::{parser::parse_theory, syntax::Theory};
use rusty_razor::chase::{r#impl::reference::{Sequent, Model, Evaluator},
                         SelectorTrait, StrategyTrait,
                         selector::{Fair, Bootstrap},
                         strategy::Dispatch,
                         bounder::DomainSize,
                         Observation,
                         solve};
use term::color::{WHITE, BRIGHT_RED};
use std::process::exit;
use failure::Error;
use std::path::PathBuf;

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
#[structopt(name = "Rusty Razor", about = "A tool for exploring finite models of first-order theories.")]
#[structopt(raw(setting = "structopt::clap::AppSettings::ColoredHelp"))]
struct Command {
    #[structopt(subcommand, name = "command")]
    command: ProcessCommand,
    #[structopt(long = "no-color", help = "Make it dim.")]
    no_color: bool,
}

impl Default for Command {
    fn default() -> Self {
        Command {
            command: ProcessCommand::default(),
            no_color: false,
        }
    }
}

fn main() {
    let args = Command::from_args();
    let command = args.command;
    let no_color = args.no_color;

    let mut terminal = term::stdout().unwrap();

    if !no_color {
        terminal.fg(136).unwrap();
    }
    println!("\n\
   ┌════════════════════════════════┐\n\
   │╤═╕╤ ╤╒═╕╒╤╕╤ ╤  ╦═╗╔═╗╔═╗╔═╗╦═╗│\n\
   │├┬┘│ │└─┐ │ └┬┘  ╠╦╝╠═╣╔═╝║ ║╠╦╝│\n\
   │┴└─└─┘└─┘ ┴  ┴   ╩╚═╩ ╩╚═╝╚═╝╩╚═│\n\
   └═══════════╦-------╦════════════┘");

    if !no_color {
        terminal.fg(WHITE).unwrap();
    }
    println!("            ╟-------╢             ");
    println!("            ╟-------╢             ");
    println!("            ╟-------╢             \n");
    terminal.reset().unwrap();

    match command {
        ProcessCommand::Solve { input, count, bound, strategy } => {
            if let Some(input) = input.to_str() {
                let theory = read_theory_from_file(input);

                if theory.is_ok() {
                    process_solve(&theory.unwrap(), bound, strategy, count, !no_color)
                } else {
                    terminal.fg(BRIGHT_RED).unwrap();
                    println!("Parser error: {}", theory.err().unwrap().to_string());
                    terminal.reset().unwrap();
                    println!();
                    exit(1);
                }
            }
        }
    }
}

fn process_solve(theory: &Theory, bound: Option<BoundCommand>, strategy: StrategyOption, count: Option<i32>, color: bool) {
    let mut terminal = term::stdout().unwrap();

    if color {
        terminal.fg(27).unwrap();
    }
    terminal.attr(term::Attr::Bold).unwrap();
    println!("Finding models for theory:");
    terminal.reset().unwrap();

    theory.formulas.iter().for_each(|f| println!("  {}", f));

    println!();
    println!();

    let theory = theory.gnf();
    let sequents: Vec<Sequent> = theory
        .formulas
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

    strategy.add(Model::new(), selector);

    while !strategy.empty() {
        if count.is_some() && found >= count.unwrap() {
            break;
        }
        solve(&mut strategy, &evaluator, bounder.as_ref(), |m| { print_model(m, color, &mut found) })
    }

    println!();
    if color {
        terminal.fg(27).unwrap();
    }
    terminal.attr(term::Attr::Bold).unwrap();
    let grammar = if found == 1 { ("", "was") } else { ("s", "were") };
    println!("{} model{} {} found.", found, grammar.0, grammar.1);
    terminal.reset().unwrap();
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
    *count += 1;
    use rusty_razor::chase::ModelTrait;
    use itertools::Itertools;

    let mut terminal = term::stdout().unwrap();

    if color {
        terminal.fg(27).unwrap();
    }
    terminal.attr(term::Attr::Bold).unwrap();

    print!("Domain: ");
    let domain = model.domain().iter().map(|e| e.get().to_string()).collect();
    let fg_color = if color { None } else { Some(term::color::GREEN) };
    print_list(&domain, fg_color);
    println!("\n");

    let elements: Vec<String> = model.domain().iter().sorted().iter().map(|e| {
        let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
        let witnesses = witnesses.into_iter().sorted();
        format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e.get())
    }).collect();

    print!("Elements: ");
    let fg_color = if color { None } else { Some(term::color::BRIGHT_YELLOW) };
    print_list(&elements, fg_color);
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
    print!("Facts: ");
    let fg_color = if color { None } else { Some(term::color::BRIGHT_BLUE) };
    print_list(&facts, fg_color);
    println!("\n");

    if color {
        terminal.fg(27).unwrap();
    }
    terminal.attr(term::Attr::Bold).unwrap();
    println!("\n- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -\n");

    terminal.reset().unwrap();
}

fn print_list<T: std::fmt::Display>(list: &Vec<T>, color: Option<term::color::Color>) {
    let mut terminal = term::stdout().unwrap();
    let last = list.len() - 1;
    let mut index = 0;
    for x in list {
        if let Some(color) = color {
            terminal.fg(color).unwrap();
        }
        terminal.attr(term::Attr::Bold).unwrap();
        print!("{}", x);
        if index != last {
            terminal.reset().unwrap();
            print!(", ");
            index += 1;
        }
    }
    terminal.reset().unwrap();
}
