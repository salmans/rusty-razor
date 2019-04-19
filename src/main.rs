use structopt::StructOpt;
use std::fs;
use std::io::Read;
use rusty_razor::formula::{parser::parse_theory, syntax::Theory};
use rusty_razor::chase::{r#impl::reference::{Sequent, Model, Evaluator},
                         selector::{Fair, Bootstrap},
                         strategy::FIFO,
                         bounder::DomainSize,
                         Observation,
                         solve};
use term::color::WHITE;

#[derive(StructOpt)]
enum BoundCommand {
    #[structopt(name = "bound-domain", about = "Bound models by their domain size.")]
    Domain {
        #[structopt(help = "Maximum domain size of models.")]
        size: usize,
    },
}

#[derive(StructOpt)]
enum ProcessCommand {
    #[structopt(name = "solve", about = "Find models for the input theory")]
    Solve {
        #[structopt(short = "i", long = "input", parse(from_os_str), help = "Path to the input theory file")]
        input: std::path::PathBuf,
        #[structopt(long = "count", help = "Number of models to return")]
        count: Option<i32>,
        #[structopt(subcommand, name = "bound")]
        bound: Option<BoundCommand>,
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

fn main() {
    let args = Command::from_args();
    let command = args.command;
    let no_color = args.no_color;

    let mut terminal = term::stdout().unwrap();

    if !no_color {
        terminal.fg(136).unwrap();
    }
    println!("\n\
    ________________________________\n\
    ┬─┐┬ ┬┌─┐┌┬┐┬ ┬  ╦═╗╔═╗╔═╗╔═╗╦═╗\n\
    ├┬┘│ │└─┐ │ └┬┘  ╠╦╝╠═╣╔═╝║ ║╠╦╝\n\
    ┴└─└─┘└─┘ ┴  ┴   ╩╚═╩ ╩╚═╝╚═╝╩╚═\n\
    -----------╦-------╦------------");

    if !no_color {
        terminal.fg(WHITE).unwrap();
    }
    println!("           ╟-------╢            ");
    println!("           ╟-------╢            ");
    println!("           ╟-------╢            \n");
    terminal.reset().unwrap();

    match command {
        ProcessCommand::Solve { input, count, bound } => {
            if let Some(input) = input.to_str() {
                let theory = read_theory_from_file(input);
                process_solve(&theory, bound, count,!no_color);
            }
        }
    }
}

fn process_solve(theory: &Theory, bound: Option<BoundCommand>, count: Option<i32>, color: bool) {
    use rusty_razor::chase::SelectorTrait;
    use rusty_razor::chase::StrategyTrait;

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
    let mut strategy = FIFO::new();

    let bounder = if let Some(bound) = bound {
        match bound {
            BoundCommand::Domain { size } => Some(DomainSize::new(size)),
        }
    } else {
        None
    };

    strategy.add(Model::new(), selector);
    let mut found = 0;

    while !strategy.empty() {
        if count.is_some() && found >= count.unwrap() {
            break;
        }
        solve(&mut strategy, &evaluator, bounder.as_ref(), &mut |m| { print_model(m, color, &mut found) })
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

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = fs::File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    let parsed = parse_theory(contents.as_str());
    if parsed.is_err() {
        panic!(parsed.err().unwrap())
    } else {
        parsed.ok().unwrap()
    }
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