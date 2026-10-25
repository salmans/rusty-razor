use crate::{
    constants::*,
    terminal::{Style, Stylus},
};
use anyhow::Error;
use itertools::Itertools;
use razor_chase::chase::{
    r#impl::{
        basic::BasicWitnessTerm,
        relational::{Function, RelModel, RelSequent},
    },
    Model, Observation, Origin, Rel, Witness, E,
};
use razor_fol::{
    syntax::{Sig, Theory, FOF},
    transform::GNF,
};
use std::{
    collections::{BTreeMap, HashMap},
    fs,
    io::{stdin, Read},
};

pub(crate) fn stylus(color: bool) -> Stylus {
    let mut stylus = Stylus::new();
    if color {
        stylus.insert_style(
            STYLE_LOGO,
            Style::new().foreground(59).attribute(term::Attr::Dim),
        );
        stylus.insert_style(
            STYLE_INFO,
            Style::new().foreground(59).attribute(term::Attr::Bold),
        );
        stylus.insert_style(STYLE_THEORY, Style::new().foreground(252));
        stylus.insert_style(
            STYLE_MODEL_DOMAIN,
            Style::new().foreground(252).attribute(term::Attr::Bold),
        );
        stylus.insert_style(STYLE_MODEL_FACTS, Style::new().foreground(252));
    }

    stylus
}

pub(crate) fn read_theory_from_file(filename: &str) -> Result<Theory<FOF>, Error> {
    let mut f = fs::File::open(filename)
        .map_err(|e| Error::new(e).context("failed to find the input file"))?;

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .map_err(|e| Error::new(e).context("failed to read the input file"))?;

    contents
        .parse()
        .map_err(|e| Error::new(e).context("failed to parse the input theory"))
}

pub(crate) fn read_theory_from_stdin() -> Result<Theory<FOF>, Error> {
    let mut buf: Vec<u8> = Vec::new();
    stdin().read_to_end(&mut buf)?;
    let s = String::from_utf8(buf)?;
    let theory = s.parse()?;
    Ok(theory)
}

/// Prints `model` over `signature`, the theory's own: its domain, its facts over the theory's
/// predicates, functions and constants, and then, one line per element, where the chase
/// introduced every element that a symbol outside the signature names, a witness read through
/// the one of `sequents` that introduced it.
pub(crate) fn print_model(
    model: RelModel,
    sequents: &[RelSequent],
    signature: &Sig,
    stylus: &Stylus,
    count: &mut i32,
) {
    *count += 1;

    stylus.set(STYLE_INFO);
    println!("{}.\n", count);
    println!("Domain:");

    {
        let domain = model.domain().iter().map(|e| e.to_string()).collect_vec();
        stylus.set(STYLE_MODEL_DOMAIN);
        print!("{}", domain.join(", "));
        println!("\n");
    }

    let entries = Entry::table(&model, sequents);
    {
        let relations = model.facts().into_iter().filter_map(|f| match f {
            Observation::Fact { relation, terms } if signature.declares_predicate(&relation) => {
                Some(format!("{}({})", relation, terms.iter().join(", ")))
            }
            _ => None,
        });
        let applications = entries.iter().filter_map(|(entry, e)| match entry {
            Entry::Term(term) if signature.declares_term(term) => Some(format!("{} = {}", term, e)),
            _ => None,
        });
        let facts = relations.chain(applications).sorted().collect_vec();

        stylus.set(STYLE_INFO);
        println!("Facts:");
        stylus.set(STYLE_MODEL_FACTS);
        print!("{}", facts.join("\n"));
    }

    let provenance = Provenance::of(&entries, signature);
    if !provenance.is_empty() {
        stylus.set(STYLE_INFO);
        println!("\n\nProvenance:");
        stylus.set(STYLE_MODEL_FACTS);
        print!("{}", provenance.lines().join("\n"));
    }

    stylus.set(STYLE_INFO);
    println!("\n\n- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -");
}

/// An entry of a model's table of applications, read as the name it gives its element.
enum Entry<'a> {
    /// An application of a function or constant of the sequents: one of the theory's, or one
    /// that the conversion to geometric form introduced.
    Term(BasicWitnessTerm),
    /// The element the chase created for the existential of `origin` in a head of `sequent`,
    /// under the assignment of `args` to the universals the existential depends on.
    Fresh {
        sequent: &'a GNF,
        origin: &'a Origin,
        args: &'a [E],
    },
}

impl<'a> Entry<'a> {
    /// Every entry of `model`'s table of applications, as the name it gives its canonical
    /// element.
    fn table(model: &'a RelModel, sequents: &'a [RelSequent]) -> Vec<(Self, E)> {
        let origins: HashMap<Witness, (&GNF, &Origin)> = sequents
            .iter()
            .flat_map(|sequent| {
                sequent
                    .origins()
                    .iter()
                    .map(move |origin| (origin.witness, (sequent.gnf(), origin)))
            })
            .collect();
        model
            .applications()
            .map(|(function, args, e)| {
                let entry = match function {
                    Function::Witness(witness) => {
                        let (sequent, origin) = origins[witness];
                        Entry::Fresh {
                            sequent,
                            origin,
                            args,
                        }
                    }
                    Function::Symbol(_) => Entry::Term(function.term(args)),
                };
                (entry, e)
            })
            .collect()
    }
}

/// Where the chase introduced the elements of a model that no symbol of the theory names alone:
/// one cause per element, a fresh existential before a Skolem term.
struct Provenance(BTreeMap<E, String>);

impl Provenance {
    fn of(entries: &[(Entry, E)], signature: &Sig) -> Self {
        let mut causes = BTreeMap::new();
        for (entry, e) in entries {
            if let Entry::Fresh {
                sequent,
                origin,
                args,
            } = entry
            {
                let with = origin
                    .args
                    .iter()
                    .zip(args.iter())
                    .map(|(v, e)| format!("{} = {}", v, e))
                    .join(", ");
                let with = if with.is_empty() {
                    with
                } else {
                    format!(" with {}", with)
                };
                causes
                    .entry(*e)
                    .or_insert(format!("∃{} of «{}»{}", origin.existential, sequent, with));
            }
        }
        for (entry, e) in entries {
            if let Entry::Term(term) = entry {
                if !signature.declares_term(term) {
                    causes.entry(*e).or_insert(format!("Skolem term {}", term));
                }
            }
        }
        Self(causes)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn lines(&self) -> Vec<String> {
        self.0
            .iter()
            .map(|(e, cause)| format!("{} ⟵ {}", e, cause))
            .collect()
    }
}

/// Whether a signature declares the symbols of a model's names.
trait Declares {
    fn declares_predicate(&self, relation: &Rel) -> bool;
    fn declares_term(&self, term: &BasicWitnessTerm) -> bool;
}

impl Declares for Sig {
    fn declares_predicate(&self, relation: &Rel) -> bool {
        self.predicates().contains_key(relation.name())
    }

    fn declares_term(&self, term: &BasicWitnessTerm) -> bool {
        match term {
            BasicWitnessTerm::Elem(_) | BasicWitnessTerm::Witness { .. } => false,
            BasicWitnessTerm::Const(c) => self.constants().contains(c),
            BasicWitnessTerm::App { function, .. } => {
                self.functions().contains_key(function.name())
            }
        }
    }
}
