use crate::{
    constants::*,
    terminal::{Style, Stylus},
};
use anyhow::Error;
use itertools::Itertools;
use razor_chase::chase::{r#impl::relational::RelModel, Model, Observation};
use razor_fol::syntax::{Theory, FOF};
use std::{
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

pub(crate) fn print_model(model: RelModel, stylus: &Stylus, count: &mut i32) {
    *count += 1;

    stylus.set(STYLE_INFO);
    println!("{}.\n", count);
    println!("Domain:");

    {
        let domain = model.domain().iter().map(|e| e.to_string()).collect_vec();
        // print_list(color, MODEL_DOMAIN_COLOR, &domain);
        stylus.set(STYLE_MODEL_DOMAIN);
        print!("{}", domain.join(", "));
        println!("\n");
    }

    {
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
            .sorted();

        stylus.set(STYLE_INFO);
        println!("Facts:");
        stylus.set(STYLE_MODEL_FACTS);
        print!("{}", facts.join("\n"));
    }

    stylus.set(STYLE_INFO);
    println!("\n\n- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -");
}
