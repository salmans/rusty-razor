mod utils;

use anyhow::Error;
use razor_fol::transform::{
    gnf_from_cnf, gnf_from_dnf, GnfFromCnfContext, GnfFromDnfContext, ToCnf, ToDnf, ToGnf,
};
use utils::*;

fn main() -> Result<(), Error> {
    let theory = read_theory_from_file("formula.input")?;
    println!("input:\n{}", theory);

    println!("--------------------------------");
    println!("from DNF:");

    let mut p_counter = 0;
    let mut context = GnfFromDnfContext::new(move || {
        let pred = format!("P#{}", p_counter).into();
        p_counter += 1;
        pred
    });

    theory
        .iter()
        .flat_map(|f| gnf_from_dnf(f.dnf(), &mut context))
        .for_each(|f| println!("{}", f));

    println!("--------------------------------");
    println!("from CNF:");

    let mut p_counter = 0;
    let mut t_counter = 0;
    let mut context = GnfFromCnfContext::new(
        move || {
            let pred = format!("P#{}", p_counter).into();
            p_counter += 1;
            pred
        },
        move || {
            let pred = format!("T#{}", t_counter).into();
            t_counter += 1;
            pred
        },
    );

    theory
        .iter()
        .flat_map(|f| gnf_from_cnf(f.cnf(), &mut context))
        .into_iter()
        .for_each(|f| println!("{}", f));

    println!("--------------------------------");
    println!("After Skolemization:");
    theory
        .iter()
        .flat_map(|f| f.gnf())
        .into_iter()
        .for_each(|f| println!("{}", f));
    Ok(())
}
