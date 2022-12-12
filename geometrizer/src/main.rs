mod utils;

use anyhow::{anyhow, Error};
use razor_fol::{
    syntax::Fof,
    transform::{gnf_from_cnf, gnf_from_dnf, ToCnf, ToDnf, ToGnf},
};
use utils::*;

fn main() -> Result<(), Error> {
    let input = read_theory_from_file("formula.input")?;
    let formula = input.first().ok_or(anyhow!("missing formula"))?;
    println!("input:\n{}", formula);

    println!("--------------------------------");
    println!("from DNF:");

    let dnf = formula.dnf();
    let theory = gnf_from_dnf(dnf)
        .into_iter()
        .map(Fof::from)
        .collect::<Vec<_>>();
    theory.iter().for_each(|f| println!("{}", f));

    println!("--------------------------------");
    println!("from CNF:");

    let cnf = formula.cnf();
    let theory = gnf_from_cnf(cnf)
        .into_iter()
        .map(Fof::from)
        .collect::<Vec<_>>();
    theory.iter().for_each(|f| println!("{}", f));

    println!("--------------------------------");
    println!("After Skolemization:");
    let theory = formula.gnf();
    theory.iter().for_each(|f| println!("{}", f));
    Ok(())
}
