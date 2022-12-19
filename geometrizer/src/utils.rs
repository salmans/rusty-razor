use anyhow::Error;
use razor_fol::syntax::{Fof, Theory};
use std::{fs, io::Read};

pub(crate) fn read_theory_from_file(filename: &str) -> Result<Theory<Fof>, Error> {
    let mut f = fs::File::open(filename)
        .map_err(|e| Error::new(e).context("failed to find the input file"))?;

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .map_err(|e| Error::new(e).context("failed to read the input file"))?;

    contents
        .parse()
        .map_err(|e| Error::new(e).context("failed to parse the input theory"))
}
