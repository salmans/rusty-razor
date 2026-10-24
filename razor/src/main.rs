mod command;
mod constants;
mod terminal;
mod utils;

#[macro_use]
extern crate tracing;

use anyhow::Error;
use command::Command;

fn main() -> Result<(), Error> {
    use clap::Parser;
    Command::parse().run()
}
