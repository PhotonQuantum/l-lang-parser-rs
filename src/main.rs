#![feature(iterator_fold_self)]
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate maplit;

use std::fs::File;
use std::io::Read;

use crate::parser::parse;
use crate::transpiler::transpile;

mod parser;
mod transpiler;

fn main() {
    let mut file = File::open("run.l").unwrap();
    let mut buffer = String::new();
    file.read_to_string(&mut buffer).unwrap();
    println!(
        "{}",
        match parse(&buffer) {
            Err(err) => format!("{}", err),
            Ok(ast) => {
                match transpile(ast){
                    Err(err) => err.to_string(),
                    Ok(transpiled_code) => format!("{}", transpiled_code)
                }
            }
        }
    )
}
