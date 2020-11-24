#![feature(iterator_fold_self)]
#[macro_use]
extern crate pest_derive;

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
    let ast = parse(&buffer).unwrap();
    let transpiled_code = transpile(ast);
    println!("{}", transpiled_code);
}
