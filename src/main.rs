#![feature(iterator_fold_self)]
#[macro_use]
extern crate pest_derive;
#[macro_use]
extern crate maplit;

use std::fs::File;
use std::io::Read;

use crate::parser::parse;
use crate::transpiler::transpile;
use std::process::exit;
use std::env::args;

mod parser;
mod transpiler;

fn main() {
    let mut file = File::open(args().nth(1).unwrap()).unwrap();
    let mut buffer = String::new();
    file.read_to_string(&mut buffer).unwrap();
    match parse(&buffer) {
        Err(err) => {
            eprintln!("{}", err);
            exit(1)
        }
        Ok(ast) => match transpile(ast) {
            Err(err) => {
                eprintln!("{}", err);
                exit(1)
            }
            Ok(transpiled_code) => println!("{}", transpiled_code),
        },
    }
}
