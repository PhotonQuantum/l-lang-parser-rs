#[macro_use]
extern crate pest_derive;

use std::fs::File;
use std::io::Read;
use crate::parser::parse;

mod parser;

fn main() {
    let mut file = File::open("run.l").unwrap();
    let mut buffer = String::new();
    file.read_to_string(&mut buffer).unwrap();
    let ast = parse(&buffer);
    println!("{:#?}", ast.unwrap());
}
