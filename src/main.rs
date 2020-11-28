#![feature(iterator_fold_self)]
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate pest_derive;

use std::fs::File;
use std::io::{Read, Write};
use std::io;
use std::path::PathBuf;
use std::process::{Command, exit};
use std::str;

use clap::{App, Arg, SubCommand};
use tempdir::TempDir;
use which::which;

use crate::parser::parse;
use crate::printer::{check_main, generate_coq_code};
use crate::printer::Mode::{Export, Run};
use crate::transpiler::{CoqProgram, transpile};

mod parser;
mod transpiler;
mod printer;

fn main() {
    let matches = App::new("l-lang-parser-rs")
        .version("0.1.0")
        .author("LightQuantum <self@lightquantum.me>")
        .about("A parser for a toy strict untyped λ-calculus language called L-lang.")
        .subcommand(SubCommand::with_name("export")
            .about("Export Coq HIR")
            .arg(Arg::with_name("INPUT")
                .help("L lang file to be parsed")
                .required(true))
            .arg(Arg::with_name("interpreter")
                .long("interp")
                .short("i")
                .help("Include interpreter in generated Coq code."))
        )
        .subcommand(SubCommand::with_name("run")
            .about("Use Coq to interpret HIR.")
            .arg(Arg::with_name("INPUT")
                .help("L lang file to be parsed")
                .required(true))
            .arg(Arg::with_name("with-steps")
                .long("with-steps")
                .short("s")
                .help("Print call steps."))
            .arg(Arg::with_name("recursion-limit")
                .long("recursion-limit")
                .short("r")
                .default_value("100")
                .value_name("LIMIT")
                .takes_value(true)
                .help("Max recursion depth."))
            .arg(Arg::with_name("coqc-binary")
                .short("bin")
                .long("coqc-binary")
                .help("Specify coqc binary path manually")
                .value_name("COQC_BINARY")
                .takes_value(true)
            )
        )
        .get_matches();

    if let Some(matches) = matches.subcommand_matches("run") {
        let mut file = File::open(matches.value_of("INPUT").unwrap()).unwrap_or_else(|_| {
            eprintln!("File not found");
            exit(1)
        });
        let hir = transpile_from_file(&mut file).unwrap_or_else(|e| {
            eprintln!("{}", e);
            exit(1)
        });
        if !check_main(&hir) {
            eprintln!("Missing main function.");
            exit(1)
        };

        let coqc_bin = if let Some(path) = matches.value_of("coqc-binary") {
            PathBuf::from(path)
        } else {
            let path = which("coqc");
            if path.is_err() {
                eprintln!("Unable to locate coqc binary.");
                exit(1)
            }
            path.unwrap()
        };

        let recursion_limit = match matches.value_of("recursion-limit"){
            Some(value) => value.parse::<usize>().unwrap_or_else(|_|{
                eprintln!("Invalid max recursion limit.");
                exit(1)
            }),
            None => 100
        };

        match execute(hir, coqc_bin, matches.is_present("with-steps"), recursion_limit) {
            Ok(output) => {
                println!("{}", output)
            }
            Err(e) => {
                eprintln!("{}", e);
                exit(1)
            }
        }
    } else if let Some(matches) = matches.subcommand_matches("export") {
        let mut file = File::open(matches.value_of("INPUT").unwrap()).unwrap_or_else(|_| {
            eprintln!("File not found");
            exit(1)
        });
        let hir = transpile_from_file(&mut file).unwrap_or_else(|e| {
            eprintln!("{}", e);
            exit(1)
        });
        println!("{}", generate_coq_code(&hir, Export { base: matches.is_present("interpreter") }))
    }
}

fn execute(ast: CoqProgram, coqc_bin: PathBuf, with_steps: bool, recursion_limit: usize) -> io::Result<String> {
    let working_dir = TempDir::new("l_lang")?;
    let file_path = working_dir.path().join("run.v");
    let mut coq_file = File::create(&file_path)?;
    write!(coq_file, "{}", generate_coq_code(&ast, Run { with_steps, recursion_limit }))?;
    coq_file.flush()?;
    Command::new(coqc_bin)
        .arg(file_path)
        .output()
        .and_then(|output| {
            Ok(str::from_utf8(if output.status.success() {
                output.stdout
            } else {
                output.stderr
            }.as_slice()).unwrap().to_string())
        })
}

fn transpile_from_file(file: &mut File) -> Result<CoqProgram, String> {
    let mut buffer = String::new();
    file.read_to_string(&mut buffer).unwrap();
    match parse(&buffer) {
        Err(err) => {
            Err(err.to_string())
        }
        Ok(ast) => match transpile(ast) {
            Err(err) => {
                Err(err)
            }
            Ok(transpiled_code) => {
                Ok(transpiled_code)
            }
        },
    }
}