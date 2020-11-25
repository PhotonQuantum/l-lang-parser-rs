use pest::error::Error;
use pest::Parser;

use self::Expr::*;
use self::Pat::*;
use self::Stmt::*;

#[derive(Parser)]
#[grammar = "l.pest"]
pub struct LParser;

#[derive(PartialEq, Debug, Clone)]
pub struct Program {
    pub stmts: Vec<Stmt>
}

#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub struct CtorDef {
    pub ident: String,
    pub argc: usize,
}

#[derive(PartialEq, Debug, Clone)]
pub enum Stmt {
    NamedFunc { name: String, expr: Box<Expr> },
    RecFunc { name: String, expr: Box<Expr> },
    ConstDef(Vec<CtorDef>),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Expr {
    App(Vec<Box<Expr>>),
    Mat { pat: Box<Expr>, branches: Vec<Box<MatchBranch>> },
    Abs { var: String, expr: Box<Expr> },
    Ident(String),
}

#[derive(PartialEq, Debug, Clone)]
pub enum Pat {
    Constructor { ctor: String, args: Vec<String> },
    Ignore,
}

#[derive(PartialEq, Debug, Clone)]
pub struct MatchBranch {
    pub pat: Pat,
    pub expr: Box<Expr>,
}

pub fn parse(source: &str) -> Result<Program, Error<Rule>> {
    let mut ast = vec![];

    let mut pairs = LParser::parse(Rule::program, source)?;
    let pair = pairs.next().unwrap();
    let mut is_terminated = false;
    match pair.as_rule() {
        Rule::program => {
            let pairs = pair.into_inner();
            for pair in pairs {
                match pair.as_rule() {
                    Rule::statement => {
                        ast.push(parse_stmt(pair.into_inner().next().unwrap()))
                    }
                    Rule::EOI => {
                        is_terminated = true
                    }
                    _ => {
                        panic!("unexpected token when parsing program: {}", pair.as_str())
                    }
                }
            }
        }
        _ => {}
    }

    if !is_terminated {
        panic!("truncated file")
    }
    Ok(Program { stmts: ast })
}

pub fn parse_stmt(pair: pest::iterators::Pair<Rule>) -> Stmt {
    match pair.as_rule() {
        Rule::named_func => {
            let mut pair = pair.into_inner();
            let name = pair.next().unwrap();
            let expr = pair.next().unwrap();
            NamedFunc { name: name.as_str().to_string(), expr: Box::new(parse_expr(expr)) }
        }
        Rule::recursive_func => {
            let mut pair = pair.into_inner();
            let name = pair.next().unwrap();
            let expr = pair.next().unwrap();
            RecFunc { name: name.as_str().to_string(), expr: Box::new(parse_expr(expr)) }
        }
        Rule::const_def => {
            let consts: Vec<CtorDef> = pair.into_inner().map(|x| parse_ctor_def(x)).collect();
            ConstDef(consts)
        }
        _ => {
            panic!("unexpected token when parsing stmt: {}", pair.as_str())
        }
    }
}

pub fn parse_ctor_def(pair: pest::iterators::Pair<Rule>) -> CtorDef {
    let mut pair = pair.into_inner();
    let ident = pair.next().unwrap().as_str().to_string();
    let argc = pair.count();
    CtorDef { ident, argc }
}

pub fn parse_expr(pair: pest::iterators::Pair<Rule>) -> Expr {
    match pair.as_rule() {
        Rule::app => {
            let exprs: Vec<Box<Expr>> = pair.into_inner().map(|x| Box::new(parse_expr(x))).collect();
            App(exprs)
        }
        Rule::mat => {
            let mut pair = pair.into_inner();
            let expr = pair.next().unwrap();
            let branches: Vec<Box<MatchBranch>> = pair.map(|x| Box::new(parse_match_branch(x))).collect();
            return Mat { pat: Box::new(parse_expr(expr)), branches };
        }
        Rule::abs => {
            let mut pair = pair.into_inner();
            let var = pair.next().unwrap();
            let expr = pair.next().unwrap();
            return Abs { var: var.as_str().to_string(), expr: Box::new(parse_expr(expr)) };
        }
        Rule::ident => {
            return Ident(pair.as_str().to_string());
        }
        _ => {
            panic!("unexpected token when parsing expr: {}", pair.as_str())
        }
    }
}

pub fn parse_match_branch(pair: pest::iterators::Pair<Rule>) -> MatchBranch {
    let mut pair = pair.into_inner();
    let pat: Vec<String> = pair.next().unwrap().into_inner().map(|x| x.as_str().to_string()).collect();
    let expr = parse_expr(pair.next().unwrap());

    if pat.len() == 0 {
        panic!("invalid pat")
    } else if pat.len() == 1 && pat[0] == "_" {
        MatchBranch { pat: Ignore, expr: Box::new(expr) }
    } else {
        MatchBranch { pat: Constructor { ctor: pat[0].clone(), args: pat[1..].to_vec() }, expr: Box::new(expr) }
    }
}