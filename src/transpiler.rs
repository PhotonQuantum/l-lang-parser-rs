use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;

use crate::parser::*;
use crate::transpiler::CoqStmt::Definition;

use self::CoqExpr::*;

#[derive(PartialEq, Debug, Clone)]
pub struct CoqProgram {
    stmts: Vec<CoqStmt>
}

impl Display for CoqProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let output = self.stmts.iter().map(|x|x.to_string()).fold_first(|x, y|format!("{}\n{}", x, y)).unwrap();
        write!(f, "{}", output)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum CoqStmt {
    Definition { name: String, expr: Box<CoqExpr> }
}

impl Display for CoqStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CoqStmt::Definition { name, expr } => {
                write!(f, "Definition {}: tm :=\n{}.", name, **expr)
            }
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum CoqExpr {
    App(Vec<Box<CoqExpr>>),
    Mat { pat: Box<CoqExpr>, branches: Vec<Box<CoqMatchBranch>> },
    Abs { var: String, expr: Box<CoqExpr> },
    Const(String),
    Var(String),
}

impl Display for CoqExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CoqExpr::App(exprs) => {
                let expr_strs: Vec<String> = exprs.iter().map(|e| e.to_string()).collect();
                let output = expr_strs.into_iter().fold_first(|x, y| format!("(app {} {})", x, y)).unwrap();
                write!(f, "{}", output)
            }
            CoqExpr::Mat { pat, branches } => {
                let pat_str = pat.to_string();
                let branch_strs: Vec<String> = branches.iter().map(|e| e.to_string()).collect();
                let branch_output = branch_strs.into_iter().fold_first(|x, y| format!("{};\n{}", x, y)).unwrap();
                write!(f, "(mat {} [\n{}\n])", pat_str, indent(branch_output.as_str()))
            }
            CoqExpr::Abs { var, expr } => {
                let expr_str = expr.to_string();
                write!(f, "(abs \"{}\"\n{}\n)", var, indent(expr_str.as_str()))
            }
            CoqExpr::Const(s) => {
                write!(f, "(const \"{}\")", s)
            }
            CoqExpr::Var(s) => {
                write!(f, "(var \"{}\")", s)
            }
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CoqPat {
    pub ctor: String,
    pub args: Vec<String>,
}

impl Display for CoqPat {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let arg_strs: Vec<String> = self.args.iter().map(|e| e.to_string()).collect();
        if arg_strs.is_empty() {
            write!(f, "\"{}\", []", self.ctor)
        } else {
            let arg_output = arg_strs.into_iter().fold_first(|x, y| format!("\"{}\"; \"{}\"", x, y)).unwrap();
            write!(f, "\"{}\", [{}]", self.ctor, arg_output)
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CoqMatchBranch {
    pub pat: CoqPat,
    pub expr: Box<CoqExpr>,
}

impl Display for CoqMatchBranch {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}, \n{})", self.pat, indent(self.expr.to_string().as_str()))
    }
}

fn indent(input_str: &str) -> String {
    input_str.lines().into_iter()
        .map(|x| format!("  {}", x))
        .fold_first(|x, y| format!("{}\n{}", x, y))
        .unwrap()
}

pub fn transpile(input_program: Program) -> CoqProgram {
    let statements = input_program.stmts;
    let const_groups = extract_const_groups(&statements);

    let mut coq_stmts: Vec<CoqStmt> = vec![];
    statements.iter().for_each(|stmt| {
        match stmt {
            Stmt::NamedFunc { name, expr } => {
                coq_stmts.push(Definition { name: name.to_string(), expr: Box::new(transpile_expr(*expr.clone(), &const_groups)) })
            }
            Stmt::ConstDef(_) => ()
        }
    });
    CoqProgram { stmts: coq_stmts }
}

fn transpile_expr(expr: Expr, const_groups: &Vec<HashSet<String>>) -> CoqExpr {
    match expr {
        Expr::App(exprs) => {
            let coq_exprs: Vec<Box<CoqExpr>> = exprs.into_iter()
                .map(|x| Box::new(transpile_expr(*x, const_groups)))
                .collect();
            App(coq_exprs)
        }
        Expr::Mat { pat, branches } => {
            let coq_pat = transpile_expr(*pat, &const_groups);
            let coq_branches = transpile_match_branches(branches, const_groups);
            Mat { pat: Box::new(coq_pat), branches: coq_branches }
        }
        Expr::Abs { var, expr } => {
            let coq_expr = transpile_expr(*expr, const_groups);
            Abs { var, expr: Box::new(coq_expr) }
        }
        Expr::Ident(s) => {
            let mut idents:HashSet<String> = HashSet::new();
            idents.insert(s.clone());
            if idents_in_const_groups(&idents, const_groups).is_some() {
                Const(s)
            } else {
                Var(s)
            }
        }
    }
}

fn transpile_match_branches(branches: Vec<Box<MatchBranch>>, const_groups: &Vec<HashSet<String>>) -> Vec<Box<CoqMatchBranch>> {
    let mut matched_ctors: HashSet<String> = HashSet::new();
    let mut coq_branches: Vec<Box<CoqMatchBranch>> = vec![];
    for branch in branches {
        let pat = branch.pat;
        let expr = branch.expr;
        match pat {
            Pat::Constructor { ctor, args } => {
                if matched_ctors.contains(&ctor) {
                    panic!("duplicate match branch")
                }
                matched_ctors.insert(ctor.clone());

                coq_branches.push(Box::new(
                    CoqMatchBranch {
                        pat: CoqPat { ctor, args },
                        expr: Box::new(transpile_expr(*expr, const_groups))
                    }
                ));
            }
            Pat::Ignore => {
                let matched_const_group = idents_in_const_groups(&matched_ctors, &const_groups)
                    .expect("unable to match a set of consts");
                let mut current_matched_ctors: HashSet<String> = HashSet::new();
                {
                    let remaining_ctors: HashSet<_> = matched_const_group.difference(&matched_ctors).collect();
                    if remaining_ctors.is_empty() {
                        panic!("nothing to match.")
                    }

                    for ctor in remaining_ctors {
                        current_matched_ctors.insert(ctor.clone());
                        coq_branches.push(Box::new(
                            CoqMatchBranch { pat: CoqPat { ctor: ctor.clone(), args: vec![] }, expr: Box::new(transpile_expr(*expr.clone(), const_groups)) }
                        ))
                    }
                }
                matched_ctors = HashSet::from(matched_ctors.union(&current_matched_ctors).cloned().collect());
            }
        }
    }
    coq_branches
}

fn idents_in_const_groups(idents: &HashSet<String>, const_groups: &Vec<HashSet<String>>) -> Option<HashSet<String>> {
    const_groups.into_iter()
        .filter(|group|{
            group.is_superset(idents)
        }).next().cloned()
}

fn extract_const_groups(stmts: &Vec<Stmt>) -> Vec<HashSet<String>> {
    let mut const_groups: Vec<HashSet<String>> = vec![];
    let mut all_consts: HashSet<String> = HashSet::new();
    stmts.iter().for_each(|stmt| {
        match stmt {
            Stmt::NamedFunc { .. } => (),
            Stmt::ConstDef(consts) => {
                let mut group: HashSet<String> = HashSet::new();
                consts.iter().for_each(|c| {
                    if all_consts.contains(c) {
                        panic!("duplicate const declaration")
                    }
                    all_consts.insert(c.clone());
                    group.insert(c.clone());
                });
                const_groups.push(group);
            }
        }
    });

    const_groups
}