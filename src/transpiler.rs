use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::iter::repeat;

use crate::parser::*;
use crate::transpiler::CoqStmt::Definition;

use self::CoqExpr::*;

#[derive(PartialEq, Debug, Clone)]
struct Consts {
    idents: HashSet<String>,
    ctors: Vec<HashSet<CtorDef>>,
}

impl Consts {
    fn contains(&self, ident: &str) -> bool {
        self.idents.iter()
            .filter(|group| group.as_str() == ident)
            .next().is_some()
    }
    fn find_ctor_group(&self, ctors: &HashSet<CtorDef>) -> Option<HashSet<CtorDef>> {
        self.ctors.iter()
            .filter(|group| group.is_superset(ctors))
            .next().cloned()
    }
    fn find_ctor(&self, ident: &str) -> Option<CtorDef> {
        self.ctors.iter()
            .filter_map(|group| group.into_iter().filter(|ctor| ctor.ident == ident).next())
            .next().cloned()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CoqProgram {
    stmts: Vec<CoqStmt>
}

impl Display for CoqProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let output = self.stmts.iter().map(|x| x.to_string()).fold_first(|x, y| format!("{}\n{}", x, y)).unwrap();
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
                write!(f, "Definition {}: tm :=\n{}.", name, indent(&expr.to_string()))
            }
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum CoqExpr {
    App(Vec<Box<CoqExpr>>),
    Mat { pat: Box<CoqExpr>, branches: Vec<Box<CoqMatchBranch>> },
    Abs { var: String, expr: Box<CoqExpr> },
    Rec(Box<CoqExpr>),
    Const(String),
    Var(String),
}

impl Display for CoqExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            App(exprs) => {
                let expr_strs: Vec<String> = exprs.iter().map(|e| e.to_string()).collect();
                let output = expr_strs.into_iter().fold_first(|x, y| format!("(app {} {})", x, y)).unwrap();
                write!(f, "{}", output)
            }
            Mat { pat, branches } => {
                let pat_str = pat.to_string();
                let branch_strs: Vec<String> = branches.iter().map(|e| e.to_string()).collect();
                let branch_output = branch_strs.into_iter().fold_first(|x, y| format!("{};\n{}", x, y)).unwrap();
                write!(f, "(mat {} [\n{}\n])", pat_str, indent(branch_output.as_str()))
            }
            Abs { var, expr } => {
                let expr_str = expr.to_string();
                write!(f, "(abs \"{}\"\n{}\n)", var, indent(expr_str.as_str()))
            }
            Rec(expr) => {
                let expr_str = expr.to_string();
                write!(f, "(rec {})", expr_str.as_str())
            }
            Const(s) => {
                write!(f, "(const \"{}\")", s)
            }
            Var(s) => {
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
        let arg_output = arg_strs.into_iter().map(|x| format!("\"{}\"", x)).fold_first(|x, y| format!("{}; {}", x, y)).unwrap_or(String::from(""));
        write!(f, "\"{}\", [{}]", self.ctor, arg_output)
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
    let consts = extract_consts(&statements);

    let mut coq_stmts: Vec<CoqStmt> = vec![];
    statements.iter().for_each(|stmt| {
        match stmt {
            Stmt::NamedFunc { name, expr } =>
                coq_stmts.push(
                    Definition {
                        name: name.to_string(),
                        expr: Box::new(transpile_expr(*expr.clone(), &consts)),
                    }),
            Stmt::RecFunc { name, expr } =>
                coq_stmts.push(
                    Definition {
                        name: name.to_string(),
                        expr: Box::new(Rec(Box::new(transpile_expr(*expr.clone(), &consts)))),
                    }),
            Stmt::ConstDef(_) => ()
        }
    });
    CoqProgram { stmts: coq_stmts }
}

fn transpile_expr(expr: Expr, consts: &Consts) -> CoqExpr {
    match expr {
        Expr::App(exprs) => {
            let coq_exprs: Vec<Box<CoqExpr>> = exprs.into_iter()
                .map(|x| Box::new(transpile_expr(*x, consts)))
                .collect();
            App(coq_exprs)
        }
        Expr::Mat { pat, branches } => {
            let coq_pat = transpile_expr(*pat, &consts);
            let coq_branches = transpile_match_branches(branches, consts);
            Mat { pat: Box::new(coq_pat), branches: coq_branches }
        }
        Expr::Abs { var, expr } => {
            let coq_expr = transpile_expr(*expr, consts);
            Abs { var, expr: Box::new(coq_expr) }
        }
        Expr::Ident(s) => {
            if consts.contains(&s) {
                Const(s)
            } else {
                Var(s)
            }
        }
    }
}

fn transpile_match_branches(branches: Vec<Box<MatchBranch>>, consts: &Consts) -> Vec<Box<CoqMatchBranch>> {
    let mut matched_ctors: HashSet<CtorDef> = HashSet::new();
    let mut coq_branches: Vec<Box<CoqMatchBranch>> = vec![];
    for branch in branches {
        let pat = branch.pat;
        let expr = branch.expr;
        match pat {
            Pat::Constructor { ctor: ident, args } => {
                let ctor = consts.find_ctor(&ident).expect("no matched ctor");
                if matched_ctors.contains(&ctor) {
                    panic!("duplicate match branch")
                }
                matched_ctors.insert(ctor.clone());

                coq_branches.push(Box::new(
                    CoqMatchBranch {
                        pat: CoqPat { ctor: ctor.ident, args },
                        expr: Box::new(transpile_expr(*expr, consts)),
                    }
                ));
            }
            Pat::Ignore => {
                let matched_consts = consts.find_ctor_group(&matched_ctors)
                    .expect("unable to match a set of consts");
                let mut current_matched_ctors: HashSet<CtorDef> = HashSet::new();
                {
                    let remaining_ctors: HashSet<_> = matched_consts.difference(&matched_ctors).collect();
                    if remaining_ctors.is_empty() {
                        panic!("nothing to match.")
                    }

                    for ctor in remaining_ctors {
                        current_matched_ctors.insert(ctor.clone());
                        coq_branches.push(Box::new(
                            CoqMatchBranch { pat: CoqPat { ctor: ctor.ident.clone(), args: repeat(String::from("_")).take(ctor.argc).collect() }, expr: Box::new(transpile_expr(*expr.clone(), consts)) }
                        ))
                    }
                }
                matched_ctors = HashSet::from(matched_ctors.union(&current_matched_ctors).cloned().collect());
            }
        }
    }
    coq_branches
}


fn extract_consts(stmts: &Vec<Stmt>) -> Consts {
    let mut const_groups: Vec<HashSet<CtorDef>> = vec![];
    let mut all_consts: HashSet<String> = HashSet::new();
    stmts.iter().for_each(|stmt| {
        match stmt {
            Stmt::ConstDef(consts) => {
                let mut group: HashSet<CtorDef> = HashSet::new();
                consts.iter().for_each(|c| {
                    if all_consts.contains(&c.ident) {
                        panic!("duplicate const declaration")
                    }
                    all_consts.insert(c.ident.clone());
                    group.insert(c.clone());
                });
                const_groups.push(group);
            },
            _ => ()
        }
    });

    Consts { idents: all_consts, ctors: const_groups }
}