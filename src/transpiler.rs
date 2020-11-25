use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::hash::Hash;
use std::iter::{repeat, FromIterator};

use crate::parser::*;

use self::CoqExpr::*;
use self::CoqStmt::*;

#[derive(PartialEq, Debug, Copy, Clone)]
enum Symbol {
    Const,
    Var,
    Func,
}

#[derive(PartialEq, Debug, Clone)]
struct Rho {
    symbols: HashMap<String, Symbol>,
    ctors: Vec<HashSet<CtorDef>>,
}

impl Rho {
    fn with_vars(&self, vars: &HashSet<String>) -> Rho {
        let var_symbols: HashMap<String, Symbol> =
            vars.iter().map(|var| (var.clone(), Symbol::Var)).collect();
        self.with(&var_symbols)
    }

    fn with_funcs(&self, funcs: &HashSet<String>) -> Rho {
        let func_symbols: HashMap<String, Symbol> = funcs
            .iter()
            .map(|var| (var.clone(), Symbol::Func))
            .collect();
        self.with(&func_symbols)
    }

    fn with(&self, symbols: &HashMap<String, Symbol>) -> Rho {
        let self_symbol_set: HashSet<_> = HashSet::from_iter(self.symbols.keys());
        let other_symbol_set: HashSet<_> = HashSet::from_iter(symbols.keys());
        if !self_symbol_set.is_disjoint(&other_symbol_set) {
            panic!("conflict symbols")
        }

        let mut self_symbols = self.symbols.clone();
        self_symbols.extend(symbols.clone());
        Rho {
            symbols: self_symbols,
            ctors: self.ctors.clone(),
        }
    }

    fn find_symbol(&self, ident: &str) -> Option<Symbol> {
        self.symbols.get(ident).copied()
    }

    fn find_ctor_group(&self, ctors: &HashSet<CtorDef>) -> Option<HashSet<CtorDef>> {
        self.ctors
            .iter()
            .filter(|group| group.is_superset(ctors))
            .next()
            .cloned()
    }

    fn find_ctor(&self, ident: &str) -> Option<CtorDef> {
        self.ctors
            .iter()
            .filter_map(|group| group.into_iter().filter(|ctor| ctor.ident == ident).next())
            .next()
            .cloned()
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CoqProgram {
    stmts: Vec<CoqStmt>,
}

impl Display for CoqProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let output = self
            .stmts
            .iter()
            .map(|x| x.to_string())
            .fold_first(|x, y| format!("{}\n{}", x, y))
            .unwrap();
        write!(f, "{}", output)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum CoqStmt {
    Definition { name: String, expr: Box<CoqExpr> },
}

impl Display for CoqStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            CoqStmt::Definition { name, expr } => write!(
                f,
                "Definition {}: tm :=\n{}.",
                name,
                indent(&expr.to_string())
            ),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub enum CoqExpr {
    App(Vec<Box<CoqExpr>>),
    Mat {
        expr: Box<CoqExpr>,
        branches: Vec<Box<CoqMatchBranch>>,
    },
    Abs {
        var: String,
        expr: Box<CoqExpr>,
    },
    Rec(Box<CoqExpr>),
    Const(String),
    Var(String),
    CoqObj(String),
}

impl Display for CoqExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            App(exprs) => {
                let expr_strs: Vec<String> = exprs.iter().map(|e| e.to_string()).collect();
                let output = expr_strs
                    .into_iter()
                    .fold_first(|x, y| format!("(app {} {})", x, y))
                    .unwrap();
                write!(f, "{}", output)
            }
            Mat {
                expr: pat,
                branches,
            } => {
                let pat_str = pat.to_string();
                let branch_strs: Vec<String> = branches.iter().map(|e| e.to_string()).collect();
                let branch_output = branch_strs
                    .into_iter()
                    .fold_first(|x, y| format!("{};\n{}", x, y))
                    .unwrap();
                write!(
                    f,
                    "(mat {} [\n{}\n])",
                    pat_str,
                    indent(branch_output.as_str())
                )
            }
            Abs { var, expr } => {
                let expr_str = expr.to_string();
                write!(f, "(abs \"{}\"\n{}\n)", var, indent(expr_str.as_str()))
            }
            Rec(expr) => {
                let expr_str = expr.to_string();
                write!(f, "(rec {})", expr_str.as_str())
            }
            Const(s) => write!(f, "(const \"{}\")", s),
            Var(s) => write!(f, "(var \"{}\")", s),
            CoqObj(s) => write!(f, "{}", s),
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
        let arg_output = arg_strs
            .into_iter()
            .map(|x| format!("\"{}\"", x))
            .fold_first(|x, y| format!("{}; {}", x, y))
            .unwrap_or(String::from(""));
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
        write!(
            f,
            "({}, \n{})",
            self.pat,
            indent(self.expr.to_string().as_str())
        )
    }
}

fn indent(input_str: &str) -> String {
    input_str
        .lines()
        .into_iter()
        .map(|x| format!("  {}", x))
        .fold_first(|x, y| format!("{}\n{}", x, y))
        .unwrap()
}

pub fn transpile(input_program: Program) -> CoqProgram {
    CoqProgram {
        stmts: input_program
            .stmts
            .iter()
            .fold(
                (
                    Vec::<CoqStmt>::new(),
                    extract_base_rho(&input_program.stmts),
                ),
                |(coq_stmts, rho), stmt| match stmt {
                    Stmt::NamedFunc { name, expr } => (
                        [
                            coq_stmts.as_slice(),
                            &[Definition {
                                name: name.clone(),
                                expr: Box::new(transpile_expr(*expr.clone(), &rho)),
                            }],
                        ]
                        .concat(),
                        rho.with_funcs(&HashSet::from_iter(vec![name.clone()])),
                    ),
                    Stmt::RecFunc { name, expr } => (
                        [
                            coq_stmts.as_slice(),
                            &[Definition {
                                name: name.clone(),
                                expr: Box::new(Rec(Box::new(transpile_expr(*expr.clone(), &rho)))),
                            }],
                        ]
                        .concat(),
                        rho.with_funcs(&HashSet::from_iter(vec![name.clone()])),
                    ),
                    _ => (coq_stmts, rho),
                },
            )
            .0,
    }
}

fn transpile_expr(expr: Expr, rho: &Rho) -> CoqExpr {
    match expr {
        Expr::App(exprs) => App(exprs
            .into_iter()
            .map(|x| Box::new(transpile_expr(*x, rho)))
            .collect()),
        Expr::Mat {
            expr: pat,
            branches,
        } => Mat {
            expr: Box::new(transpile_expr(*pat, &rho)),
            branches: transpile_match_branches(branches, rho),
        },
        Expr::Abs { var, expr } => Abs {
            var: var.clone(),
            expr: Box::new(transpile_expr(
                *expr,
                &rho.with_vars(&HashSet::from_iter(vec![var.clone()])),
            )),
        },
        Expr::Ident(s) => {
            match rho
                .find_symbol(&s)
                .expect(format!("missing symbol: {}", s).as_str())
            {
                Symbol::Const => Const(s),
                Symbol::Var => Var(s),
                Symbol::Func => CoqObj(s),
            }
        }
    }
}

fn transpile_match_branches(
    branches: Vec<Box<MatchBranch>>,
    rho: &Rho,
) -> Vec<Box<CoqMatchBranch>> {
    let mut matched_ctors: HashSet<CtorDef> = HashSet::new();
    let mut coq_branches: Vec<Box<CoqMatchBranch>> = vec![];
    for branch in branches {
        let pat = branch.pat;
        let expr = branch.expr;
        match pat {
            Pat::Constructor { ctor: ident, args } => {
                let ctor = rho.find_ctor(&ident).expect("no matched ctor");
                if matched_ctors.contains(&ctor) {
                    panic!("duplicate match branch")
                }
                matched_ctors.insert(ctor.clone());

                coq_branches.push(Box::new(CoqMatchBranch {
                    pat: CoqPat {
                        ctor: ctor.ident,
                        args: args.clone(),
                    },
                    expr: Box::new(transpile_expr(
                        *expr,
                        &rho.with_vars(&HashSet::from_iter(args)),
                    )),
                }));
            }
            Pat::Ignore => {
                let matched_consts = rho
                    .find_ctor_group(&matched_ctors)
                    .expect("unable to match a set of consts");
                let mut current_matched_ctors: HashSet<CtorDef> = HashSet::new();
                {
                    let remaining_ctors: HashSet<_> =
                        matched_consts.difference(&matched_ctors).collect();
                    if remaining_ctors.is_empty() {
                        panic!("nothing to match.")
                    }

                    for ctor in remaining_ctors {
                        current_matched_ctors.insert(ctor.clone());
                        coq_branches.push(Box::new(CoqMatchBranch {
                            pat: CoqPat {
                                ctor: ctor.ident.clone(),
                                args: repeat(String::from("_")).take(ctor.argc).collect(),
                            },
                            expr: Box::new(transpile_expr(*expr.clone(), rho)),
                        }))
                    }
                }
                matched_ctors = HashSet::from(
                    matched_ctors
                        .union(&current_matched_ctors)
                        .cloned()
                        .collect(),
                );
            }
        }
    }
    coq_branches
}

fn extract_base_rho(stmts: &Vec<Stmt>) -> Rho {
    let mut const_groups: Vec<HashSet<CtorDef>> = vec![];
    let mut symbols: HashMap<String, Symbol> = HashMap::new();
    stmts.iter().for_each(|stmt| match stmt {
        Stmt::ConstDef(consts) => {
            let mut group: HashSet<CtorDef> = HashSet::new();
            consts.iter().for_each(|c| {
                if symbols.contains_key(&c.ident) {
                    panic!("duplicate const declaration")
                }
                symbols.insert(c.ident.clone(), Symbol::Const);
                group.insert(c.clone());
            });
            const_groups.push(group);
        }
        _ => (),
    });

    Rho {
        symbols,
        ctors: const_groups,
    }
}
