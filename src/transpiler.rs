use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::iter::FromIterator;

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
    fn with_vars(&self, vars: &HashSet<String>) -> Result<Rho, String> {
        let var_symbols: HashMap<String, Symbol> =
            vars.iter().map(|var| (var.clone(), Symbol::Var)).collect();
        self.with(&var_symbols, true)
    }

    fn with_funcs(&self, funcs: &HashSet<String>) -> Result<Rho, String> {
        let func_symbols: HashMap<String, Symbol> = funcs
            .iter()
            .map(|var| (var.clone(), Symbol::Func))
            .collect();
        self.with(&func_symbols, false)
    }

    fn with(
        &self,
        symbols: &HashMap<String, Symbol>,
        allow_overwrite: bool,
    ) -> Result<Rho, String> {
        if !allow_overwrite {
            let self_symbol_set: HashSet<_> = HashSet::from_iter(self.symbols.keys());
            let other_symbol_set: HashSet<_> = HashSet::from_iter(symbols.keys());
            if !self_symbol_set.is_disjoint(&other_symbol_set) {
                return Err(format!(
                    "conflict symbol(s): [{}]",
                    other_symbol_set
                        .into_iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }

        Ok(Rho {
            symbols: self
                .symbols
                .clone()
                .into_iter()
                .chain(symbols.clone())
                .collect(),
            ctors: self.ctors.clone(),
        })
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

    fn list_funcs(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Func)
            .map(|x| x.0.clone())
    }
    fn list_vars(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Var)
            .map(|x| x.0.clone())
    }
    fn list_consts(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Const)
            .map(|x| x.0.clone())
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct CoqProgram {
    pub stmts: Vec<CoqStmt>,
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
                "Definition {}: tm :=\n{}.\n",
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
        ctor: String,
        then: Box<CoqExpr>,
        els: Box<CoqExpr>,
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
                expr,
                ctor,
                then,
                els,
            } => {
                write!(
                    f,
                    "(mat {} \"{}\" {} {})",
                    expr.to_string(),
                    ctor,
                    then.to_string(),
                    els.to_string()
                )
            }
            Abs { var, expr } => {
                write!(
                    f,
                    "(abs \"{}\"\n{}\n)",
                    var,
                    indent(expr.to_string().as_str())
                )
            }
            Rec(expr) => {
                write!(f, "(rec {})", expr.to_string().as_str())
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
        .unwrap_or(String::new())
}

pub fn transpile(input_program: Program) -> Result<CoqProgram, String> {
    Ok(CoqProgram {
        stmts: input_program
            .stmts
            .iter()
            .try_fold::<_, _, Result<_, String>>(
                (
                    Vec::<CoqStmt>::new(),
                    extract_base_rho(&input_program.stmts)?,
                ),
                |(coq_stmts, rho), stmt| {
                    Ok(match stmt {
                        Stmt::NamedFunc { name, expr } => (
                            [
                                coq_stmts.as_slice(),
                                &[Definition {
                                    name: name.clone(),
                                    expr: box transpile_expr(*expr.clone(), &rho)?,
                                }],
                            ]
                            .concat(),
                            rho.with_funcs(&HashSet::from_iter(vec![name.clone()]))?,
                        ),
                        Stmt::RecFunc { name, expr } => (
                            [
                                coq_stmts.as_slice(),
                                &[Definition {
                                    name: name.clone(),
                                    expr: box Rec(box Abs {
                                        var: name.clone(),
                                        expr: box transpile_expr(
                                            *expr.clone(),
                                            &rho.with_vars(&HashSet::from_iter(
                                                vec![name.clone()],
                                            ))?,
                                        )?,
                                    }),
                                }],
                            ]
                            .concat(),
                            rho.with_funcs(&HashSet::from_iter(vec![name.clone()]))?,
                        ),
                        _ => (coq_stmts, rho),
                    })
                },
            )?
            .0,
    })
}

fn transpile_expr(expr: Expr, rho: &Rho) -> Result<CoqExpr, String> {
    Ok(match expr {
        Expr::App(exprs) => App(exprs
            .into_iter()
            .map(|x| Ok(box transpile_expr(*x, rho)?))
            .collect::<Result<Vec<_>, String>>()?),
        Expr::Mat { expr, branches } => transpile_match(expr, branches, rho)?,
        Expr::MatIf {
            expr: pat,
            success,
            fail,
        } => {
            if let Err(e) = ensure_ctors(vec![("true", 0), ("false", 0)], rho) {
                return Err(format!("If statement is not available when there's no bool ctors.\nConsider adding:\n{}", e));
            };
            transpile_expr(
                Expr::Mat {
                    expr: pat,
                    branches: vec![
                        box MatchBranch {
                            pat: Pat::Constructor {
                                ctor: String::from("true"),
                                args: vec![],
                            },
                            expr: success,
                        },
                        box MatchBranch {
                            pat: Pat::Constructor {
                                ctor: String::from("false"),
                                args: vec![],
                            },
                            expr: fail,
                        },
                    ],
                },
                rho,
            )?
        }
        Expr::Abs { var, expr } => Abs {
            var: var.clone(),
            expr: box transpile_expr(
                *expr,
                &rho.with_vars(&HashSet::from_iter(vec![var.clone()]))?,
            )?,
        },
        Expr::Ident(s) => {
            match rho.find_symbol(&s).ok_or(format!(
                "Missing symbol: \"{}\".\nAvailable symbols in scope: {:#?}",
                s, rho.symbols
            ))? {
                Symbol::Const => Const(s),
                Symbol::Var => Var(s),
                Symbol::Func => CoqObj(s),
            }
        }
        Expr::StringLiteral(string_literal) => {
            if let Err(e) = ensure_ctors(vec![("Ascii", 8)], rho) {
                return Err(format!("String literal is not available when there's no Ascii ctors.\nConsider adding:\n{}", e));
            }
            if let Err(e) = ensure_ctors(vec![("String", 1), ("EmptyString", 0)], rho) {
                return Err(format!("String literal is not available when there's no String or EmptyString ctors.\nConsider adding:\n{}", e));
            }
            transpile_string_literal(&string_literal)?
        }
    })
}

fn transpile_string_literal(string_literal: &str) -> Result<CoqExpr, String> {
    let coq_chars: Vec<CoqExpr> = string_literal
        .chars()
        .map(|char| {
            let mut b = [0; 2];
            char.encode_utf8(&mut b);
            if b[1] != 0 {
                Err(format!("{} is not a valid ascii string.", string_literal))
            } else {
                let mut byte = b[0];
                let mut bits: VecDeque<bool> = VecDeque::new();
                byte /= 2;
                for _ in 0..8 {
                    bits.push_front(byte % 2 == 0);
                    byte /= 2;
                }
                let mut ascii_expr: VecDeque<Box<CoqExpr>> = bits
                    .iter()
                    .map(|b| {
                        box if *b {
                            Const(String::from("true"))
                        } else {
                            Const(String::from("false"))
                        }
                    })
                    .collect();
                ascii_expr.push_front(box Const(String::from("Ascii")));
                Ok(App(Vec::<Box<CoqExpr>>::from(ascii_expr)))
            }
        })
        .collect::<Result<Vec<CoqExpr>, String>>()?;
    Ok(coq_chars
        .into_iter()
        .fold(Const(String::from("EmptyString")), |prec, expr| {
            App(vec![
                box App(vec![box Const(String::from("String")), box expr]),
                box prec,
            ])
        }))
}

fn transpile_match(
    expr: Box<Expr>,
    mut branches: Vec<Box<MatchBranch>>,
    rho: &Rho,
) -> Result<CoqExpr, String> {
    let (is_exhaustive, matched_ctor_group, current_ctors) = branches
        .iter()
        .try_rfold::<_, _, Result<_, String>>(
            HashSet::<CtorDef>::new(),
            |matched_ctors, branch| {
                let box MatchBranch { pat, expr: _ } = branch;
                match pat {
                    Pat::Constructor { ctor: ident, args } => {
                        let ctor = rho.find_ctor(&ident).ok_or(format!(
                            "No matched const.\nExpected: one of [{}]\nGot: \"{}\"",
                            rho.list_consts()
                                .map(|x| format!("\"{}\"", x))
                                .collect::<Vec<_>>()
                                .join(", "),
                            ident
                        ))?;
                        if matched_ctors.contains(&ctor) {
                            if args.len() > 0 {
                                Err(format!(
                                    "Duplicate match branch: ({} {}).\nMatched ctor: {}",
                                    ident,
                                    args.join(" "),
                                    ctor
                                ))
                            } else {
                                Err(format!(
                                    "Duplicate match branch: {}.\nMatched ctor: {}",
                                    ident, ctor
                                ))
                            }
                        } else { Ok(()) }?;
                        rho.find_ctor_group(&matched_ctors.union(&hashset! {ctor.clone()}).cloned().collect())
                            .ok_or(format!(
                                "Invalid set of consts.\nExpected: a subset of one of {{\n{}\n}}\nGot: [{}]",
                                indent(&rho.ctors.iter().map(|group| group
                                    .iter()
                                    .map(|ctor| ctor.to_string())
                                    .collect::<Vec<_>>()
                                    .join(", "))
                                    .map(|x| format!("[{}]", x))
                                    .collect::<Vec<_>>()
                                    .join(",\n")),
                                matched_ctors
                                    .iter()
                                    .map(|x| x.to_string())
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ))?;
                        Ok(matched_ctors.union(&hashset! {ctor}).cloned().collect())
                    }
                    Pat::Ignore => Ok(matched_ctors)
                }
            },
        )
        .and_then(|x| {
            let matched_ctor_group = rho.find_ctor_group(&x).ok_or(String::from("unexpected error"))?;
            if matched_ctor_group.len() > x.len() {
                Ok((false, matched_ctor_group, x))
            } else {
                Ok((true, matched_ctor_group, x))
            }
        })?;

    let coq_expr = transpile_expr(*expr, rho)?;
    let last_branch = branches.last().ok_or("Empty match.")?;
    let branches_len = branches.len();
    if let Pat::Constructor { ctor: _, args } = last_branch.pat.clone() {
        if args.len() > 0 {
            for (i, branch) in branches[..branches_len - 1].iter().enumerate() {
                if let Pat::Constructor { ctor: _, args } = branch.pat.clone() {
                    if args.len() == 0 {
                        branches.swap(i, branches_len - 1);
                        break;
                    }
                }
            }
        }
    };
    let last_branch = branches.last().ok_or("Empty match.")?;
    let is_last_branch_wild = if let Pat::Ignore = last_branch.pat {
        true
    } else {
        false
    };

    let (wild_branch, truncate_branch) = if is_last_branch_wild {
        Ok((transpile_expr(*last_branch.expr.clone(), rho)?, true))
    } else if is_exhaustive {
        if let Pat::Constructor { ctor: _, args } = last_branch.pat.clone() {
            if args.len() == 0 {
                Ok((
                    transpile_expr(
                        *last_branch.expr.clone(),
                        &rho.with_vars(&HashSet::from_iter(args.clone()))?,
                    )?,
                    true,
                ))
            } else {
                Ok((Const(String::from("UNREACHABLE")), false))
            }
        } else {
            Err(String::from("unexpected error."))
        }
    } else {
        Err(format!(
            "Match must be exhaustive. Missing ctors: {}",
            matched_ctor_group
                .difference(&current_ctors)
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }?;

    if truncate_branch {
        branches.truncate(branches.len() - 1);
    };

    branches
        .into_iter()
        .try_rfold(wild_branch, |els_branch, branch| {
            let MatchBranch { pat, expr } = *branch;
            match pat {
                Pat::Constructor { ctor: ident, args } => {
                    let then_abs = args.iter().rfold(
                        transpile_expr(*expr, &rho.with_vars(&HashSet::from_iter(args.clone()))?)?,
                        |inner, arg| Abs {
                            var: arg.clone(),
                            expr: box inner,
                        },
                    );
                    Ok(Mat {
                        expr: box coq_expr.clone(),
                        ctor: ident,
                        then: box then_abs,
                        els: box els_branch,
                    })
                }
                Pat::Ignore => unreachable!(),
            }
        })
}

fn extract_base_rho(stmts: &Vec<Stmt>) -> Result<Rho, String> {
    let (const_groups, symbols) = stmts.iter().try_fold::<_, _, Result<_, String>>(
        (
            Vec::<HashSet<CtorDef>>::new(),
            HashMap::<String, Symbol>::new(),
        ),
        |(const_groups, symbols), stmt| match stmt {
            Stmt::ConstDef(consts) => {
                let (group, new_symbols) = consts.iter().try_fold(
                    (HashSet::<CtorDef>::new(), HashMap::<String, Symbol>::new()),
                    |(group, new_symbols), ctor| {
                        if symbols.contains_key(&ctor.ident)
                            || new_symbols.contains_key(&ctor.ident)
                        {
                            Err(format!("Duplicate const declaration: {}", ctor))
                        } else {
                            Ok((
                                group.union(&hashset! {ctor.clone()}).cloned().collect(),
                                new_symbols
                                    .into_iter()
                                    .chain(hashmap! {ctor.ident.clone()=>Symbol::Const})
                                    .collect(),
                            ))
                        }
                    },
                )?;
                Ok((
                    [const_groups.as_slice(), &[group]].concat(),
                    symbols.into_iter().chain(new_symbols).collect(),
                ))
            }
            _ => Ok((const_groups, symbols)),
        },
    )?;

    Ok(Rho {
        symbols,
        ctors: const_groups,
    })
}

fn ensure_ctors(ctors: Vec<(&str, usize)>, rho: &Rho) -> Result<(), String> {
    let ctor_defs: Vec<CtorDef> = ctors
        .into_iter()
        .map(|(name, argc)| CtorDef {
            ident: name.to_string(),
            argc,
        })
        .collect();
    if !(ctor_defs.iter().fold(true, |b, ctor_def| {
        b && rho.find_ctor(&ctor_def.ident) == Some(ctor_def.clone())
    })) {
        Err(format!(
            "const: {}",
            ctor_defs
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", "),
        ))
    } else {
        Ok(())
    }
}
