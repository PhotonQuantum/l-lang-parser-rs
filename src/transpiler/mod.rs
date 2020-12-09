use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::FromIterator;

use crate::parser::*;

pub use self::ast::CoqExpr::*;
pub use self::ast::CoqStmt::*;
pub use self::ast::*;
use self::symbol::{Rho, Symbol};
use self::utils::indent;

pub(crate) mod ast;
mod symbol;
mod utils;

#[derive(Copy, Clone)]
pub struct Config {
    pub optimize: bool,
    pub strict: bool,
}

pub fn transpile(input_program: Program, config: Config) -> Result<CoqProgram, String> {
    Ok(CoqProgram {
        stmts: input_program
            .stmts
            .iter()
            .try_fold::<_, _, Result<_, String>>(
                (
                    Vec::<CoqStmt>::new(),
                    extract_base_rho(&input_program.stmts, config)?,
                ),
                |(coq_stmts, rho), stmt| {
                    Ok(match stmt {
                        Stmt::NamedFunc { name, expr } => (
                            [
                                coq_stmts.as_slice(),
                                &[Definition {
                                    name: name.clone(),
                                    expr: box transpile_expr(*expr.clone(), &rho, config)?,
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
                                            config,
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

fn transpile_expr(expr: Expr, rho: &Rho, config: Config) -> Result<CoqExpr, String> {
    Ok(match expr {
        Expr::App(exprs) => App(exprs
            .into_iter()
            .map(|x| Ok(box transpile_expr(*x, rho, config)?))
            .collect::<Result<Vec<_>, String>>()?),
        Expr::Mat { expr, branches } => transpile_match(expr, branches, rho, config)?,
        Expr::MatIf {
            expr: pat,
            success,
            fail,
        } => {
            if config.strict {
                if let Err(e) = ensure_ctors(vec![("true", 0), ("false", 0)], rho) {
                    return Err(format!(
                        "If statement is not available when there's no bool ctors.\n\
                Consider adding:\n{}",
                        e
                    ));
                };
            }
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
                            pat: Pat::Ignore,
                            expr: fail,
                        },
                    ],
                },
                rho,
                config,
            )?
        }
        Expr::Abs { var, expr } => Abs {
            var: var.clone(),
            expr: box transpile_expr(
                *expr,
                &rho.with_vars(&HashSet::from_iter(vec![var.clone()]))?,
                config,
            )?,
        },
        Expr::Ident(s) => {
            if config.strict {
                match rho.find_symbol(&s).ok_or(format!(
                    "Missing symbol: \"{}\".\nAvailable symbols in scope: {:#?}",
                    s, rho.symbols
                ))? {
                    Symbol::Const => Const(s),
                    Symbol::Var => Var(s),
                    Symbol::Func => CoqObj(s),
                }
            } else {
                match rho.find_symbol(&s).unwrap_or_else(|| {
                    eprintln!("Missing symbol: \"{}\". Assuming it's a const.", s);
                    Symbol::Const
                }) {
                    Symbol::Const => Const(s),
                    Symbol::Var => Var(s),
                    Symbol::Func => CoqObj(s),
                }
            }
        }
        Expr::StringLiteral(string_literal) => {
            if config.strict {
                if let Err(e) = ensure_ctors(vec![("Ascii", 8)], rho) {
                    return Err(format!(
                        "String literal is not available when there's no Ascii ctors.\n\
                        Consider adding:\n{}",
                        e
                    ));
                }
                if let Err(e) = ensure_ctors(vec![("String", 1), ("EmptyString", 0)], rho) {
                    return Err(format!("String literal is not available when there's no String or EmptyString ctors.\n\
                    Consider adding:\n{}", e));
                }
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
                for _ in 0..8 {
                    bits.push_front(!byte % 2 == 0);
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
                    .rev()
                    .collect();
                ascii_expr.push_front(box Const(String::from("Ascii")));
                Ok(App(Vec::<Box<CoqExpr>>::from(ascii_expr)))
            }
        })
        .collect::<Result<Vec<CoqExpr>, String>>()?;
    Ok(coq_chars
        .into_iter()
        .rev()
        .fold(Const(String::from("EmptyString")), |prec, expr| {
            App(vec![
                box App(vec![box Const(String::from("String")), box expr]),
                box prec,
            ])
        }))
}

fn transpile_match(
    expr: Box<Expr>,
    branches: Vec<Box<MatchBranch>>,
    rho: &Rho,
    config: Config,
) -> Result<CoqExpr, String> {
    let (wild_branch, coq_expr, branches) = preprocess_match(expr, branches, rho, config)?;
    branches
        .into_iter()
        .try_rfold(wild_branch, |els_branch, branch| {
            let MatchBranch { pat, expr } = *branch;
            match pat {
                Pat::Constructor { ctor: ident, args } => {
                    let then_abs = args.iter().rfold(
                        transpile_expr(
                            *expr,
                            &rho.with_vars(&HashSet::from_iter(args.clone()))?,
                            config,
                        )?,
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

fn preprocess_match(
    expr: Box<Expr>,
    mut branches: Vec<Box<MatchBranch>>,
    rho: &Rho,
    config: Config,
) -> Result<(CoqExpr, CoqExpr, Vec<Box<MatchBranch>>), String> {
    let coq_expr = transpile_expr(*expr, rho, config)?;
    let last_branch = branches.last().ok_or("Empty match.")?;
    let branches_len = branches.len();
    if config.optimize {
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
    };
    let last_branch = branches.last().ok_or("Empty match.")?;
    let is_last_branch_wild = if let Pat::Ignore = last_branch.pat {
        true
    } else {
        false
    };

    if config.strict {
        let (is_exhaustive, matched_ctor_group, current_ctors) =
            branches
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
                                let new_ctors = matched_ctors.union(&hashset! {ctor.clone()}).cloned().collect();
                                rho.find_ctor_group(&new_ctors)
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
                    let matched_ctor_group = rho.find_ctor_group(&x)
                        .ok_or(String::from("unexpected error"))?;
                    if matched_ctor_group.len() > x.len() {
                        Ok((false, matched_ctor_group, x))
                    } else {
                        Ok((true, matched_ctor_group, x))
                    }
                })?;

        let (wild_branch, truncate_branch) = if is_last_branch_wild {
            Ok((
                transpile_expr(*last_branch.expr.clone(), rho, config)?,
                true,
            ))
        } else if is_exhaustive {
            if let Pat::Constructor { ctor: _, args } = last_branch.pat.clone() {
                if config.optimize && args.len() == 0 {
                    Ok((
                        transpile_expr(
                            *last_branch.expr.clone(),
                            &rho.with_vars(&HashSet::from_iter(args.clone()))?,
                            config,
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

        Ok((wild_branch, coq_expr, branches))
    } else {
        let (wild_branch, truncate_branch) = if is_last_branch_wild {
            (
                transpile_expr(*last_branch.expr.clone(), rho, config)?,
                true,
            )
        } else {
            (Const(String::from("UNREACHABLE")), false)
        };

        if truncate_branch {
            branches.truncate(branches.len() - 1);
        };
        Ok((wild_branch, coq_expr, branches))
    }
}

fn extract_base_rho(stmts: &Vec<Stmt>, config: Config) -> Result<Rho, String> {
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
                            if config.strict {
                                Err(format!("Duplicate const declaration: {}", ctor))
                            } else {
                                eprintln!("Duplicate const declaration: {}. Ignored.", ctor);
                                Ok((group, new_symbols))
                            }
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
