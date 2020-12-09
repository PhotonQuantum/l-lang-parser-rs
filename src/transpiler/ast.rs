use std::fmt;
use std::fmt::{Display, Formatter};

use super::utils::indent;

use self::CoqExpr::*;

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
