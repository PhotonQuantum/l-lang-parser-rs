use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

use crate::parser::CtorDef;

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Symbol {
    Const,
    Var,
    Func,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Rho {
    pub symbols: HashMap<String, Symbol>,
    pub ctors: Vec<HashSet<CtorDef>>,
}

impl Rho {
    pub fn with_vars(&self, vars: &HashSet<String>) -> Result<Rho, String> {
        let var_symbols: HashMap<String, Symbol> =
            vars.iter().map(|var| (var.clone(), Symbol::Var)).collect();
        self.with(&var_symbols, true)
    }

    pub fn with_funcs(&self, funcs: &HashSet<String>) -> Result<Rho, String> {
        let func_symbols: HashMap<String, Symbol> = funcs
            .iter()
            .map(|var| (var.clone(), Symbol::Func))
            .collect();
        self.with(&func_symbols, false)
    }

    pub fn with(
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

    pub fn find_symbol(&self, ident: &str) -> Option<Symbol> {
        self.symbols.get(ident).copied()
    }

    pub fn find_ctor_group(&self, ctors: &HashSet<CtorDef>) -> Option<HashSet<CtorDef>> {
        self.ctors
            .iter()
            .filter(|group| group.is_superset(ctors))
            .next()
            .cloned()
    }

    pub fn find_ctor(&self, ident: &str) -> Option<CtorDef> {
        self.ctors
            .iter()
            .filter_map(|group| group.into_iter().filter(|ctor| ctor.ident == ident).next())
            .next()
            .cloned()
    }

    pub fn list_funcs(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Func)
            .map(|x| x.0.clone())
    }

    pub fn list_vars(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Var)
            .map(|x| x.0.clone())
    }

    pub fn list_consts(&self) -> impl Iterator<Item = String> + '_ {
        self.symbols
            .iter()
            .filter(|x| x.1 == &Symbol::Const)
            .map(|x| x.0.clone())
    }
}
