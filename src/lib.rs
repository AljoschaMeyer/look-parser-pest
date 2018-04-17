#![feature(custom_attribute)]

extern crate pest;
#[macro_use]
extern crate pest_derive;

pub mod ast;
mod unescape;

#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("look.pest");


#[derive(Parser)]
#[grammar = "look.pest"]
pub struct LookParser;
