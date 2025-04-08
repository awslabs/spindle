#![allow(rustdoc::bare_urls)]
#![doc = include_str!("../README.md")]

mod grammar;
mod ir;
mod regex;
mod reserved;
mod visitor;

pub use grammar::{Error, Grammar};
pub use visitor::Visitor;
