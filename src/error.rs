use std::collections::HashSet;
use std::fmt;

/// The type of error that can occur when parsing a grammar.
#[derive(Debug, PartialEq)]
pub struct Error(pub(crate) ErrorRepr);

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.0 {
            ErrorRepr::Regex(e) => Some(e),
            ErrorRepr::Grammar(e) => Some(e),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) enum ErrorRepr {
    Regex(crate::regex::Error),
    Grammar(peg::error::ParseError<peg::str::LineCol>),
    UnkownVar(String),
    DuplicateVars(HashSet<String>),
    Reserved(Vec<String>),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ErrorRepr::Regex(e) => e.fmt(f),
            ErrorRepr::Grammar(e) => e.fmt(f),
            ErrorRepr::UnkownVar(e) => write!(f, "Unkown variable reference: {}", e),
            ErrorRepr::DuplicateVars(e) => write!(f, "Duplicate variable definitions: {:?}", e),
            ErrorRepr::Reserved(e) => write!(f, "Reserved variable name: {:?}", e),
        }
    }
}
