use crate::error::ErrorRepr;
use crate::Error;
use crate::{ir, regex::Regex, reserved::*, Visitor};

use arbitrary::{Arbitrary, Unstructured};
use std::{collections::HashSet, fmt, str::FromStr};

/// A state machine that produces `arbitrary` matching expressions or byte sequences from `Unstructured`.
///
/// # Implementation
/// ## Construction
/// `Grammar` is constructed using `from_str` of a string that specifies the syntax of expressions:
/// - A peg parser converts the string into an "intermediary representation" AST (in ir.rs).
/// - The IR is validated for duplicate and conflicting rule definitions
/// - The IR is converted to a state machine in which regex is parsed and rule definitions are indexed.
///
/// ## Expression Generation
/// `Unstructured` is used to generate `arbitrary` choices and loops to traverse the state machine.
/// When a "leaf" state is reached, e.g. a pre-defined rule, regex, or string literal, `Unstructured`
/// is used to write arbitrary data (except for string literals) to an output buffer.
#[derive(Debug)]
pub struct Grammar(Vec<Expr>);

impl Grammar {
    /// Returns a resulting `Visitor` after an arbitirary state machine traversal.
    ///
    /// The state machine traversal starts at the first rule in the grammar.
    pub fn expression<V: Visitor>(
        &self,
        u: &mut Unstructured<'_>,
        max_depth: Option<usize>,
    ) -> arbitrary::Result<V> {
        // Maybe there's a smarter way to pre-allocate the buffer,
        // like predicting or pre-computing arbitrary lengths (but tracking
        // that requires another data structure).
        //
        // It's simple and efficient enough to let 2x Vec growth do it's thing.
        let mut visitor = V::new();
        let mut to_write = vec![(&self.0[0], 0)]; // always start at first rule

        while let Some((expr, depth)) = to_write.pop() {
            if depth > max_depth.unwrap_or(usize::MAX) {
                return Err(arbitrary::Error::IncorrectFormat);
            }

            match expr {
                Expr::Or(v) => {
                    let arb_index = u.int_in_range(0..=(v.len() - 1))?;
                    to_write.push((&v[arb_index], depth + 1));
                    visitor.visit_or(arb_index);
                }
                Expr::Concat(v) => {
                    to_write.extend(v.iter().map(|x| (x, depth + 1)));
                    visitor.visit_concat();
                }
                Expr::Optional(x) => {
                    let b = bool::arbitrary(u)?;
                    if b {
                        to_write.push((x, depth + 1));
                    }
                    visitor.visit_optional(b);
                }
                Expr::Repetition(x, min_rep) => {
                    let mut reps = 0;
                    u.arbitrary_loop(Some(*min_rep), Some(10), |_| {
                        to_write.push((x, depth + 1));
                        reps += 1;
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    visitor.visit_repetition(reps);
                }
                Expr::Reference(index) => {
                    to_write.push((&self.0[*index], depth + 1));
                    visitor.visit_reference(*index);
                }
                Expr::Literal(s) => visitor.visit_literal(s.as_str()),
                Expr::Bytes(b) => visitor.visit_bytes(b),
                Expr::Regex(regex) => regex.visit(&mut visitor, u)?,
                Expr::Group(x) => to_write.push((x, depth + 1)),
                Expr::Predefined(v) => v.visit(&mut visitor, u)?,
            }
        }
        Ok(visitor)
    }
}

/// Pretty prints the state machine.
///
/// It's helpful to check if the compiled state machine matches
/// what is expected from the the un-parsed grammar
/// (the printed rules are more verbose and order of operations is clearer)
impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, rule) in self.0.iter().enumerate() {
            writeln!(f, "{}: {}", i, rule)?;
        }
        Ok(())
    }
}

impl FromStr for Grammar {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed_ir = ir::bnf::expr(s).map_err(|e| Error(ErrorRepr::Grammar(e)))?;
        Self::try_from(parsed_ir)
    }
}

impl TryFrom<Vec<(String, ir::Expr)>> for Grammar {
    type Error = Error;

    fn try_from(value: Vec<(String, ir::Expr)>) -> Result<Self, Self::Error> {
        let (mut names, ir_exprs): (Vec<String>, Vec<ir::Expr>) = value.into_iter().unzip();

        if let Some(dups) = find_duplicates(&names) {
            return Err(Error(ErrorRepr::DuplicateVars(dups)));
        }

        if let Some(res) = filter_reserved_keywords(&names) {
            return Err(Error(ErrorRepr::Reserved(res)));
        }

        names.extend(Predefined::all().map(|s| s.as_str().to_string()));

        let mut exprs = ir_exprs
            .into_iter()
            .map(|ir_expr| Expr::try_new(ir_expr, &names))
            .collect::<Result<Vec<Expr>, _>>()?;

        exprs.extend(Predefined::all().map(Expr::Predefined));

        assert_eq!(names.len(), exprs.len());
        Ok(Self(exprs))
    }
}

fn find_duplicates(names: &[String]) -> Option<HashSet<String>> {
    let mut set: HashSet<String> = names.iter().cloned().collect();
    let dups: HashSet<String> = names.iter().filter(|&n| !set.remove(n)).cloned().collect();
    (!dups.is_empty()).then_some(dups)
}

#[derive(Debug)]
enum Expr {
    Or(Vec<Expr>),
    Concat(Vec<Expr>),
    Optional(Box<Expr>),
    Repetition(Box<Expr>, u32),
    Reference(usize),
    Literal(String),
    Regex(Regex),
    Bytes(Vec<u8>),
    Group(Box<Expr>),
    Predefined(Predefined),
}

fn fmt_w_name<'a>(
    name: &'static str,
    x: impl Iterator<Item = &'a Expr>,
    f: &mut fmt::Formatter<'_>,
) -> Result<(), fmt::Error> {
    write!(
        f,
        "{}({})",
        name,
        x.into_iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>()
            .join(", ")
    )
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Or(x) => fmt_w_name("or", x.iter(), f)?,
            Self::Concat(x) => fmt_w_name("concat", x.iter().rev(), f)?,
            Self::Optional(x) => write!(f, "option({})", x)?,
            Self::Repetition(x, _) => write!(f, "repeat({})", x)?,
            Self::Reference(index) => write!(f, "{}", index)?,
            Self::Literal(l) => write!(f, "{:?}", l)?,
            Self::Regex(_) => write!(f, "regex")?, // TODO: no way to pretty print regex
            Self::Bytes(b) => write!(f, "{:?}", b)?,
            Self::Group(x) => write!(f, "({})", x)?,
            Self::Predefined(p) => write!(f, "{}", p.as_str())?,
        }
        Ok(())
    }
}

impl Expr {
    /// Converts the intermediary representation into a "compiled" state machine.
    ///
    /// Checks done:
    /// - parses regex
    /// - Converts rule references to rule indexes
    fn try_new(ir_expr: ir::Expr, names: &[String]) -> Result<Self, Error> {
        Ok(match ir_expr {
            ir::Expr::Or(x) => Self::Or(
                x.into_iter()
                    .map(|e| Self::try_new(e, names))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            ir::Expr::Concat(x) => {
                let mut y = x
                    .into_iter()
                    .map(|e| Self::try_new(e, names))
                    .collect::<Result<Vec<_>, _>>()?;
                y.reverse(); // reverse so that `expression` can use a stack
                Self::Concat(y)
            }
            ir::Expr::Optional(x) => Self::Optional(Box::new(Self::try_new(*x, names)?)),
            ir::Expr::Repetition(x, min) => {
                Self::Repetition(Box::new(Self::try_new(*x, names)?), min)
            }
            ir::Expr::Group(x) => Self::Group(Box::new(Self::try_new(*x, names)?)),
            ir::Expr::Reference(name) => match names.iter().position(|n| *n == name) {
                Some(i) => Self::Reference(i),
                None => return Err(Error(ErrorRepr::UnkownVar(name))),
            },
            ir::Expr::Literal(x) => Self::Literal(x),
            ir::Expr::Regex(r) => {
                Self::Regex(Regex::compile(&r, 10).map_err(|e| Error(ErrorRepr::Regex(e)))?)
            }
            ir::Expr::Bytes(x) => Self::Bytes(x),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catches_duplicates() {
        for x in [
            r#"x: y; x: z;"#,
            r#"x: y; x: x;"#,
            r#"ok: x; x: y; y: x; x: x;"#,
        ] {
            let result: Error = x.parse::<Grammar>().unwrap_err();
            assert_eq!(
                result,
                Error(ErrorRepr::DuplicateVars(["x".into()].into_iter().collect()))
            )
        }

        for x in [
            r#"x: y; x: z; y: x; y: y;"#,
            r#"x: x; y: x; y: y; x: y; x: z;"#,
        ] {
            let result: Error = x.parse::<Grammar>().unwrap_err();
            assert_eq!(
                result,
                Error(ErrorRepr::DuplicateVars(
                    ["x".into(), "y".into()].into_iter().collect()
                ))
            )
        }
    }

    #[test]
    fn rejects_reserved() {
        for x in [r#"u16: u16 ;"#, r#"u16: [8, 8]  ;"#] {
            let result: Error = x.parse::<Grammar>().unwrap_err();
            assert_eq!(
                result,
                Error(ErrorRepr::Reserved(["u16".into()].into_iter().collect()))
            )
        }

        for x in [r#"String: u16 ;"#, r#"String: [8, 8]  ;"#] {
            let result: Error = x.parse::<Grammar>().unwrap_err();
            assert_eq!(
                result,
                Error(ErrorRepr::Reserved(["String".into()].into_iter().collect()))
            )
        }
    }
}
