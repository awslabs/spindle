use crate::error::ErrorRepr;
use crate::Error;
use crate::{ir, regex::Regex, reserved::*, Visitor};

use arbitrary::{Arbitrary, Unstructured};
use std::{collections::HashSet, fmt, str::FromStr};

const MAX_REP: u32 = 8; // TODO, make interface for user to control this

/// A state machine that produces `Arbitrary` matching expressions or byte sequences from [`Unstructured`](https://docs.rs/arbitrary/latest/arbitrary/struct.Unstructured.html).
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
pub struct Grammar {
    rules: Vec<Expr>,
}

impl Grammar {
    /// Returns a resulting `Visitor` after an arbitirary state machine traversal.
    ///
    /// The state machine traversal starts at the first rule in the grammar.
    ///
    /// # Parameters
    /// `max_depth` is nesting limit of rule referencing during the traversal.
    /// For example, the below grammar generates numbers less than or equal to the `max_depth` parameter.
    /// ```text
    /// one   : "1" | two ;
    /// two   : "2" | three ;
    /// three : "3" ;
    /// ```
    pub fn expression<V: Visitor>(
        &self,
        u: &mut Unstructured<'_>,
        max_depth: Option<usize>,
    ) -> arbitrary::Result<V> {
        let mut visitor = V::new();
        let mut to_write = vec![(&self.rules[0], 0)]; // always start at first rule

        while let Some((expr, depth)) = to_write.pop() {
            if depth >= max_depth.unwrap_or(usize::MAX) {
                return Err(arbitrary::Error::IncorrectFormat);
            }

            match expr {
                Expr::Or(v) => {
                    let arb_index = u.int_in_range(0..=(v.len() - 1))?;
                    to_write.push((&v[arb_index], depth));
                    visitor.visit_or(arb_index);
                }
                Expr::Concat(v) => {
                    to_write.extend(v.iter().map(|x| (x, depth)));
                    visitor.visit_concat();
                }
                Expr::Optional(x) => {
                    let b = bool::arbitrary(u)?;
                    if b {
                        to_write.push((x, depth));
                    }
                    visitor.visit_optional(b);
                }
                Expr::Repetition(x, min_rep) => {
                    let mut reps = 0;
                    u.arbitrary_loop(Some(*min_rep), Some(MAX_REP), |_| {
                        to_write.push((x, depth));
                        reps += 1;
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    visitor.visit_repetition(reps);
                }
                Expr::Reference(index) => {
                    to_write.push((&self.rules[*index], depth + 1));
                    visitor.visit_reference(*index);
                }
                Expr::Literal(s) => visitor.visit_literal(s.as_str()),
                Expr::Bytes(b) => visitor.visit_bytes(b),
                Expr::Regex(regex) => regex.visit(&mut visitor, u)?,
                Expr::Group(x) => to_write.push((x, depth)),
                Expr::Predefined(v) => v.visit(&mut visitor, u)?,
            }
        }
        Ok(visitor)
    }

    /// Returns the number of possible state machine traversals for
    /// this state machine or `None` if the result exceeds `u64::MAX`.
    ///
    /// # Parameters
    /// `max_depth` is the maximum nested references that the traversal is allowed.
    /// A `max_depth` of 0 will always return 0.
    /// `grammar.how_many(depth)` is the number of unique values possible from
    /// `grammar.expression::<u64>(u, depth)`, barring hash collisions.
    ///
    /// # Usage
    /// Provides a rough possible number of equivalence classes of the grammar,
    /// which is useful for estimating overall coverage as the fuzzer discovers more
    /// classes over time.
    ///
    /// # Limitations
    /// 1. No traversals are counted inside of Regex and pre-defined (e.g. String) rules
    /// i.e. are counted as 1 possible traversal even though many regex expressions or Strings
    /// are possible.
    ///
    /// 2. The result is not aware of duplicate outputs, e.g.
    /// ```text
    /// expr : "foo" | "foo" ;
    /// ```
    /// counts as 2 traversals, even though every output is "foo".
    pub fn how_many(&self, max_depth: Option<usize>) -> Option<u64> {
        let target_depth = max_depth.unwrap_or(usize::MAX);
        if target_depth == 0 {
            return Some(0);
        }

        // Use a bottom up approach for calculating the number of traversals:
        // 1. all rules have 0 traversals at depth 0.
        // 2. prev[i] == `how_many` for the ith rule at the previously calculated depth.
        // 3. dp[i] == `how_many` for the ith rule the current depth which depends on `prev`.
        // 4. finally return `how_many` for the first (start) rule.
        let mut prev = vec![Some(0u64); self.rules.len()];

        for _ in 1..target_depth {
            let dp: Vec<_> = self
                .rules
                .iter()
                .map(|r| r.how_many(&self.rules, &prev))
                .collect();
            // discovered all possible or already exceeded `u64::MAX`
            if dp == prev || dp[0] == None {
                return dp[0];
            }
            prev = dp;
        }
        self.rules[0].how_many(&self.rules, &prev)
    }
}

/// Pretty prints the state machine.
///
/// It's helpful to check if the compiled state machine matches
/// what is expected from the the un-parsed grammar
/// (the printed rules are more verbose and order of operations is clearer)
impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (i, rule) in self.rules.iter().enumerate() {
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
        let (names, ir_exprs): (Vec<String>, Vec<ir::Expr>) = value.into_iter().unzip();

        if let Some(dups) = find_duplicates(&names) {
            return Err(Error(ErrorRepr::DuplicateVars(dups)));
        }

        if let Some(res) = filter_reserved_keywords(&names) {
            return Err(Error(ErrorRepr::Reserved(res)));
        }

        let rules = ir_exprs
            .into_iter()
            .map(|ir_expr| Expr::try_new(ir_expr, &names))
            .collect::<Result<Vec<Expr>, _>>()?;

        assert_eq!(names.len(), rules.len());
        Ok(Self { rules })
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

impl Expr {
    /// See [`Grammar::how_many`].
    ///
    /// `mem` is previously calculated `how_many` for `depth - 1` for each rule in `rules`.
    fn how_many(&self, rules: &[Expr], mem: &[Option<u64>]) -> Option<u64> {
        match self {
            Self::Or(x) => {
                let mut res = 0u64;
                for child in x.iter() {
                    let sub_res = child.how_many(rules, mem)?;
                    res = res.checked_add(sub_res)?;
                }
                Some(res)
            }
            Self::Concat(x) => {
                let mut res = 1u64;
                for child in x.iter() {
                    let sub_res = child.how_many(rules, mem)?;
                    res = res.checked_mul(sub_res)?;
                }
                Some(res)
            }
            Self::Optional(x) => 1u64.checked_add(x.how_many(rules, mem)?),
            Self::Repetition(x, min_reps) => {
                let mut res = 0u64;
                let sub_res = x.how_many(rules, mem)?;
                for used_rep in *min_reps..=MAX_REP {
                    res = res.checked_add(sub_res.pow(used_rep))?;
                }
                Some(res)
            }
            Self::Group(x) => x.how_many(rules, mem),
            Self::Reference(x) => mem[*x],
            _ => Some(1),
        }
    }
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
                None => Self::Predefined(Predefined::from_str(&name).map_err(Error)?),
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
    use rand::{rngs::StdRng, RngCore, SeedableRng};

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

    fn assert_how_many_matches_generations(grammar: &Grammar, depth: usize) {
        let mut buf = [0u8; 1024];
        let num_classes = grammar
            .how_many(Some(depth))
            .expect("small number of classes") as usize;
        assert!(num_classes < 10_000);
        let mut classes = fxhash::FxHashSet::<u64>::default();
        classes.try_reserve(num_classes).unwrap();

        let mut rng = StdRng::seed_from_u64(42);

        // pick `num_iterations` to reduce prob of test being accurate
        // note, not all classes have the same probability of being picked!
        // note, 400 is tuned
        let num_iterations = 400 * num_classes;

        for _ in 0..num_iterations {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            if let Ok(class) = grammar.expression::<u64>(&mut u, Some(depth)) {
                classes.insert(class);
            }
        }
        assert_eq!(classes.len(), num_classes);
    }

    #[test]
    fn how_many_or() {
        let grammar: Grammar = r#"num : "1" | "2" ;"#.parse().unwrap();

        for max in 1..=10 {
            assert_eq!(grammar.how_many(Some(max)), Some(2));
        }
        assert_eq!(grammar.how_many(None), Some(2));
        assert_how_many_matches_generations(&grammar, 1);
    }

    #[test]
    fn how_many_concat() {
        let grammar: Grammar = r#"
            expr : "1" | "2" | num ;
            num  : ("3" | "4") "." ("5" | "6") ;
        "#
        .parse()
        .unwrap();

        // only a depth of 1 is allowed, so "1" or "2"
        assert_eq!(grammar.how_many(Some(1)), Some(2));
        assert_how_many_matches_generations(&grammar, 1);

        // 2 + (2 * 2)
        // 2: "1" or "2"
        // 2 * 2: ("3" or "4") * ("5" or "6")
        assert_eq!(grammar.how_many(Some(2)), Some(6));
        assert_how_many_matches_generations(&grammar, 2);

        let grammar: Grammar = r#"
            expr : "1" | "2" | num? ;
            num  : ("3" | "4") "." ("5" | "6") ;
        "#
        .parse()
        .unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(7));
        assert_how_many_matches_generations(&grammar, 2);
        assert_eq!(grammar.how_many(None), Some(7));
    }

    #[test]
    fn how_many_reps() {
        let grammar: Grammar = r#"
            expr : num* ;
            num  : "0" | "1" ;
        "#
        .parse()
        .unwrap();

        // 0 reps: 1
        // 1 reps: 2 ("0" or "1")
        // 2 reps: 2^2
        // 3 reps: 2^3
        // ...
        assert_eq!(grammar.how_many(Some(2)), Some(511));
        assert_eq!(grammar.how_many(None), Some(511));
    }

    #[test]
    fn how_many_choice() {
        let grammar: Grammar = r#"expr : "1"? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(2));
        assert_how_many_matches_generations(&grammar, 2);

        let grammar: Grammar = r#"expr : ("1" | "2" )? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(3));
        assert_how_many_matches_generations(&grammar, 2);

        // "1", "2", "", or "" (outer)
        let grammar: Grammar = r#"expr : ("1" | "2"? )? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(4));
        assert_how_many_matches_generations(&grammar, 2);
        assert_eq!(grammar.how_many(None), Some(4));
    }

    #[test]
    fn how_many_simpler_math() {
        let grammar: Grammar = r#"
            expr   : u16 | expr symbol expr ;
            symbol : "+" | "-" | "*" | "/" ;
        "#
        .parse()
        .unwrap();

        assert_eq!(grammar.how_many(Some(1)), Some(1));
        assert_how_many_matches_generations(&grammar, 1);

        // a singular number
        // two numbers with 4 possible operators
        // 1 + 4
        assert_eq!(grammar.how_many(Some(2)), Some(5));
        assert_how_many_matches_generations(&grammar, 2);

        // combinations are:
        // 1 singular number
        // + 5 possible expressions (from above) on the left
        // * 4 possible symbols
        // * 5 possible expressions on the right
        assert_eq!(grammar.how_many(Some(3)), Some(101));
        assert_how_many_matches_generations(&grammar, 3);
        assert_eq!(grammar.how_many(None), None);
    }

    #[test]
    fn how_many_with_prefined() {
        let grammar: Grammar = r#"
            one : "1" | "2" | (u16 | String)? | u16? | (u16 | String)* ;
        "#
        .parse()
        .unwrap();
        assert_how_many_matches_generations(&grammar, 2);
    }

    #[test]
    fn how_many_simple_math() {
        let grammar: Grammar = r#"
            expr   : num | expr symbol expr ;
            symbol : "+" | "-" | "*" | "/" ;
            num    : nested | "1" | "2" ;
            nested : u16;
        "#
        .parse()
        .unwrap();

        assert_eq!(grammar.how_many(Some(1)), Some(0));
        assert_how_many_matches_generations(&grammar, 1);
        // only "1" and "2" are reachable, `nested` is a reference
        // and needs one more depth!
        assert_eq!(grammar.how_many(Some(2)), Some(2));
        assert_how_many_matches_generations(&grammar, 2);

        // 3 + 2 * 4 * 2
        assert_eq!(grammar.how_many(Some(3)), Some(19));
        assert_how_many_matches_generations(&grammar, 3);

        // This grammar is infinitely recursive
        assert_eq!(grammar.how_many(None), None);
    }

    #[test]
    fn how_many_nesting() {
        let grammar: Grammar = r#"
            one    : "1" | two ;
            two    : "2" | three ;
            three  : "3" ;
        "#
        .parse()
        .unwrap();
        assert_eq!(grammar.how_many(Some(10)), Some(3));
        for depth in 0..=3 {
            assert_how_many_matches_generations(&grammar, depth);
        }
    }
}
