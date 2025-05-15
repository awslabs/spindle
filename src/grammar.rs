use crate::error::ErrorRepr;
use crate::Error;
use crate::{ir, regex::Regex, reserved::*, Visitor};

use arbitrary::{Arbitrary, Unstructured};
use std::{collections::HashSet, fmt, str::FromStr};

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

    // `how_many[i]` == number of possible traversals at the ith depth
    // i.e. memoized results of `how_many` calculated on construction.
    how_many: Vec<Option<u64>>,

    // `reachable[i][j]` == first depth that is reachable by the `i`th branch `Expr`'s `j`th branch.
    // Branch `Expr`s are `Expr::Optional`, `Expr::Or`, `Expr::Repetition`.
    // `reachable` is used in `expression`: branches that are not reachable at the current depth are not explored.
    reachable: Vec<Vec<usize>>,
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
        let mut to_write = vec![(&self.rules[0], max_depth.unwrap_or(usize::MAX))]; // always start at first rule

        while let Some((expr, depth)) = to_write.pop() {
            if depth == 0 {
                return Err(arbitrary::Error::IncorrectFormat);
            }

            match expr {
                Expr::Or(v, i) => {
                    // TODO: might be better way to choose a random item from a filtered list
                    // will explore ways to avoid the vec allocation when we have benchmarks.
                    let avail: Vec<_> = (0..v.len())
                        .filter(|j| self.reachable(depth, *i, *j))
                        .collect();
                    let arb_index = u.choose_iter(avail.iter())?;
                    to_write.push((&v[*arb_index], depth));
                    visitor.visit_or(*arb_index);
                }
                Expr::Concat(v) => {
                    to_write.extend(v.iter().map(|x| (x, depth)));
                    visitor.visit_concat();
                }
                Expr::Optional(x, i) => {
                    let b = self.reachable(depth, *i, 0) && bool::arbitrary(u)?;
                    if b {
                        to_write.push((x, depth));
                    }
                    visitor.visit_optional(b);
                }
                Expr::Repetition(x, min_rep, max_rep, i) => {
                    let mut reps = 0;
                    if self.reachable(depth, *i, 0) {
                        u.arbitrary_loop(Some(*min_rep), Some(*max_rep), |_| {
                            to_write.push((x, depth));
                            reps += 1;
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                    }
                    visitor.visit_repetition(reps);
                }
                Expr::Reference(index) => {
                    to_write.push((&self.rules[*index], depth - 1));
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

    /// Returns `true` if the `i`th branch `Expr`s `j`th branch is reachable at `depth`.
    fn reachable(&self, depth: usize, i: usize, j: usize) -> bool {
        depth > self.reachable[i][j]
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
        let target_depth = std::cmp::min(max_depth.unwrap_or(usize::MAX), self.how_many.len() - 1);
        self.how_many[target_depth]
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

        let mut reachable: Vec<Vec<usize>> = Vec::new();
        let rules = ir_exprs
            .into_iter()
            .map(|ir_expr| Expr::try_new(ir_expr, &names, &mut reachable))
            .collect::<Result<Vec<Expr>, _>>()?;

        // Use a bottom up approach for calculating the number of traversals:
        // 1. all rules have 0 traversals at depth 0.
        // 2. prev[i] == `how_many` for the ith rule at the previously calculated depth.
        // 3. dp[i] == `how_many` for the ith rule the current depth which depends on `prev`.
        // 4. finally return `how_many` for the first (start) rule.
        let mut how_many = vec![Some(0u64)];
        let mut prev = vec![Some(0u64); rules.len()];
        loop {
            let dp: Vec<_> = rules
                .iter()
                .map(|r| r.how_many(&rules, &prev, &mut reachable))
                .collect();

            how_many.push(dp[0]);

            // discovered all possible or already exceeded `u64::MAX`
            if dp == prev || dp[0] == None {
                break;
            }

            prev = dp;
        }

        assert_eq!(names.len(), rules.len());
        Ok(Self {
            rules,
            reachable,
            how_many,
        })
    }
}

fn find_duplicates(names: &[String]) -> Option<HashSet<String>> {
    let mut set: HashSet<String> = names.iter().cloned().collect();
    let dups: HashSet<String> = names.iter().filter(|&n| !set.remove(n)).cloned().collect();
    (!dups.is_empty()).then_some(dups)
}

/// Branch `Expr`s (`Optional`, `Or`, `Repetition`) contain a `usize`
/// which is index of the branch in the state machine (pre-ordered).
#[derive(Debug)]
enum Expr {
    Or(Vec<Expr>, usize),
    Concat(Vec<Expr>),
    Optional(Box<Expr>, usize),
    Repetition(Box<Expr>, u32, u32, usize),
    Reference(usize),
    Literal(String),
    Regex(Regex),
    Bytes(Vec<u8>),
    Group(Box<Expr>),
    Predefined(Predefined),
}

impl Expr {
    fn add(x: Option<u64>, y: Option<u64>) -> Option<u64> {
        x?.checked_add(y?)
    }

    fn mul(x: Option<u64>, y: Option<u64>) -> Option<u64> {
        x?.checked_mul(y?)
    }

    /// See [`Grammar::how_many`].
    ///
    /// `mem` is previously calculated `how_many` for `depth - 1` for each `Reference::Expr`/rule in `rules`.
    /// `reachable` is semi-built `Grammar.reachable`. If the expr is not reachable, `reachable[i][j]` is incremented to
    /// finally indicate the first depth in which the jth branch in ith rule is reachable.
    fn how_many(
        &self,
        rules: &[Expr],
        mem: &[Option<u64>],
        reachable: &mut [Vec<usize>],
    ) -> Option<u64> {
        match self {
            Self::Or(x, i) => {
                let mut res = Some(0u64);
                for (j, child) in x.iter().enumerate() {
                    let sub_res = child.how_many(rules, mem, reachable);
                    let child_reachable = sub_res.map_or(true, |x| x > 0);
                    if !child_reachable {
                        reachable[*i][j] += 1;
                    }
                    res = Self::add(res, sub_res);
                }
                res
            }
            Self::Concat(x) => {
                let mut res = Some(1u64);
                for child in x.iter() {
                    let sub_res = child.how_many(rules, mem, reachable);
                    res = Self::mul(res, sub_res);
                }
                res
            }
            Self::Optional(x, i) => {
                let child = x.how_many(rules, mem, reachable);
                let child_reachable = child.map_or(true, |x| x > 0);
                if !child_reachable {
                    reachable[*i][0] += 1;
                }
                1u64.checked_add(child?)
            }
            Self::Repetition(x, min_reps, max_reps, i) => {
                let mut res = Some(0u64);
                let child = x.how_many(rules, mem, reachable);
                let child_reachable = child.map_or(true, |x| x > 0);
                if !child_reachable {
                    reachable[*i][0] += 1;
                }
                match child {
                    Some(child) if child > 1 => {
                        for used_rep in *min_reps..=*max_reps {
                            let (sub_res, overflow) = child.overflowing_pow(used_rep);
                            res = Self::add(res, (!overflow).then_some(sub_res));
                            if res.is_none() {
                                break;
                            }
                        }
                    }
                    Some(child) if child == 1 => {
                        // e.g. min,max = 1,3
                        // "1", "11", "111" -- 3 options
                        let range = *max_reps as u64 - *min_reps as u64 + 1;
                        res = Self::add(res, Some(range));
                    }
                    _ => (),
                }
                res
            }
            Self::Group(x) => x.how_many(rules, mem, reachable),
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
            Self::Or(x, _) => fmt_w_name("or", x.iter(), f)?,
            Self::Concat(x) => fmt_w_name("concat", x.iter().rev(), f)?,
            Self::Optional(x, _) => write!(f, "option({})", x)?,
            Self::Repetition(x, min, max, _) => write!(f, "repeat({}, {}, {})", x, min, max)?,
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
    /// Also populates `reachable`, see `Grammar.reachable`.
    ///
    /// Checks done:
    /// - parses regex
    /// - Converts rule references to rule indexes
    fn try_new(
        ir_expr: ir::Expr,
        names: &[String],
        reachable: &mut Vec<Vec<usize>>,
    ) -> Result<Self, Error> {
        Ok(match ir_expr {
            ir::Expr::Or(x) => {
                let child = x
                    .into_iter()
                    .map(|e| Self::try_new(e, names, reachable))
                    .collect::<Result<Vec<_>, _>>()?;
                reachable.push(vec![0; child.len()]);
                Self::Or(child, reachable.len() - 1)
            }
            ir::Expr::Concat(x) => {
                let mut y = x
                    .into_iter()
                    .map(|e| Self::try_new(e, names, reachable))
                    .collect::<Result<Vec<_>, _>>()?;
                y.reverse(); // reverse so that `expression` can use a stack
                Self::Concat(y)
            }
            ir::Expr::Optional(x) => {
                let child = Box::new(Self::try_new(*x, names, reachable)?);
                reachable.push(vec![0]);
                Self::Optional(child, reachable.len() - 1)
            }
            ir::Expr::Repetition(x, min, max) => {
                let child = Box::new(Self::try_new(*x, names, reachable)?);
                reachable.push(vec![0]);
                Self::Repetition(child, min, max, reachable.len() - 1)
            }
            ir::Expr::Group(x) => Self::Group(Box::new(Self::try_new(*x, names, reachable)?)),
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
    use std::hash::Hash;

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

    #[test]
    fn rejects_incorrect_ranges() {
        for x in [
            r#"expr: "0"{3,2} ;"#,
            r#"expr: "0"{3,0} ;"#,
            r#"expr: "0"a3,a} ;"#,
            r#"expr: "0"{a,b} ;"#,
            r#"expr: "0"{2,0} ;"#,
            r#"expr: "0"{0,-1} ;"#,
            r#"expr: "0"{-1,3} ;"#,
            r#"expr: "0"{3a} ;"#,
            r#"expr: "0"{-1} ;"#,
            r#"expr: "0"{} ;"#,
        ] {
            assert!(x.parse::<Grammar>().is_err());
        }
    }

    fn assert_how_many_matches_generations<T: Visitor + Hash + Eq>(
        grammar: &Grammar,
        depth: usize,
    ) {
        let mut buf = [0u8; 1024];
        let num_classes = grammar
            .how_many(Some(depth))
            .expect("small number of classes") as usize;
        assert!(num_classes < 10_000);
        let mut classes = fxhash::FxHashSet::<T>::default();
        classes.try_reserve(num_classes).unwrap();

        let mut rng = StdRng::seed_from_u64(42);

        // pick `num_iterations` to reduce prob of test being accurate
        // note, not all classes have the same probability of being picked!
        // note, 400 is tuned
        let num_iterations = 400 * num_classes;

        for _ in 0..num_iterations {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            if let Ok(class) = grammar.expression::<T>(&mut u, Some(depth)) {
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
        assert_how_many_matches_generations::<u64>(&grammar, 1);
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
        assert_how_many_matches_generations::<u64>(&grammar, 1);

        // 2 + (2 * 2)
        // 2: "1" or "2"
        // 2 * 2: ("3" or "4") * ("5" or "6")
        assert_eq!(grammar.how_many(Some(2)), Some(6));
        assert_how_many_matches_generations::<u64>(&grammar, 2);

        let grammar: Grammar = r#"
            expr : "1" | "2" | num? ;
            num  : ("3" | "4") "." ("5" | "6") ;
        "#
        .parse()
        .unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(7));
        assert_how_many_matches_generations::<u64>(&grammar, 2);
        assert_eq!(grammar.how_many(None), Some(7));
    }

    #[test]
    fn how_many_static_reps() {
        let grammar: Grammar = r#"
            expr : num{6} ;
            num  : "0" | "1" ;
        "#
        .parse()
        .unwrap();

        // 2 choices, exactly 6 times... 2^6 = 64
        assert_eq!(grammar.how_many(Some(2)), Some(64));
        assert_eq!(grammar.how_many(None), Some(64));
        assert_how_many_matches_generations::<u64>(&grammar, 2);
    }

    #[test]
    fn how_many_bounded_reps() {
        let grammar: Grammar = r#"
            expr : num{0,6} ;
            num  : "0" | "1" ;
        "#
        .parse()
        .unwrap();

        // 0 reps: 1
        // 1 reps: 2 ("0" or "1")
        // 2 reps: 2^2
        // 3 reps: 2^3
        // ...
        assert_eq!(grammar.how_many(Some(2)), Some(127));
        assert_eq!(grammar.how_many(None), Some(127));
        assert_how_many_matches_generations::<u64>(&grammar, 2);
    }

    #[test]
    fn how_many_inf_reps() {
        let grammar: Grammar = r#"
            expr : num* ;
            num  : "0" | "1" ;
        "#
        .parse()
        .unwrap();

        assert_eq!(grammar.how_many(Some(2)), None);
        assert_eq!(grammar.how_many(None), None);

        let grammar: Grammar = r#"
            expr : num* ;
            num  : "0" ;
        "#
        .parse()
        .unwrap();

        assert_eq!(
            grammar.how_many(Some(2)),
            Some(crate::MAX_REPEAT as u64 + 1)
        );
        assert_eq!(grammar.how_many(None), Some(crate::MAX_REPEAT as u64 + 1));

        let grammar: Grammar = r#"
            expr : num* ;
            num  : "0" | r"[a-z]{2,3}" ;
        "#
        .parse()
        .unwrap();

        assert_eq!(grammar.how_many(Some(2)), None);
        assert_eq!(grammar.how_many(None), None);
    }

    #[test]
    fn how_many_choice() {
        let grammar: Grammar = r#"expr : "1"? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(2));
        assert_how_many_matches_generations::<u64>(&grammar, 2);

        let grammar: Grammar = r#"expr : ("1" | "2" )? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(3));
        assert_how_many_matches_generations::<u64>(&grammar, 2);

        // "1", "2", "", or "" (outer)
        let grammar: Grammar = r#"expr : ("1" | "2"? )? ;"#.parse().unwrap();
        assert_eq!(grammar.how_many(Some(2)), Some(4));
        assert_how_many_matches_generations::<u64>(&grammar, 2);
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
        assert_how_many_matches_generations::<u64>(&grammar, 1);

        // a singular number
        // two numbers with 4 possible operators
        // 1 + 4
        assert_eq!(grammar.how_many(Some(2)), Some(5));
        assert_how_many_matches_generations::<u64>(&grammar, 2);

        // combinations are:
        // 1 singular number
        // + 5 possible expressions (from above) on the left
        // * 4 possible symbols
        // * 5 possible expressions on the right
        assert_eq!(grammar.how_many(Some(3)), Some(101));
        assert_how_many_matches_generations::<u64>(&grammar, 3);
        assert_eq!(grammar.how_many(None), None);
    }

    #[test]
    fn how_many_with_prefined() {
        let grammar: Grammar = r#"
            one : "1" | "2" | (u16 | String)? | u16? | (u16 | String){6} ;
        "#
        .parse()
        .unwrap();
        assert_how_many_matches_generations::<u64>(&grammar, 2);
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
        assert_how_many_matches_generations::<u64>(&grammar, 1);
        // only "1" and "2" are reachable, `nested` is a reference
        // and needs one more depth!
        assert_eq!(grammar.how_many(Some(2)), Some(2));
        assert_how_many_matches_generations::<u64>(&grammar, 2);

        // 3 + 2 * 4 * 2
        assert_eq!(grammar.how_many(Some(3)), Some(19));
        assert_how_many_matches_generations::<u64>(&grammar, 3);

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
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    fn success_count(grammar: &Grammar, depth: usize, total: usize) -> usize {
        let mut buf = [0u8; 1024];
        let mut rng = StdRng::seed_from_u64(42);

        let mut valid = 0;
        for _ in 0..total {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            valid += grammar.expression::<u64>(&mut u, Some(depth)).is_ok() as usize;
        }
        valid
    }

    #[test]
    fn avoid_long_expr_opt_ref() {
        let grammar: Grammar = r#"
            one : two?;
            two : "2" ;
        "#
        .parse()
        .unwrap();

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_long_expr_opt_hardcoded() {
        let grammar: Grammar = r#"
            one : "2"?;
        "#
        .parse()
        .unwrap();

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_long_expr_opt_hardcoded_paren() {
        let grammar: Grammar = r#"
            one : ("2")?;
        "#
        .parse()
        .unwrap();

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_long_expr_or() {
        let grammar: Grammar = r#"
            one : "1" | two ;
            two : "2" | three ;
            three : "3" ;
        "#
        .parse()
        .unwrap();

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_long_expr_rep_0_or_more() {
        let grammar: Grammar = r#"
            one : "1" | two{4} ;
            two : "2";
        "#
        .parse()
        .unwrap();

        assert_eq!(grammar.how_many(Some(1)), Some(1));

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_long_expr_rep_1_or_more() {
        let grammar: Grammar = r#"
            one : "1" | two{1,3} ;
            two : "2";
        "#
        .parse()
        .unwrap();

        for depth in 1..=4 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_impossible_deep_ref() {
        let grammar: Grammar = r#"
            one : two ;
            two : three ;
            three : "3";
        "#
        .parse()
        .unwrap();

        for depth in 0..=2 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 0);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
            assert_how_many_matches_generations::<String>(&grammar, depth);
        }
        let valid = success_count(&grammar, 3, 100);
        assert_eq!(valid, 100);
        assert_how_many_matches_generations::<u64>(&grammar, 3);
        assert_how_many_matches_generations::<String>(&grammar, 3);
    }

    #[test]
    fn avoid_example() {
        let grammar: Grammar = r#"
            one : "1" | two three ;
            two : "2" "2"? ;
            three : three_inner ;
            three_inner : "3"   ;
        "#
        .parse()
        .unwrap();

        for depth in 1..=8 {
            let valid = success_count(&grammar, depth, 100);
            assert_eq!(valid, 100);
            assert_how_many_matches_generations::<u64>(&grammar, depth);
        }
    }

    #[test]
    fn avoid_mixed_branches() {
        let grammar: Grammar = r#"
            expr : "qwerty"{2,4} | "4" | (two)? ;
            two : "5"{3} | three | three four? ;
            three : two | three ;
            four  : "4" ;
        "#
        .parse()
        .unwrap();

        for depth in 1..=6 {
            assert_how_many_matches_generations::<u64>(&grammar, depth);
        }

        for depth in 1..=30 {
            let valid = success_count(&grammar, depth, 10);
            assert_eq!(valid, 10);
        }
    }
}
