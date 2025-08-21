//! Intermediary representation (ir) for a parsed grammar.

use peg::parser;

use crate::grammar::WeightType;

/// The maxium repititions in `+` and `*` rules.
/// This can be overriden with explicit range rules,
/// e.g. `"3"{0,2345678}` repeats up to 2345678 `"3"`s.
pub const MAX_REPEAT: u32 = 255;

/// If `Or` branches are not given weights, then they all default to having the same
/// weight of 1.
///
/// If this is ever changed, make sure the value is >= 1, otherwise grammar tests may fail.
const DEFAULT_WEIGHT: usize = 1;

parser! {
/// This parser is not meant to efficient, since parsing the grammar is not meant to be
/// on the hot path (unlike generating expressions).
pub grammar bnf() for str {
    pub rule expr() -> Vec<(String, Expr)>
        = l:(definition() ++ _)

    rule definition() -> (String, Expr)
        = _ s:reference() _ ":" _ e:branch() _ ";" _ { (s, e) }

    // NOTE: the order of the below parse rules is important
    rule branch() -> Expr
        = weighted_or()
        / or()

    rule branch_inner() -> Expr
        = _ x:concat() _ { x }
        / _ x:concat_inner() _ { x }

    rule weighted_branch_inner() -> (Expr, WeightType)
        = _ x:concat() _ "@" _ w:weight() _ { (x, w) }
        / _ x:concat_inner() _ "@" _ w:weight() _ { (x, w) }

    rule weight() -> WeightType
        = w:$(['0'..='9']+) {?
            // weights are parsed as u16 to avoid overflow issues when summing weights
            w.parse::<u16>()
                .and_then(|v| Ok(v as WeightType))
                .map_err(|_| "can't parse weight to u16")
        }

    rule concat_inner() -> Expr
        = rep()
        / choice()
        / expression()

    rule expression() -> Expr
        = terminal()
        / group()

    rule terminal() -> Expr
        = regex()
        / bytes()
        / s:reference() { Expr::Reference(s) }
        / literal()

    rule group() -> Expr
        = "(" _ r:branch() _ ")" { Expr::Group(Box::new(r)) }

    rule or() -> Expr
        = l:(branch_inner() **<1,64> "|") {?
            let weighted_exprs = l.into_iter().map(|e| (e, DEFAULT_WEIGHT)).collect::<Vec<_>>();
            let total_weight = weighted_exprs.len().checked_mul(DEFAULT_WEIGHT).ok_or("total weight does not fit in a usize")?;
            if total_weight > 0 {
                Ok(Expr::Or(weighted_exprs))
            } else {
                Err("total weight must be greater than 0")
            }
        }

    rule weighted_or() -> Expr
        = l:(weighted_branch_inner() **<1,64> "|") {?
            // branches with 0 weight are filtered out during parsing
            // this is done to not mess with how_many calculations
            let positive_weights = l.into_iter().filter(|(_e, w)| *w > 0).collect::<Vec<_>>();
            let total_weight = positive_weights.iter().map(|(_e, w)| w).try_fold(0usize, |acc, &x| acc.checked_add(x)).ok_or("total weight does not fit in a usize")?;
            if total_weight > 0 {
                Ok(Expr::Or(positive_weights))
            } else {
                Err("total weight must be greater than 0")
            }
        }

    rule rep() -> Expr
        = g:expression() _ "*" { Expr::Repetition(Box::new(g), 0, MAX_REPEAT) }
        / g:expression() _ "+" { Expr::Repetition(Box::new(g), 1, MAX_REPEAT) }
        / g:expression() _ "{" _ n:$(['0'..='9']+) _ "}" {?
            n.parse().map_or(Err("u32"), |reps| Ok(Expr::Repetition(Box::new(g), reps, reps)))
        }
        / g:expression() _ "{" _ n1:$(['0'..='9']+) _ "," _ n2:$(['0'..='9']+) _ "}" {?
            let min_reps = n1.parse().or(Err("u32"))?;
            let max_reps = n2.parse().or(Err("u32"))?;
            match min_reps < max_reps {
                true => Ok(Expr::Repetition(Box::new(g), min_reps, max_reps)),
                false => Err("Min repetitions cannot be larger than max repetitions"),
            }

        }

    rule choice() -> Expr
        = g:expression() _ "?" { Expr::Optional(Box::new(g)) }

    rule concat() -> Expr
        = l:(concat_inner() **<2,64> __) { Expr::Concat(l) }

    // the parser is designed to assume parsing a weight if a token starts with a number.
    // adding look-forward parsing to support identifiers that start with numbers is too difficult,
    // going to restrict identifiers to start with a letter or underscore
    rule reference() -> String
        = s:$(['a'..='z' | 'A'..='Z' | '_'] ['a'..='z' | 'A'..='Z' | '_' | '0'..='9']*) { s.to_string() }

    rule literal() -> Expr
        = s:string() { Expr::Literal(s) }

    rule regex() -> Expr
        = "r" s:string() { Expr::Regex(s) }

    rule _ = [' ' | '\n' | '\t']*
    rule __ = [' ' | '\n' | '\t']+

    rule string() -> String
        = "\"" s:string_inner() "\"" { s }

    rule bytes() -> Expr
        = "[" s:bytes_inner() "]" { Expr::Bytes(s) }

    rule bytes_inner() -> Vec<u8>
        = l:(byte_ws() ** ",") { l }

    rule byte_ws() -> u8
        = _ b:byte() _ { b }

    rule byte() -> u8
        = n:$(['0'..='9']+) {? n.parse().or(Err("valid u8")) }

    // checks for certain escape characters (todo, probably isn't a complete list)
    rule escape_char() -> char
        = "\\\"" { '"' }
        / "\\n" { '\n' }
        / "\\t" { '\t' }
        / "\\\0" { '\0' }
        / "\\u{" value:$(['0'..='9' | 'a'..='f' | 'A'..='F']+) "}" {?
              u32::from_str_radix(value, 16).ok().and_then(char::from_u32).ok_or("valid unicode code point")
          }
        / expected!("valid escape sequence")

    rule string_inner() -> String
        = c:escape_char() s:string_inner() {
            let mut x = c.to_string();
            x.push_str(&s);
            x
        }
        / c:[^'"'] s:string_inner() {
            let mut x = c.to_string();
            x.push_str(&s);
            x
        }
        / "" { String::new() }
}}

#[derive(Debug)]
pub enum Expr {
    Or(Vec<(Expr, WeightType)>),
    Concat(Vec<Expr>),
    Optional(Box<Expr>),
    Repetition(Box<Expr>, u32, u32),
    Reference(String),
    Literal(String),
    Regex(String),
    Bytes(Vec<u8>),
    Group(Box<Expr>),
}
