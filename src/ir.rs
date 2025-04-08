//! Intermediary representation (ir) for a parsed grammar.

use peg::parser;

parser! {
/// This parser is not meant to efficient, since parsing the grammar is not meant to be
/// on the hot path (unlike generating expressions).
pub grammar bnf() for str {
    pub rule expr() -> Vec<(String, Expr)>
        = l:(definition() ++ _)

    rule definition() -> (String, Expr)
        = _ s:reference() _ ":" _ e:branch() _ ";" _ { (s, e) }

    rule branch() -> Expr
        = or()
        / branch_inner()

    rule branch_inner() -> Expr
        = _ x:concat() _ { x }
        / _ x:concat_inner() _ { x }

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
        = l:(branch_inner() **<2,64> "|") { Expr::Or(l) }

    rule rep() -> Expr
        = g:expression() _ "*" { Expr::Repetition(Box::new(g), 0) }
        / g:expression() _ "+" { Expr::Repetition(Box::new(g), 1) }

    rule choice() -> Expr
        = g:expression() _ "?" { Expr::Optional(Box::new(g)) }

    rule concat() -> Expr
        = l:(concat_inner() **<2,64> __) { Expr::Concat(l) }

    rule reference() -> String
        = s:$(['a'..='z' | 'A'..='Z' | '_' | '0'..='9']+) { s.to_string() }

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
    Or(Vec<Expr>),
    Concat(Vec<Expr>),
    Optional(Box<Expr>),
    Repetition(Box<Expr>, u32),
    Reference(String),
    Literal(String),
    Regex(String),
    Bytes(Vec<u8>),
    Group(Box<Expr>),
}
