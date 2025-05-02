# Spindle
[![Crates.io](https://img.shields.io/crates/v/spindle-lib.svg)](https://crates.io/crates/spindle-lib)
[![docs.rs](https://docs.rs/spindle-lib/badge.svg)](https://docs.rs/spindle-lib)
[![License: APACHE](https://img.shields.io/badge/License-Apache-blue.svg)](https://github.com/awslabs/spindle/blob/main/LICENSE)
![Downloads](https://img.shields.io/crates/d/spindle-lib)

Spindle is a simple and efficient expression and byte sequence generator to aid fuzz testing parsers and de-serializers. Spindle spins raw, untyped byte buffers into structured data.

## Overview
Spindle's syntax, similar to [Extended Backus–Naur form](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form), lets users define the structure of generated data. This syntax compiles to `Grammar`, a state machine that can be arbitrarily traversed to produce structure-aware, matching expressions.

Spindle works with fuzzers such as [cargo-fuzz](https://crates.io/crates/cargo-fuzz) or [AFL](https://crates.io/crates/afl) because it is an extension of [arbitrary](https://crates.io/crates/arbitrary); the traversal of the state machine is deterministically dependent on [`Unstructured`](https://docs.rs/arbitrary/latest/arbitrary/struct.Unstructured.html).

Spindle is particularily useful for generating semi-correct and interesting inputs that attack edge cases of parsers and de-serializers, such as mixing familar tokens in incorrect places or sprinkling in Unicode characters.

Spindle is developed and leveraged by AWS to fuzz test the parsers and de-serializers in their backend systems.

## Examples
**For more examples, see the [examples](https://github.com/awslabs/spindle/tree/main/examples) folder.**

```rust
use spindle_lib::Grammar;
use arbitrary::Unstructured;

let math: Grammar = r#"
    expr   : u16 | paren | expr symbol expr ;
    paren  : "(" expr symbol expr ")" ;
    symbol : r"-|\+|\*|÷" ;
"#.parse().unwrap();

let mut u = Unstructured::new(b"poiuytasdbvcxeygrey");
let sentence: String = math.expression(&mut u, None).unwrap();
// (21359*39933))+13082-62216
```
The state machine traversal always starts at the first rule. In the example, 
- `expr` is the first rule and evaluates to either `u16`, `paren`, or the concatenation of `expr` and `symbol` and `expr`.
- `;` delimits different rules.
- `u16` is a pre-defined data types that directly evaluates to `u16::arbitrary(u)`.
- `paren` evaluates to the concatenation of the literal `"("`, `expr`, `symbol`, `expr` and, `")"`.
- `symbol` evaluates to the an arbitrary string matching the regex `-|\+|\*|÷`.

### Semi-Correct Expression
This grammar is similar to the well formed math expression grammar, but sometimes includes an extra closing parenthesis and/or an arbitrary symbol.

```rust
use spindle_lib::Grammar;
use arbitrary::Unstructured;

let math: Grammar = r#"
    expr   : u16 | paren | expr symbol expr ;
    paren  : "(" expr symbol expr ")" ")"? ;
    symbol : r"-|\+|\*|÷" | String ;
"#.parse().unwrap();

let mut u = Unstructured::new(b"poiuytasdbvcxeygrey");
let sentence: String = math.expression(&mut u, None).unwrap();
// (44637*32200)Ѱ'x124928390-27338)
```

### Usage in Fuzzer
```rust,ignore
use spindle_lib::Grammar;
use libfuzzer_sys::fuzz_target;
use arbitrary::{Arbitrary, Result, Unstructured};
use std::sync::LazyLock;

static GRAMMAR: LazyLock<Grammar> = LazyLock::new(|| {
    r#"
        expr   : u16 | paren | expr symbol expr ;
        paren  : "(" expr symbol expr ")" ;
        symbol : r"-|\+|\*|÷" ;
    "#.parse().unwrap()
});

struct MathExpression(String);

impl<'a> Arbitrary<'a> for MathExpression {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self(GRAMMAR.expression(u, None)?.0))
    }
}

fuzz_target!(|expr: MathExpression| {
    // ... my_parser(expr);
});
```

## Pre-defined Rules
- `String` evaluates to `str::arbitrary(u)`
- `u16` evaluates to `u16::arbitrary(u)`

## Visitor
A `Visitor` is some state that is initialized before traversal and mutated as different rules are visited during the traversal, e.g. `visit_or`. Vistors that are already implemented are `String` and `Vec<u8>` for output buffers, and `u64` for classification. 

Users can use their own implementation of `Visitor`, for example if they want to 
- use a different output buffer
- use a different classification
- gather data
- build an abstract syntax tree

### Example
```rust
use spindle_lib::{Grammar, Visitor};

let math: Grammar = r#"
    expr   : u16 | paren | expr symbol expr ;
    paren  : "(" expr symbol expr ")" ;
    symbol : r"-|\+|\*|÷" ;
"#.parse().unwrap();

/// Detects if any prime numbers were generated.
#[derive(Debug, Default)]
struct PrimeDetector(bool);

impl Visitor for PrimeDetector {
    fn new() -> Self {
        Self::default()
    }

    fn visit_u16(&mut self, num: u16) {
        let num_is_prime = (2..num).all(|a| num % a != 0);
        self.0 |= num_is_prime;
    }
}

let mut u = arbitrary::Unstructured::new(b"qwerty");
let (expr, any_primes): (String, PrimeDetector) = math.expression(&mut u, None).unwrap();
let expr: String = math.expression(&mut u, None).unwrap();
assert!(any_primes.0);
```

## Example
In this example, a math specific abstract syntax tree (AST) is built during the arbitrary traversal.

```rust
use spindle_lib::{Grammar, Visitor};

let math: Grammar = r#"
    expr   : u16 | paren | expr symbol expr ;
    paren  : "(" expr symbol expr ")" ;
    symbol : r"-|\+|\*|÷" ;
"#.parse().unwrap();

#[derive(Debug, Default)]
struct MathAst {
    cur_op: Option<char>,
    stack: Vec<MathAstNode>,
}

#[derive(Debug)]
enum MathAstNode {
    Num(u16),
    Expr(Box<MathAstNode>, char, Box<MathAstNode>)
}

impl Visitor for MathAst {
    fn new() -> Self {
        Self::default()
    }

    fn visit_regex(&mut self, regex_output: &[u8]) {
        assert_eq!(regex_output.len(), 1);
        let c = regex_output[0] as char;
        self.cur_op = Some(c);
    }

    fn visit_u16(&mut self, num: u16) {
        match self.cur_op {
            None => self.stack.push(MathAstNode::Num(num)),
            Some(symbol) => {
                let left = Box::new(self.stack.pop().unwrap());
                let right = Box::new(MathAstNode::Num(num));
                let new = MathAstNode::Expr(left, symbol, right);
                self.stack.push(new);
                self.cur_op = None;
            }
        }
    }
}

let mut u = arbitrary::Unstructured::new(b"494392");
// MathAst { cur_op: None, stack: [Expr(Num(13108), '*', Num(0))] }
let tree: MathAst = math.expression(&mut u, None).unwrap();
```