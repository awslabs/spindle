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

let mut wool = Unstructured::new(b"poiuytasdbvcxeygrey");
let yarn: String = math.expression(&mut wool, None).unwrap();
// (21359*39933))+13082-62216
```
The state machine traversal always starts at the first rule. In the example, 
- `expr` is the first rule and evaluates to either `u16`, `paren`, or the concatenation of `expr` and `symbol` and `expr`.
- `;` delimits different rules.
- `u16` is a pre-defined rule that directly evaluates to `u16::arbitrary(u)`.
- `paren` evaluates to the concatenation of the literal `"("`, `expr`, `symbol`, `expr`, and `")"`.
- `symbol` evaluates to any arbitrary string that matches the regex `-|\+|\*|÷`.

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

let mut wool = Unstructured::new(b"poiuytasdbvcxeygrey");
let yarn: String = math.expression(&mut wool, None).unwrap();
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
        paren  : "(" expr symbol expr ")" ")"? ;
        symbol : r"-|\+|\*|÷" | String ;
    "#.parse().unwrap()
});

struct MathExpression(String);

impl<'a> Arbitrary<'a> for MathExpression {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Self(GRAMMAR.expression(u, None)?))
    }
}

fuzz_target!(|expr: MathExpression| {
    // ... my_parser(expr);
});
```
#### Samples
```text
6705d81051237=
♣69382149-12901+8851÷50*3993043534
(8198942155÷60177552446447)
(586643-96)*036074789
(8÷68){K2628
(5798))
(0868430}ݾ▼73)
0135259
(930-6*9502)
5045620÷91599
```

## Grammar Syntax
**For examples see [examples](https://github.com/awslabs/spindle/tree/main/examples).**

| Syntax      | Description |
| ----------- | ----------- |
| `rule : X ;` | Defines a rule with name "rule" with some pattern `X`. "rule" can be referenced in the same grammar, e.g. `another_rule : rule+ ;` |
| `X?`         | Evaluates to either `X` or nothing. |
| `X+`         | Evaluates to `X` 1 or more times (up to and including [`crate::MAX_REPEAT`]) |
| `X*`         | Evaluates to `X` 0 or more times (up to and including [`crate::MAX_REPEAT`]) |
| `X{k}`       | Evaluates to `X` exactly `k` times, where `k` is a `u32`. |
| `X{min,max}` | Evaluates `X` at least `min` times and at most (including) `max` times. `min` and `max` are `u32`. |
| `X \| Y`     | Evaluates to either `X` or `Y`. |
| `"X"`        | Literal value inside the quotes, e.g. `"foo"` |
| `[X]`        | Literal `Vec<u8>`, e.g. `[1, 2]`. |
| `r"X"`       | Arbitrarily evaluates the regex inside the quotes, e.g. `r"[A-Z]+"`. |
| `X Y`        | Evaluates to `X` and then `Y`. |
| `(X)`        | Groups the expression inside the parenthesis, e.g. `(X \| Y)+`. |
| `u16`, `String`, etc | A pre-defined type that evaluates to `T::arbitrary(u)`. [See more](https://docs.rs/arbitrary/1.4.1/arbitrary/trait.Arbitrary.html#foreign-impls). Supported pre-defined rules are `String`, `char`, `f32`, `f64`, and signed+unsigned integer types. |

## Visitor
A [`Visitor`] is state that is initialized before traversal and mutated as different rules are visited during the traversal, e.g. `visit_or`. Visitors that are already implemented are `String` and `Vec<u8>` for output buffers, and `u64` for classification.

Users can implement their own `Visitor` to
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

let mut wool = arbitrary::Unstructured::new(b"qwerty");
let (expr, any_primes): (String, PrimeDetector) = math.expression(&mut wool, None).unwrap();
let yarn: String = math.expression(&mut wool, None).unwrap();
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

let mut wool = arbitrary::Unstructured::new(b"494392");
// MathAst { cur_op: None, stack: [Expr(Num(13108), '*', Num(0))] }
let yarn: MathAst = math.expression(&mut wool, None).unwrap();
```