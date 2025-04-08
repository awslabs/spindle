Spindle is a simple and efficient expression and byte sequence generator to aid fuzz testing parsers and de-serializers.

# Usage
Spindle offers a syntax similar to [Extended Backus–Naur form](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form) which compiles to a state machine --`Grammar`--that produces structured matching arbitrary sentences from an unstructured feed of bytes.

Spindle integrates with [libfuzzer](https://llvm.org/docs/LibFuzzer.html) and [cargo-fuzz](https://crates.io/crates/cargo-fuzz): Unstructured bytes, from the [arbitrary](https://crates.io/crates/arbitrary) crate, are manipulated by the fuzzer based on code coverage.

Spindle can be used to generate database expressions, big decimal strings, JSON, and other syntaxes, as well as slightly malformed variants of correct expressions to test interesting edge cases of parser or de-serializer.

# Example
```rust
use spindle_lib::Grammar;
use arbitrary::Unstructured;

let math: Grammar = r#"
    expr   : u16 | paren | expr symbol expr ;
    paren  : "(" expr symbol expr ")" ;
    symbol : r"-|\+|\*|÷" ;
"#.parse().unwrap();

let mut u = Unstructured::new(b"poiuyt5r4321sdnlknasdbvcxeygrey");
let sentence: String = math.expression(&mut u, None).unwrap(); // (30057+(12594+((((25976+(0*0))*0*0)*0)*0)*0*0))
```
The state machine traversal always starts at the first rule. In the example, 
- `expr` is the first rule and evaluates to either `u16`, `paren`, or the concatenation of `expr` and `symbol` and `expr`.
- `;` delimits different rules.
- `u16` is a pre-defined data types that directly evaluates to `u16::arbitrary(u)`
- `paren` evaluates to the concatenation of the literal `"("`, `expr`, `symbol`, `expr` and, `")"`.
- `symbol` evaluates to the an arbitrary string matching the regex `-|\+|\*|÷`.

## Usage in Fuzzer
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

For more examples, see the `examples` folder.

# Pre-defined Rules
- `String` evaluates to `str::arbitrary(u)`
- `u16` evaluates to `u16::arbitrary(u)`

# Visitor
A `Visitor` is some state that is initialized before traversal and mutated as different rules are visited during the traversal, e.g. `visit_or`. Vistors that are already implemented are `String` and `Vec<u8>` for output buffers, and `u64` for classification. 

Users can use their own implementation of `Visitor`, for example if they want to 
- use a different output buffer
- use a different classification
- gather data
- build an abstract syntax tree

## Example
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