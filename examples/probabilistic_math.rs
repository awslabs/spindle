mod common;
use spindle_lib::Grammar;

use crate::common::rand_u;

fn main() {
    // this grammar will generate more numbers than expressions
    let grammar: Grammar = r#"
        expr   : num                   @ 90
               | paren                 @ 5
               | expr symbol expr      @ 5  ;
        paren  : "(" expr symbol expr ")"   ;
        symbol : r"-|\+|\*|÷"               ;
        num    : r"[0-9]+"                  ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    for _ in 0..100 {
        let sentence: String = grammar.expression(&mut u, Some(10)).unwrap();
        println!("{}\n", sentence);
    }
}
