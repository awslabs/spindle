mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    let grammar: Grammar = r#"
        expr   : num | paren | expr symbol expr ;
        paren  : "(" expr symbol expr ")" ;
        symbol : r"-|\+|\*|÷" ;
        num    : r"[0-9]+" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, Some(5)).unwrap();
    println!("{}", sentence);

    // This grammar is similar to the well formed math expression grammar,
    // but sometimes includes an extra closing parenthesis and/or an arbitrary symbol.
    let grammar: Grammar = r#"
        expr   : num | paren | expr symbol expr ;
        paren  : "(" expr symbol expr ")" ")"? ;
        symbol : r"-|\+|\*|÷" | String;
        num    : r"[0-9]+" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, Some(5)).unwrap();
    println!("{}", sentence);
}
