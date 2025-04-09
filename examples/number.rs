mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    // grammar for generating semi-correct numbers
    // designed to potentially confuse a big number parser.
    let grammar: Grammar = r#"
        big_number : sign? prefix E? sign? exponent? ;
        E          : "E" | "e" ;
        sign       : "+" | "-" ;
        prefix     : number | String ;
        exponent   : number ;
        number     : ("."? digits "."?)* ; 
        digits     : r"[0-9]*" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, Some(10)).unwrap();
    println!("{:?}", sentence);
}
