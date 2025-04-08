mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    let grammar: Grammar = r#"
        regex_string : "\"" r"[a-zA-Z_0-9]+" "\"" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, Some(10)).unwrap();
    println!("{}", sentence);
}
