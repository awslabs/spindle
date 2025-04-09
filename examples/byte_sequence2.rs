mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    let grammar: Grammar = r#"
        bytes: as_string | as_regex ;
        as_regex: r"\\u{1}" ;
        as_string: "\u{2}\0" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, None).unwrap();
    println!("{}", sentence);
}
