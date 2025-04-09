mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    // a grammar that produces random grammars
    let grammar: Grammar = r#"
        grammar   : (rule)+ ;
        rule      : name " : " rule_or " ;\n" ;
        rule_or : rule_concat | rule_concat " | " rule_or ;
        rule_concat : rule_repeat | rule_repeat " " rule_concat ;
        rule_repeat : terminal | terminal "?" | "(" terminal ")" ("*" | "+") ;
        terminal    : literal ;
        literal     : "\"" r"[a-z]+" "\"" ;
        name: r"[a-z]+" ;
    "#
    .parse()
    .unwrap();

    let mut buf = [0; 4096];
    let mut u = rand_u(&mut buf);
    let sentence: String = grammar.expression(&mut u, None).unwrap();
    println!("Grammar:\n{}", sentence);

    let g: Grammar = sentence.parse().unwrap();
    println!("Generated sentences:");
    for _ in 0..10 {
        let mut buf = [0; 4096];
        let mut u = rand_u(&mut buf);
        let sentence: String = g.expression(&mut u, None).unwrap();
        println!("{}", sentence);
    }
}
