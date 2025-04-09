mod common;
use common::rand_u;
use spindle_lib::Grammar;

fn main() {
    let grammar: Grammar = r#"
        json     : "{" children "}" ;
        children : keyval | keyval ", " children ;
        keyval   : key ": " val ;
        key      : json_string ;
        val      : json | list | json_string ;
        list     : "[" elements "]" ;
        elements : val | val ", " elements ;
        json_string : "\"" r"[a-zA-Z_0-9]+" "\"";
    "#
    .parse()
    .unwrap();

    loop {
        let mut buf = [0; 4096];
        let mut u = rand_u(&mut buf);
        if let Ok(s) = grammar.expression::<String>(&mut u, Some(100)) {
            println!("{}", s);
            break;
        }
    }
}
