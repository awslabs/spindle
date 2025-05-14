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

    for depth in 1..=16 {
        let how_many = grammar.how_many(Some(depth));
        let how_many_s = if let Some(x) = how_many {
            x.to_string()
        } else {
            String::from(">u64::MAX")
        };
        println!("{} possible traversals with depth {}", how_many_s, depth);
        if how_many.unwrap_or(u64::MAX) > 0 {
            let mut buf = [0; 4096];
            let mut u = rand_u(&mut buf);
            let expr = grammar.expression::<String>(&mut u, Some(depth)).unwrap();
            println!("example: {}\n", expr);
        }
    }
}
