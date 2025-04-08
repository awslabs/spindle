use arbitrary::Unstructured;
use rand::RngCore;
use spindle_lib::Grammar;
use std::collections::HashSet;

fn rand_u<'a>(buf: &'a mut [u8]) -> Unstructured<'a> {
    let mut rng = rand::rng();
    rng.fill_bytes(buf);
    Unstructured::new(buf)
}

#[test]
fn is_determinsitic() {
    let grammar: Grammar = r#"
        expr   : num | paren | expr symbol expr ;
        paren  : "(" expr symbol expr ")" ;
        symbol : r"-|\+|\*|÷" ;
        num    : r"[0-9]+" ;
    "#
    .parse()
    .unwrap();

    let seed = b"qwertyqwertyqwertyqwertyqwertyqwerty";
    let mut u = Unstructured::new(seed);
    let (sentence_old, id_old): (String, u64) = grammar.expression(&mut u, None).unwrap();
    for _ in 0..100 {
        u = Unstructured::new(seed);
        let (sentence, id): (String, u64) = grammar.expression(&mut u, None).unwrap();
        assert_eq!(sentence, sentence_old);
        assert_eq!(id, id_old);
    }
}

#[test]
fn id_diff_for_diff_predefined() {
    let grammar: Grammar = "expr : u16 | String ;".parse().unwrap();
    let mut unique = HashSet::with_capacity(2);
    for _ in 0..100 {
        let mut buf = [0; 4096];
        let mut u = rand_u(&mut buf);
        let id: u64 = grammar.expression(&mut u, None).unwrap();
        unique.insert(id);
    }
    assert_eq!(unique.len(), 2);
}

#[test]
fn tuple_same_no_tuple() {
    let math: Grammar = r#"
        expr   : u16 | paren | expr symbol expr ;
        paren  : "(" expr symbol expr ")" ;
        symbol : r"-|\+|\*|÷" ;
    "#
    .parse()
    .unwrap();

    for _ in 0..100 {
        let mut buf = [0; 4096];
        let mut u = rand_u(&mut buf);
        let expr: (String, String) = math.expression(&mut u, None).unwrap();
        assert_eq!(expr.0, expr.1);
    }

    for _ in 0..100 {
        let mut buf = [0; 8];
        let _ = rand_u(&mut buf);
        let mut u1 = Unstructured::new(&buf);
        let mut u2 = Unstructured::new(&buf);
        let mut u3 = Unstructured::new(&buf);
        let mut u4 = Unstructured::new(&buf);
        let expr1: String = math.expression(&mut u1, None).unwrap();
        let id1: u64 = math.expression(&mut u2, None).unwrap();
        let (expr2, id2): (String, u64) = math.expression(&mut u3, None).unwrap();
        let (id3, expr3): (u64, String) = math.expression(&mut u4, None).unwrap();
        assert_eq!(expr1, expr2);
        assert_eq!(expr1, expr3);
        assert_eq!(id1, id2);
        assert_eq!(id1, id3);
    }
}
