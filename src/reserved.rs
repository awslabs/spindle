use crate::error::ErrorRepr;
use crate::Visitor;
use arbitrary::{Arbitrary, Result, Unstructured};
use std::str::FromStr;
use std::sync::LazyLock;

/// Illegal attribute names in a grammar.
/// Currently these are just the names of the pre-defined types, e.g. `u16`, `String`
static RESERVED_KEYWORDS_SET: LazyLock<Vec<String>> = LazyLock::new(|| {
    Predefined::all()
        .map(|s| s.as_str().to_ascii_lowercase())
        .collect()
});

fn is_reserved_keyword(attr: &str) -> bool {
    let lower = attr.to_ascii_lowercase();
    RESERVED_KEYWORDS_SET.contains(&lower)
}

/// Returns the list of all Strings in `attrs` that are reserved.
/// It's called once per grammar parse.
pub(crate) fn filter_reserved_keywords(attrs: &[String]) -> Option<Vec<String>> {
    let r: Vec<_> = attrs
        .iter()
        .filter(|arg0: &&String| is_reserved_keyword(arg0))
        .cloned()
        .collect();
    (!r.is_empty()).then_some(r)
}

/// Fundemental datatypes that implement `Arbitrary` and evaluate to that implementation.
#[derive(Debug, PartialEq, Eq, enum_iterator::Sequence)]
#[allow(non_camel_case_types)]
pub(crate) enum Predefined {
    String,
    char,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    f32,
    f64,
}

impl Predefined {
    pub(crate) fn visit<V: Visitor>(&self, v: &mut V, u: &mut Unstructured<'_>) -> Result<()> {
        match self {
            Self::String => v.visit_str(<&str as Arbitrary>::arbitrary(u)?),
            Self::char => v.visit_char(char::arbitrary(u)?),
            Self::u8 => v.visit_u8(u8::arbitrary(u)?),
            Self::u16 => v.visit_u16(u16::arbitrary(u)?),
            Self::u32 => v.visit_u32(u32::arbitrary(u)?),
            Self::u64 => v.visit_u64(u64::arbitrary(u)?),
            Self::u128 => v.visit_u128(u128::arbitrary(u)?),
            Self::usize => v.visit_usize(usize::arbitrary(u)?),
            Self::i8 => v.visit_i8(i8::arbitrary(u)?),
            Self::i16 => v.visit_i16(i16::arbitrary(u)?),
            Self::i32 => v.visit_i32(i32::arbitrary(u)?),
            Self::i64 => v.visit_i64(i64::arbitrary(u)?),
            Self::i128 => v.visit_i128(i128::arbitrary(u)?),
            Self::isize => v.visit_isize(isize::arbitrary(u)?),
            Self::f32 => v.visit_f32(f32::arbitrary(u)?),
            Self::f64 => v.visit_f64(f64::arbitrary(u)?),
        }
        Ok(())
    }

    pub(crate) fn all() -> impl Iterator<Item = Self> {
        enum_iterator::all::<Self>()
    }

    pub(crate) const fn as_str(&self) -> &'static str {
        match self {
            Self::String => "String",
            Self::char => "char",
            Self::u8 => "u8",
            Self::u16 => "u16",
            Self::u32 => "u32",
            Self::u64 => "u64",
            Self::u128 => "u128",
            Self::usize => "usize",
            Self::i8 => "i8",
            Self::i16 => "i16",
            Self::i32 => "i32",
            Self::i64 => "i64",
            Self::i128 => "i128",
            Self::isize => "isize",
            Self::f32 => "f32",
            Self::f64 => "f64",
        }
    }
}

impl FromStr for Predefined {
    type Err = ErrorRepr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "String" => Ok(Self::String),
            "char" => Ok(Self::char),
            "u8" => Ok(Self::u8),
            "u16" => Ok(Self::u16),
            "u32" => Ok(Self::u32),
            "u64" => Ok(Self::u64),
            "u128" => Ok(Self::u128),
            "usize" => Ok(Self::usize),
            "i8" => Ok(Self::i8),
            "i16" => Ok(Self::i16),
            "i32" => Ok(Self::i32),
            "i64" => Ok(Self::i64),
            "i128" => Ok(Self::i128),
            "isize" => Ok(Self::isize),
            "f32" => Ok(Self::f32),
            "f64" => Ok(Self::f64),
            _ => Err(ErrorRepr::UnkownVar(String::from(s))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grammar;
    use rand::{rngs::StdRng, RngCore, SeedableRng};

    #[test]
    fn str_conversions() {
        for p in Predefined::all() {
            assert_eq!(p, Predefined::from_str(p.as_str()).unwrap());
        }
    }

    macro_rules! test_integer {
        ($($fn_name:ident = $type:ident),* $(,)*) => (
            $(
                #[test]
                fn $fn_name() {
                    let s = format!("expr: {} ;", stringify!($type));
                    let grammar: Grammar = s.parse().unwrap();

                    let mut buf = [0u8; 64];
                    let mut rng = StdRng::seed_from_u64(42);

                    let mut min_gen = $type::MAX;
                    let mut max_gen = $type::MIN;

                    for _ in 0..1000 {
                        rng.fill_bytes(&mut buf);
                        let mut u = Unstructured::new(&buf);
                        let expr = grammar.expression::<String>(&mut u, None).unwrap();
                        // checks that generated numbers are not outside the bounds of MIN and MAX
                        let x = expr.parse::<$type>().unwrap();
                        min_gen = std::cmp::min(min_gen, x);
                        max_gen = std::cmp::max(max_gen, x);
                    }
                    // check that generated numbers pretty close to MIN and MAX
                    // e.g. `u64` isn't generating only `u8`s.

                    // compare the min and max generated numbers to the range of the space.
                    // Example:
                    // u16 half range is 32767. if u16 is generating u8s, then the largest `max_gen`
                    // is 255. 255 is not "close enough" to u16::MAX because 32767 > (65535 - 255) is not true.
                    // it is unlikely that u16's generates all 1000 numbers less than 255.
                    // Visualizaiton:
                    // [0    u8::MAX       u16::MAX]
                    //                ^ `max_gen` should land somewhere here
                    let half_range = ($type::MAX / 2) -  ($type::MIN / 2);
                    let min_diff = min_gen - $type::MIN;
                    let max_diff = $type::MAX - max_gen;
                    // 64 is arbitrary and tightens the validation a bit.
                    assert!(half_range / 64 > max_diff);
                    assert!(half_range / 64 > min_diff);
                }
            )*
        )
    }

    test_integer!(
        test_u8 = u8,
        test_u16 = u16,
        test_u32 = u32,
        test_u64 = u64,
        test_u128 = u128,
        test_usize = usize,
        test_i8 = i8,
        test_i16 = i16,
        test_i32 = i32,
        test_i64 = i64,
        test_i128 = i128,
        test_isize = isize,
    );

    #[test]
    fn test_char() {
        let grammar: Grammar = "expr: char ;".parse().unwrap();

        let mut buf = [0u8; 64];
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..1000 {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            let expr = grammar.expression::<String>(&mut u, None).unwrap();
            assert_eq!(1, expr.chars().count());
            assert!(expr.parse::<char>().is_ok());
        }
    }

    #[test]
    fn test_f32() {
        let grammar: Grammar = "expr: f32 ;".parse().unwrap();

        let mut buf = [0u8; 64];
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..1000 {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            let expr = grammar.expression::<String>(&mut u, None).unwrap();
            assert!(expr.parse::<f32>().is_ok());
        }
    }

    #[test]
    fn test_f64() {
        let grammar: Grammar = "expr: f64 ;".parse().unwrap();

        let mut buf = [0u8; 64];
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..1000 {
            rng.fill_bytes(&mut buf);
            let mut u = Unstructured::new(&buf);
            let expr = grammar.expression::<String>(&mut u, None).unwrap();
            assert!(expr.parse::<f64>().is_ok());
        }
    }
}
