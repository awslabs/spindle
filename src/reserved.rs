use crate::Visitor;
use arbitrary::{Arbitrary, Result, Unstructured};
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
#[derive(Debug, enum_iterator::Sequence)]
#[allow(non_camel_case_types)]
pub(crate) enum Predefined {
    /// Reference to an arbitrary `String`.
    String,
    /// Reference to an arbitrary `u16`.
    u16,
}

impl Predefined {
    pub(crate) fn visit<V: Visitor>(&self, v: &mut V, u: &mut Unstructured<'_>) -> Result<()> {
        match self {
            Self::u16 => {
                let x = u16::arbitrary(u)?;
                v.visit_u16(x);
            }
            Self::String => v.visit_str(<&str as Arbitrary>::arbitrary(u)?),
        }
        Ok(())
    }

    pub(crate) fn all() -> impl Iterator<Item = Self> {
        enum_iterator::all::<Self>()
    }

    pub(crate) const fn as_str(&self) -> &'static str {
        match self {
            Self::u16 => "u16",
            Self::String => "String",
        }
    }
}
