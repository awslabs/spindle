use itoa::Buffer as itoaBuffer;
use ryu::Buffer as ryuBuffer;
use std::str;

/// Defines state that is built during [`crate::Grammar::expression`].
///
/// This is implemented for
/// - `String` to produce string expressions
/// - `Vec<u8>` to produce byte sequences
/// - `u64` to produce equivalence class IDs of the traversal path. See [`crate::Grammar::how_many`] for more info.
///
/// You can implement this yourself, for example if you want to implement equivalence classes that
/// - ignore order
/// - ignore certain paths or transitions
/// - are more accurate
/// - care about characterics of the arbitrary data, such as if a string is ascii or not.
/// Or implement a visitor to build some structured state, such as a tree a collection of generated data.
pub trait Visitor {
    /// Instiates the visitor before traversal.
    fn new() -> Self;
    /// Visits the `X | Y` branch in the grammar and provides the `index`th path that was taken.
    fn visit_or(&mut self, _index: usize) {}
    /// Visits the `X Y` operation.
    fn visit_concat(&mut self) {}
    /// Visits `X?` and provides whether or not `X` will be evaluated.
    fn visit_optional(&mut self, _was_chosen: bool) {}
    /// Visits `X*`, `X+`, `X{k}`, or `X{min,max}` and provides how many repetitions were arbitrarily selected.
    fn visit_repetition(&mut self, _reps: usize) {}
    /// Visits a use/reference of a defined rule and provides the rule name and index/id.
    fn visit_reference(&mut self, _name: &str, _index: usize) {}
    /// Visits the literal `str`.
    fn visit_literal(&mut self, _s: &str) {}
    /// Visits the literal `&[u8]`.
    fn visit_bytes(&mut self, _val: &[u8]) {}
    /// Visits regex and provides the arbitrary regex that was generated.
    fn visit_regex(&mut self, _generated: &[u8]) {}
    /// Visits the `(X)` group.
    fn visit_group(&mut self) {}
    /// Visits `String` pre-defined rule and provides the generated arbitrary `str`.
    fn visit_str(&mut self, _s: &str) {}
    /// Visits `char` pre-defined rule and provides the generated arbitrary `char`.
    fn visit_char(&mut self, _c: char) {}
    /// Visits `f32` pre-defined rule and provides the generated arbitrary `f32`.
    fn visit_f32(&mut self, _f: f32) {}
    /// Visits `f64` pre-defined rule and provides the generated arbitrary `f64`.
    fn visit_f64(&mut self, _f: f64) {}
    /// Visits `u8` pre-defined rule and provides the generated arbitrary `u8`.
    fn visit_u8(&mut self, _num: u8) {}
    /// Visits `u16` pre-defined rule and provides the generated arbitrary `u16`.
    fn visit_u16(&mut self, _num: u16) {}
    /// Visits `u32` pre-defined rule and provides the generated arbitrary `u32`.
    fn visit_u32(&mut self, _num: u32) {}
    /// Visits `u64` pre-defined rule and provides the generated arbitrary `u64`.
    fn visit_u64(&mut self, _num: u64) {}
    /// Visits `u128` pre-defined rule and provides the generated arbitrary `u128`.
    fn visit_u128(&mut self, _num: u128) {}
    /// Visits `usize` pre-defined rule and provides the generated arbitrary `usize`.
    fn visit_usize(&mut self, _num: usize) {}
    /// Visits `i8` pre-defined rule and provides the generated arbitrary `i8`.
    fn visit_i8(&mut self, _num: i8) {}
    /// Visits `i16` pre-defined rule and provides the generated arbitrary `i16`.
    fn visit_i16(&mut self, _num: i16) {}
    /// Visits `i32` pre-defined rule and provides the generated arbitrary `i32`.
    fn visit_i32(&mut self, _num: i32) {}
    /// Visits `i64` pre-defined rule and provides the generated arbitrary `i64`.
    fn visit_i64(&mut self, _num: i64) {}
    /// Visits `i128` pre-defined rule and provides the generated arbitrary `i128`.
    fn visit_i128(&mut self, _num: i128) {}
    /// Visits `isize` pre-defined rule and provides the generated arbitrary `isize`.
    fn visit_isize(&mut self, _num: isize) {}
}

macro_rules! impl_visit_num_for_vec {
    ($($fn_name:ident = $type:ident = $buf_type:ident),* $(,)*) => (
        $(
            fn $fn_name(&mut self, num: $type) {
                self.extend($buf_type::new().format(num).as_bytes());
            }
        )*
    )
}

/// Returns an arbitrary byte sequence matching the grammar.
impl Visitor for Vec<u8> {
    fn new() -> Self {
        Default::default()
    }
    fn visit_literal(&mut self, val: &str) {
        self.extend(val.as_bytes());
    }
    fn visit_bytes(&mut self, val: &[u8]) {
        self.extend(val);
    }
    fn visit_regex(&mut self, regex_result: &[u8]) {
        self.extend(regex_result);
    }
    impl_visit_num_for_vec!(
        visit_u8 = u8 = itoaBuffer,
        visit_u16 = u16 = itoaBuffer,
        visit_u32 = u32 = itoaBuffer,
        visit_u64 = u64 = itoaBuffer,
        visit_u128 = u128 = itoaBuffer,
        visit_usize = usize = itoaBuffer,
        visit_i8 = i8 = itoaBuffer,
        visit_i16 = i16 = itoaBuffer,
        visit_i32 = i32 = itoaBuffer,
        visit_i64 = i64 = itoaBuffer,
        visit_i128 = i128 = itoaBuffer,
        visit_isize = isize = itoaBuffer,
        visit_f32 = f32 = ryuBuffer,
        visit_f64 = f64 = ryuBuffer,
    );
    fn visit_str(&mut self, s: &str) {
        self.extend(s.as_bytes())
    }
    fn visit_char(&mut self, c: char) {
        let mut b = [0; 4];
        let result = c.encode_utf8(&mut b);
        self.extend(result.as_bytes())
    }
}

macro_rules! impl_visit_num_for_string {
    ($($fn_name:ident = $type:ident = $buf_type:ident),* $(,)*) => (
        $(
            fn $fn_name(&mut self, num: $type) {
                self.push_str($buf_type::new().format(num));
            }
        )*
    )
}

/// Returns an arbitrary expression `String` matching the grammar.
///
/// # Panics
/// Panics if the regex or byte sequence evaluates to non-utf8. This
/// can be avoided by avoiding such regexes or non-utf8 bytes in the grammar.
impl Visitor for String {
    fn new() -> Self {
        Default::default()
    }
    fn visit_literal(&mut self, val: &str) {
        self.push_str(val);
    }
    fn visit_bytes(&mut self, val: &[u8]) {
        self.push_str(str::from_utf8(val).expect("utf8 bytes"));
    }
    fn visit_regex(&mut self, regex_result: &[u8]) {
        self.push_str(str::from_utf8(regex_result).expect("utf8 bytes"));
    }
    impl_visit_num_for_string!(
        visit_u8 = u8 = itoaBuffer,
        visit_u16 = u16 = itoaBuffer,
        visit_u32 = u32 = itoaBuffer,
        visit_u64 = u64 = itoaBuffer,
        visit_u128 = u128 = itoaBuffer,
        visit_usize = usize = itoaBuffer,
        visit_i8 = i8 = itoaBuffer,
        visit_i16 = i16 = itoaBuffer,
        visit_i32 = i32 = itoaBuffer,
        visit_i64 = i64 = itoaBuffer,
        visit_i128 = i128 = itoaBuffer,
        visit_isize = isize = itoaBuffer,
        visit_f32 = f32 = ryuBuffer,
        visit_f64 = f64 = ryuBuffer,
    );
    fn visit_str(&mut self, s: &str) {
        self.push_str(s)
    }
    fn visit_char(&mut self, c: char) {
        self.push(c)
    }
}

fn id_hash(val: &mut u64, rule_id: u64) {
    *val = fxhash::hash64(&(rule_id, *val));
}

/// Returns an identifier of the path taken during the traversal.
impl Visitor for u64 {
    // TODO: maybe a struct(s) that capture different traversal patterns?
    // ```ignore
    // OrderedClass(u64);
    // Unordered(u64);
    // IncludeLiterals(u64);
    // ```

    fn new() -> Self {
        u64::MAX
    }
    fn visit_or(&mut self, index: usize) {
        id_hash(self, fxhash::hash64(&(0, index as u64)))
    }
    fn visit_concat(&mut self) {
        id_hash(self, 1)
    }
    fn visit_optional(&mut self, was_chosen: bool) {
        id_hash(self, fxhash::hash64(&(2, was_chosen as u64)))
    }
    fn visit_reference(&mut self, _: &str, index: usize) {
        id_hash(self, fxhash::hash64(&(3, index as u64)))
    }
    fn visit_repetition(&mut self, reps: usize) {
        id_hash(self, fxhash::hash64(&(4, reps as u64)))
    }
    fn visit_literal(&mut self, _: &str) {
        id_hash(self, 5)
    }
    fn visit_bytes(&mut self, _: &[u8]) {
        id_hash(self, 6)
    }
    fn visit_regex(&mut self, _: &[u8]) {
        id_hash(self, 7)
    }
    fn visit_group(&mut self) {
        id_hash(self, 8)
    }
}

// Code is adapted from:
// <https://doc.rust-lang.org/src/core/tuple.rs.html#10>
// <https://doc.rust-lang.org/src/core/hash/mod.rs.html#879>
macro_rules! impl_visitor_tuple {
    () => (
        impl Visitor for () {
            #[inline]
            fn new() {}
        }
    );

    ( $($name:ident)+) => (
        #[allow(non_snake_case)]
        impl<$($name: Visitor),+> Visitor for ($($name,)+) {
            fn new() -> ($($name,)+) {
                ($({ let x: $name = Visitor::new(); x},)+)
            }

            fn visit_or(&mut self, index: usize) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_or(index);)+
            }
            fn visit_concat(&mut self) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_concat();)+
            }
            fn visit_optional(&mut self, b: bool) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_optional(b);)+
            }
            fn visit_repetition(&mut self, reps: usize) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_repetition(reps);)+
            }
            fn visit_reference(&mut self, name: &str, index: usize) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_reference(name, index);)+
            }
            fn visit_literal(&mut self, val: &str) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_literal(val);)+
            }
            fn visit_bytes(&mut self, val: &[u8]) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_bytes(val);)+
            }
            fn visit_regex(&mut self, val: &[u8]) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_regex(val);)+
            }
            fn visit_group(&mut self) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_group();)+
            }
            fn visit_u16(&mut self, num: u16) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_u16(num);)+
            }
            fn visit_str(&mut self, s: &str) {
                let ($(ref mut $name,)+) = *self;
                $($name.visit_str(s);)+
            }
        }
    );
}

impl_visitor_tuple! {}
impl_visitor_tuple! { T }
impl_visitor_tuple! { T B }
impl_visitor_tuple! { T B C }
impl_visitor_tuple! { T B C D }
impl_visitor_tuple! { T B C D E }
impl_visitor_tuple! { T B C D E F }
impl_visitor_tuple! { T B C D E F G }
impl_visitor_tuple! { T B C D E F G H }
impl_visitor_tuple! { T B C D E F G H I }
impl_visitor_tuple! { T B C D E F G H I J }
impl_visitor_tuple! { T B C D E F G H I J K }
impl_visitor_tuple! { T B C D E F G H I J K L }
