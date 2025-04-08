use arbitrary::Unstructured;
use rand::RngCore;

pub fn rand_u<'a>(buf: &'a mut [u8]) -> Unstructured<'a> {
    let mut rng = rand::rng();
    rng.fill_bytes(buf);
    Unstructured::new(buf)
}

#[allow(dead_code)]
fn main() {}
