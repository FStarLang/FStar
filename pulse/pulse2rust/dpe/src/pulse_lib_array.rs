pub fn compare(
    len: usize,
    a: &mut [u8],
    b: &mut [u8],
    p: (),
    a_seq: (),
    b_seq: (),
    __c0: (),
) -> bool {
    panic!()
}

pub fn memcpy<A: Copy>(l: usize, src: &mut [A], dst: &mut [A], p: (), src0: (), dst0: ()) -> () {
    dst.copy_from_slice(src);
}

pub fn zeroize(len: usize, src: &mut [u8], s: ()) -> () {
    panic!()
}
