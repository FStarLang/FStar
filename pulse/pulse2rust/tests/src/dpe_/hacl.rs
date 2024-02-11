pub type hashable_len = usize;
pub type signable_len = usize;

pub fn ed25519_verify(
    pubk: &mut [u8],
    hdr: &mut [u8],
    hdr_len: signable_len,
    sig: &mut [u8],
    ppubk: (),
    phdr: (),
    psig: (),
    pubk_seq: (),
    hdr_seq: (),
    sig_seq: (),
) -> bool {
    panic!()
}

pub const dice_digest_len: usize = 32;

pub fn hacl_hash(
    alg: (),
    src_len: hashable_len,
    src: &mut [u8],
    dst: &mut [u8],
    psrc: (),
    src_seq: (),
    dst_seq: (),
) -> () {
    panic!()
}

pub const dice_hash_alg: () = ();

pub fn hacl_hmac(
    alg: (),
    dst: &mut [u8],
    key: &mut [u8],
    key_len: hashable_len,
    msg: &mut [u8],
    msg_len: hashable_len,
    pkey: (),
    pmsg: (),
    dst_seq: (),
    key_seq: (),
    msg_seq: (),
) -> () {
    panic!()
}
