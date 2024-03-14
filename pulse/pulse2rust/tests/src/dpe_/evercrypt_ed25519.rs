pub fn sign (
    signature: *mut u8,
    p_private_key: (),
    v_private_key: (),
    private_key: *mut u8,
    msg_len: u32,
    p_msg: (),
    v_msg: (),
    msg: *mut u8
) {
  super::evercrypt::EverCrypt_Ed25519_sign(signature, private_key, msg_len, msg);
}

pub fn verify (
    p_public_key: (),
    v_public_key: (),
    public_key: *mut u8,
    msg_len: u32,
    p_msg: (),
    v_msg: (),
    msg: *mut u8,
    p_signature: (),
    v_signature: (),
    signature: *mut u8
) -> bool {
  return super::evercrypt::EverCrypt_Ed25519_verify(public_key, msg_len, msg, signature);
}
