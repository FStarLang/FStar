pub use super::evercrypt::EverCrypt_HMAC_is_supported_alg as is_supported_alg;

pub fn compute (
  a: super::evercrypt::Spec_Hash_Definitions_hash_alg,
  tag: &mut [u8],
  key: &mut [u8],
  p_key: (),
  v_key: (),
  keylen: u32,
  data: &mut [u8],
  p_data: (),
  v_data: (),
  datalen: u32
) {
  super::evercrypt::EverCrypt_HMAC_compute(a, tag.as_mut_ptr(), key.as_mut_ptr(), keylen, data.as_mut_ptr(), datalen);
}
