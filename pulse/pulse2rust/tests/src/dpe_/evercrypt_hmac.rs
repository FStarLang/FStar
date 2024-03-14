pub fn is_supported_alg (
  a: super::evercrypt::Spec_Hash_Definitions_hash_alg,
) -> bool { unsafe {
 return super::evercrypt::EverCrypt_HMAC_is_supported_alg(a);
}}

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
) { unsafe {
  super::evercrypt::EverCrypt_HMAC_compute(a, tag.as_mut_ptr(), key.as_mut_ptr(), keylen, data.as_mut_ptr(), datalen);
}}
