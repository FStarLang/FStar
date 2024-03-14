pub use super::evercrypt::EverCrypt_Hash_Incremental_hash_len as hash_len;

pub fn hash (
  a: super::evercrypt::Spec_Hash_Definitions_hash_alg,
  output: &mut [u8],
  input: &mut [u8],
  p_input: (),
  v_input: (),
  input_len: u32
) {
  super::evercrypt::EverCrypt_Hash_Incremental_hash(a, output.as_mut_ptr(), input.as_mut_ptr(), input_len);
}
