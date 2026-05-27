use super::generated::evercrypt_gen;
use once_cell::sync::Lazy;
pub static EVERCRYPT: Lazy<evercrypt_gen::evercrypt> =
    Lazy::new(|| unsafe { evercrypt_gen::evercrypt::new("libevercrypt.so").unwrap() });

pub type Spec_Hash_Definitions_hash_alg = evercrypt_gen::Spec_Hash_Definitions_hash_alg;
