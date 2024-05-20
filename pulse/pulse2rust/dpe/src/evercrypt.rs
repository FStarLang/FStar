use super::generated::evercrypt_gen;
use once_cell::sync::Lazy;
pub static EVERCRYPT: Lazy<evercrypt_gen::evercrypt> =
    Lazy::new(|| unsafe { evercrypt_gen::evercrypt::new("libevercrypt.so").unwrap() });
