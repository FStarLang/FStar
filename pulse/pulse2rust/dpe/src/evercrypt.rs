use once_cell::sync::Lazy;
pub static EVERCRYPT: Lazy<super::evercrypt_gen::evercrypt> =
    Lazy::new(|| unsafe { super::evercrypt_gen::evercrypt::new("libevercrypt.so").unwrap() });
