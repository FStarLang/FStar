pub const is_supported_alg : fn (uu___: super::evercrypt::Spec_Hash_Definitions_hash_alg) -> bool
= super::evercrypt::EverCrypt_HMAC_is_supported_alg;

pub const compute : fn (
        a: super::evercrypt::Spec_Hash_Definitions_hash_alg,
        x0: *mut u8,
        x1: *mut u8,
        x2: u32,
        x3: *mut u8,
        x4: u32,
    )
= super::evercrypt::EverCrypt_HMAC_compute;
