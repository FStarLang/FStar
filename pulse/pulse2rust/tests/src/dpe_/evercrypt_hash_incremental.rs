pub const hash_len : fn (uu___: super::evercrypt::Spec_Hash_Definitions_hash_alg) -> u32
= super::evercrypt::EverCrypt_Hash_Incremental_hash_len;

pub const hash : fn (
        a: Spec_Hash_Definitions_hash_alg,
        output: *mut u8,
        input: *mut u8,
        input_len: u32,
    )
= super::evercrypt::EverCrypt_Hash_Incremental_hash;
