pub const sign : fn (
        signature: *mut u8,
        private_key: *mut u8,
        msg_len: u32,
        msg: *mut u8,
    )
= super::evercrypt::EverCrypt_Ed25519_sign;

pub const verify : fn (
        public_key: *mut u8,
        msg_len: u32,
        msg: *mut u8,
        signature: *mut u8,
    ) -> bool
= super::evercrypt::EverCrypt_Ed25519_verify;
