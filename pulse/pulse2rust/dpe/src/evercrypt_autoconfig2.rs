use super::evercrypt::EVERCRYPT;

pub fn init(_: ()) {
    unsafe {
        EVERCRYPT.EverCrypt_AutoConfig2_init();
    }
}
