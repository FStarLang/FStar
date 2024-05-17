use once_cell::sync::Lazy;
pub static L0: Lazy<super::l0core_gen::l0> =
    Lazy::new(|| unsafe { super::l0core_gen::l0::new("l0.so").unwrap() });

pub type deviceIDCSR_ingredients_t = super::l0core_gen::L0Core_deviceIDCSR_ingredients_t;
pub type aliasKeyCRT_ingredients_t = super::l0core_gen::L0Core_aliasKeyCRT_ingredients_t;

pub fn l0(
    cdi: &mut [u8],
    fwid: &mut [u8],
    deviceID_label_len: u32,
    deviceID_label: &mut [u8],
    aliasKey_label_len: u32,
    aliasKey_label: &mut [u8],
    deviceIDCSR_ingredients: super::l0core_gen::L0Core_deviceIDCSR_ingredients_t,
    aliasKeyCRT_ingredients: super::l0core_gen::L0Core_aliasKeyCRT_ingredients_t,
    deviceID_pub: &mut [u8],
    aliasKey_pub: &mut [u8],
    aliasKey_priv: &mut [u8],
    deviceIDCSR_len: u32,
    deviceIDCSR_buf: &mut [u8],
    aliasKeyCRT_len: u32,
    aliasKeyCRT_buf: &mut [u8],
    cdi_repr: (),
    fwid_repr: (),
    deviceID_label_repr: (),
    aliasKey_label_repr: (),
    deviceID_pub_repr: (),
    aliasKey_pub_repr: (),
    aliasKey_priv_repr: (),
    deviceIDCSR_buf_repr: (),
    aliasKeyCRT_buf_repr: (),
) {
    unsafe {
        L0.L0Core_l0(
            cdi.as_mut_ptr(),
            fwid.as_mut_ptr(),
            deviceID_label_len,
            deviceID_label.as_mut_ptr(),
            aliasKey_label_len,
            aliasKey_label.as_mut_ptr(),
            deviceIDCSR_ingredients,
            aliasKeyCRT_ingredients,
            deviceID_pub.as_mut_ptr(),
            aliasKey_pub.as_mut_ptr(),
            aliasKey_priv.as_mut_ptr(),
            deviceIDCSR_len,
            deviceIDCSR_buf.as_mut_ptr(),
            aliasKeyCRT_len,
            aliasKeyCRT_buf.as_mut_ptr(),
        )
    }
}
