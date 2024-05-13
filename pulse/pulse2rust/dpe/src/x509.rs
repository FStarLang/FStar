use super::l0types::*;

pub fn x509_get_deviceIDCRI(
    deviceIDCSR_ingredients: deviceIDCSR_ingredients_t,
    deviceID_pub: &mut [u8],
    pub_perm: (),
    deviceID_pub0: (),
) -> (deviceIDCSR_ingredients_t, deviceIDCRI_t) {
    panic!()
}

pub fn serialize_deviceIDCSR(
    deviceIDCRI_len: usize,
    deviceIDCSR: deviceIDCSR_t,
    deviceIDCSR_len: usize,
    deviceIDCSR_buf: &mut [u8],
    _buf: (),
) -> () {
    panic!()
}

pub fn x509_get_aliasKeyTBS(
    aliasKeyCRT_ingredients: aliasKeyCRT_ingredients_t,
    fwid: &mut [u8],
    deviceID_pub: &mut [u8],
    aliasKey_pub: &mut [u8],
    fwid_perm: (),
    deviceID_perm: (),
    aliasKey_perm: (),
    fwid0: (),
    deviceID0: (),
    aliasKey0: (),
) -> (aliasKeyCRT_ingredients_t, aliasKeyTBS_t) {
    panic!()
}

pub fn serialize_aliasKeyTBS(
    aliasKeyTBS: aliasKeyTBS_t,
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyTBS_buf0: (),
) -> () {
    panic!()
}

pub fn x509_get_aliasKeyCRT(
    aliasKeyTBS_len: usize,
    aliasKeyTBS_buf: &mut [u8],
    aliasKeyTBS_sig: &mut [u8],
    buf_perm: (),
    sig_perm: (),
    buf: (),
    sig: (),
) -> aliasKeyCRT_t {
    panic!()
}

pub fn serialize_aliasKeyCRT(
    aliasKeyTBS_len: usize,
    aliasKeyCRT: aliasKeyCRT_t,
    aliasKeyCRT_len: usize,
    aliasKeyCRT_buf: &mut [u8],
    _buf: (),
) -> () {
    panic!()
}

pub fn len_of_deviceIDCRI(x: deviceIDCSR_ingredients_t) -> (deviceIDCSR_ingredients_t, usize) {
    panic!()
}

pub fn len_of_aliasKeyTBS(x: aliasKeyCRT_ingredients_t) -> (aliasKeyCRT_ingredients_t, usize) {
    panic!()
}

pub fn length_of_deviceIDCSR(x: usize) -> usize {
    panic!()
}
pub fn length_of_aliasKeyCRT(x: usize) -> usize {
    panic!()
}

pub fn serialize_deviceIDCRI(
    deviceIDCRI: deviceIDCRI_t,
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCRI_buf0: (),
) -> () {
    panic!()
}

pub fn x509_get_deviceIDCSR(
    deviceIDCRI_len: usize,
    deviceIDCRI_buf: &mut [u8],
    deviceIDCRI_sig: &mut [u8],
    buf_perm: (),
    sig_perm: (),
    buf: (),
    sig: (),
) -> deviceIDCSR_t {
    panic!()
}
