/* @flow */
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_UInt8 from "./FStar_UInt8";
import * as Hacl_Symmetric_Poly1305 from "./Hacl_Symmetric_Poly1305";
import * as FStar_Buffer from "./FStar_Buffer";
import * as FStar_Int8 from "./FStar_Int8";
import * as FStar_ST from "./FStar_ST";
import * as FStar_Int32 from "./FStar_Int32";
export const main = (uu____19: null): (FStar_Int32.t) => {
  let _res;
  FStar_ST.push_frame(null);
  const len = FStar_UInt32.uint_to_t(34);
  const keysize = FStar_UInt32.uint_to_t(32);
  const macsize = FStar_UInt32.uint_to_t(16);
  const mac = FStar_Buffer.create(FStar_UInt8.uint_to_t(0))(macsize);
  const plaintext = FStar_Buffer.createL([FStar_UInt8.uint_to_t(0x43)].concat([FStar_UInt8.uint_to_t(0x72)].concat([FStar_UInt8.uint_to_t(0x79)].concat([FStar_UInt8.uint_to_t(0x70)].concat([FStar_UInt8.uint_to_t(0x74)].concat([FStar_UInt8.uint_to_t(0x6f)].concat([FStar_UInt8.uint_to_t(0x67)].concat([FStar_UInt8.uint_to_t(0x72)].concat([FStar_UInt8.uint_to_t(0x61)].concat([FStar_UInt8.uint_to_t(0x70)].concat([FStar_UInt8.uint_to_t(0x68)].concat([FStar_UInt8.uint_to_t(0x69)].concat([FStar_UInt8.uint_to_t(0x63)].concat([FStar_UInt8.uint_to_t(0x20)].concat([FStar_UInt8.uint_to_t(0x46)].concat([FStar_UInt8.uint_to_t(0x6f)].concat([FStar_UInt8.uint_to_t(0x72)].concat([FStar_UInt8.uint_to_t(0x75)].concat([FStar_UInt8.uint_to_t(0x6d)].concat([FStar_UInt8.uint_to_t(0x20)].concat([FStar_UInt8.uint_to_t(0x52)].concat([FStar_UInt8.uint_to_t(0x65)].concat([FStar_UInt8.uint_to_t(0x73)].concat([FStar_UInt8.uint_to_t(0x65)].concat([FStar_UInt8.uint_to_t(0x61)].concat([FStar_UInt8.uint_to_t(0x72)].concat([FStar_UInt8.uint_to_t(0x63)].concat([FStar_UInt8.uint_to_t(0x68)].concat([FStar_UInt8.uint_to_t(0x20)].concat([FStar_UInt8.uint_to_t(0x47)].concat([FStar_UInt8.uint_to_t(0x72)].concat([FStar_UInt8.uint_to_t(0x6f)].concat([FStar_UInt8.uint_to_t(0x75)].concat([FStar_UInt8.uint_to_t(0x70)].concat([])))))))))))))))))))))))))))))))))));
  const expected = FStar_Buffer.createL([FStar_UInt8.uint_to_t(0xa8)].concat([FStar_UInt8.uint_to_t(0x06)].concat([FStar_UInt8.uint_to_t(0x1d)].concat([FStar_UInt8.uint_to_t(0xc1)].concat([FStar_UInt8.uint_to_t(0x30)].concat([FStar_UInt8.uint_to_t(0x51)].concat([FStar_UInt8.uint_to_t(0x36)].concat([FStar_UInt8.uint_to_t(0xc6)].concat([FStar_UInt8.uint_to_t(0xc2)].concat([FStar_UInt8.uint_to_t(0x2b)].concat([FStar_UInt8.uint_to_t(0x8b)].concat([FStar_UInt8.uint_to_t(0xaf)].concat([FStar_UInt8.uint_to_t(0x0c)].concat([FStar_UInt8.uint_to_t(0x01)].concat([FStar_UInt8.uint_to_t(0x27)].concat([FStar_UInt8.uint_to_t(0xa9)].concat([])))))))))))))))));
  const key = FStar_Buffer.createL([FStar_UInt8.uint_to_t(0x85)].concat([FStar_UInt8.uint_to_t(0xd6)].concat([FStar_UInt8.uint_to_t(0xbe)].concat([FStar_UInt8.uint_to_t(0x78)].concat([FStar_UInt8.uint_to_t(0x57)].concat([FStar_UInt8.uint_to_t(0x55)].concat([FStar_UInt8.uint_to_t(0x6d)].concat([FStar_UInt8.uint_to_t(0x33)].concat([FStar_UInt8.uint_to_t(0x7f)].concat([FStar_UInt8.uint_to_t(0x44)].concat([FStar_UInt8.uint_to_t(0x52)].concat([FStar_UInt8.uint_to_t(0xfe)].concat([FStar_UInt8.uint_to_t(0x42)].concat([FStar_UInt8.uint_to_t(0xd5)].concat([FStar_UInt8.uint_to_t(0x06)].concat([FStar_UInt8.uint_to_t(0xa8)].concat([FStar_UInt8.uint_to_t(0x01)].concat([FStar_UInt8.uint_to_t(0x03)].concat([FStar_UInt8.uint_to_t(0x80)].concat([FStar_UInt8.uint_to_t(0x8a)].concat([FStar_UInt8.uint_to_t(0xfb)].concat([FStar_UInt8.uint_to_t(0x0d)].concat([FStar_UInt8.uint_to_t(0xb2)].concat([FStar_UInt8.uint_to_t(0xfd)].concat([FStar_UInt8.uint_to_t(0x4a)].concat([FStar_UInt8.uint_to_t(0xbf)].concat([FStar_UInt8.uint_to_t(0xf6)].concat([FStar_UInt8.uint_to_t(0xaf)].concat([FStar_UInt8.uint_to_t(0x41)].concat([FStar_UInt8.uint_to_t(0x49)].concat([FStar_UInt8.uint_to_t(0xf5)].concat([FStar_UInt8.uint_to_t(0x1b)].concat([])))))))))))))))))))))))))))))))));
  Hacl_Symmetric_Poly1305.poly1305_mac(mac)(plaintext)(len)(key);
  const poly1305 = FStar_Buffer.createL([FStar_Int8.int_to_t(0)].concat([]));
  FStar_ST.pop_frame(null);
  _res = FStar_Int32.int_to_t(0);
  return _res;
};


