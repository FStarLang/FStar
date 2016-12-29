/* @flow */
import * as FStar_ST from "./FStar_ST";
import * as FStar_Int_Cast from "./FStar_Int_Cast";
import * as Prims from "./Prims";
import * as FStar_Buffer from "./FStar_Buffer";
import * as Hacl_UInt64 from "./Hacl_UInt64";
import * as Hacl_UInt32 from "./Hacl_UInt32";
import * as Hacl_UInt8 from "./Hacl_UInt8";
import * as FStar_UInt64 from "./FStar_UInt64";
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_UInt8 from "./FStar_UInt8";
export type u8 = FStar_UInt8.t;

export type u32 = FStar_UInt32.t;

export type u64 = FStar_UInt64.t;

export type s8 = Hacl_UInt8.t;

export type s32 = Hacl_UInt32.t;

export type s64 = Hacl_UInt64.t;

export type h8 = Hacl_UInt8.t;

export type h32 = Hacl_UInt32.t;

export type h64 = Hacl_UInt64.t;

export type u8s = FStar_Buffer.buffer;

export type uint32_p = FStar_Buffer.buffer;

export const op_Greater_Greater_Greater = (a: h32): ((_1: u32) => (h32)) => ((s: u32) => (FStar_UInt32.logor(FStar_UInt32.shift_right(a)(s))(FStar_UInt32.shift_left(a)(FStar_UInt32.sub(FStar_UInt32.uint_to_t(32))(s)))));

export const op_Less_Less_Less = (a: h32): ((_1: u32) => (h32)) => ((s: u32) => (FStar_UInt32.logor(FStar_UInt32.shift_left(a)(s))(FStar_UInt32.shift_right(a)(FStar_UInt32.sub(FStar_UInt32.uint_to_t(32))(s)))));

export const lemma_euclidian_division = (r: number): ((_1: number) => ((_1: Prims.pos) => (null))) => ((b: number) => ((q: Prims.pos) => (null)));

export const lemma_uint32_of_bytes = (a: Hacl_UInt32.t): ((_1: Hacl_UInt32.t) => ((_1: Hacl_UInt32.t) => ((_1: Hacl_UInt32.t) => (null)))) => ((b: Hacl_UInt32.t) => ((c: Hacl_UInt32.t) => ((d: Hacl_UInt32.t) => (null))));

export const uint32_of_bytes = (b: u8s): (Hacl_UInt32.t) => {
  let _res;
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  _res = FStar_UInt32.add(FStar_UInt32.add(FStar_UInt32.add(FStar_Int_Cast.uint8_to_uint32(b0))(FStar_UInt32.shift_left(FStar_Int_Cast.uint8_to_uint32(b1))(FStar_UInt32.uint_to_t(8))))(FStar_UInt32.shift_left(FStar_Int_Cast.uint8_to_uint32(b2))(FStar_UInt32.uint_to_t(16))))(FStar_UInt32.shift_left(FStar_Int_Cast.uint8_to_uint32(b3))(FStar_UInt32.uint_to_t(24)));
  return _res;
};

export const bytes_of_uint32s = (output: u8s): ((_1: FStar_Buffer.buffer) => ((_1: u32) => (null))) => ((m: FStar_Buffer.buffer) => ((l: u32) => {
  let _res;
  const _0_172 = FStar_UInt32.gt(l)(FStar_UInt32.uint_to_t(0));
  if( (_0_172 == true) ) {
    const rem_ = FStar_UInt32.rem(l)(FStar_UInt32.uint_to_t(4));
    const _0_173 = FStar_UInt32.gt(rem_)(FStar_UInt32.uint_to_t(0));
    if( (_0_173 == true) ) {
      const _0_176 = l;
      {
        const l = FStar_UInt32.sub(_0_176)(rem_);
        const x = m[FStar_UInt32.div(l)(FStar_UInt32.uint_to_t(4))];
        const b0 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(x)(FStar_UInt32.uint_to_t(255)));
        output[l] = b0;
        const _0_174 = FStar_UInt32.gt(rem_)(FStar_UInt32.uint_to_t(1));
        if( (_0_174 == true) ) {
          const b1 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(8)))(FStar_UInt32.uint_to_t(255)));
          output[FStar_UInt32.add(l)(FStar_UInt32.uint_to_t(1))] = b1;
          const _0_175 = FStar_UInt32.gt(rem_)(FStar_UInt32.uint_to_t(2));
          if( (_0_175 == true) ) {
            const b2 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(16)))(FStar_UInt32.uint_to_t(255)));
            output[FStar_UInt32.add(l)(FStar_UInt32.uint_to_t(2))] = b2;
            null;
          } else {
            const uu____198 = _0_175;
            null;
          }
        } else {
          const uu____199 = _0_174;
          null;
        }
        _res = bytes_of_uint32s(output)(m)(l);
      }
    } else {
      const uu____202 = _0_173;
      const _0_177 = l;
      {
        const l = FStar_UInt32.sub(_0_177)(FStar_UInt32.uint_to_t(4));
        {
          const x = m[FStar_UInt32.div(l)(FStar_UInt32.uint_to_t(4))];
          {
            const b0 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(x)(FStar_UInt32.uint_to_t(255)));
            {
              const b1 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(8)))(FStar_UInt32.uint_to_t(255)));
              {
                const b2 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(16)))(FStar_UInt32.uint_to_t(255)));
                const b3 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(24)))(FStar_UInt32.uint_to_t(255)));
                output[l] = b0;
                output[FStar_UInt32.add(l)(FStar_UInt32.uint_to_t(1))] = b1;
                output[FStar_UInt32.add(l)(FStar_UInt32.uint_to_t(2))] = b2;
                output[FStar_UInt32.add(l)(FStar_UInt32.uint_to_t(3))] = b3;
                _res = bytes_of_uint32s(output)(m)(l);
              }
            }
          }
        }
      }
    }
  } else {
    const uu____221 = _0_172;
    _res = null;
  }
  return _res;
}));

export const bytes_of_uint32 = (output: u8s): ((_1: s32) => (null)) => ((x: s32) => {
  let _res;
  const mask = FStar_UInt32.uint_to_t(255);
  const b0 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(x)(mask));
  const b1 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(8)))(mask));
  const b2 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(16)))(mask));
  const b3 = FStar_Int_Cast.uint32_to_uint8(FStar_UInt32.logand(FStar_UInt32.shift_right(x)(FStar_UInt32.uint_to_t(24)))(mask));
  output[FStar_UInt32.uint_to_t(0)] = b0;
  output[FStar_UInt32.uint_to_t(1)] = b1;
  output[FStar_UInt32.uint_to_t(2)] = b2;
  output[FStar_UInt32.uint_to_t(3)] = b3;
  _res = null;
  return _res;
});

export const xor_uint8_p_2 = (output: u8s): ((_1: u8s) => ((_1: u32) => (null))) => ((in1: u8s) => ((len: u32) => {
  let _res;
  const _0_178 = FStar_UInt32.eq(len)(FStar_UInt32.uint_to_t(0));
  if( (_0_178 == true) ) {
    _res = null;
  } else {
    const uu____296 = _0_178;
    const i = FStar_UInt32.sub(len)(FStar_UInt32.uint_to_t(1));
    const in1i = in1[i];
    const oi = output[i];
    const _0_179 = oi;
    {
      const oi = FStar_UInt8.logxor(in1i)(_0_179);
      output[i] = oi;
      _res = xor_uint8_p_2(output)(in1)(i);
    }
  }
  return _res;
}));

export const sum_matrixes = (m: uint32_p): ((_1: uint32_p) => (null)) => ((m0: uint32_p) => {
  let _res;
  const m_0 = m[FStar_UInt32.uint_to_t(0)];
  const m0_0 = m0[FStar_UInt32.uint_to_t(0)];
  m[FStar_UInt32.uint_to_t(0)] = FStar_UInt32.add_mod(m_0)(m0_0);
  const m_1 = m[FStar_UInt32.uint_to_t(1)];
  const m0_1 = m0[FStar_UInt32.uint_to_t(1)];
  m[FStar_UInt32.uint_to_t(1)] = FStar_UInt32.add_mod(m_1)(m0_1);
  const m_2 = m[FStar_UInt32.uint_to_t(2)];
  const m0_2 = m0[FStar_UInt32.uint_to_t(2)];
  m[FStar_UInt32.uint_to_t(2)] = FStar_UInt32.add_mod(m_2)(m0_2);
  const m_3 = m[FStar_UInt32.uint_to_t(3)];
  const m0_3 = m0[FStar_UInt32.uint_to_t(3)];
  m[FStar_UInt32.uint_to_t(3)] = FStar_UInt32.add_mod(m_3)(m0_3);
  const m_4 = m[FStar_UInt32.uint_to_t(4)];
  const m0_4 = m0[FStar_UInt32.uint_to_t(4)];
  m[FStar_UInt32.uint_to_t(4)] = FStar_UInt32.add_mod(m_4)(m0_4);
  const m_5 = m[FStar_UInt32.uint_to_t(5)];
  const m0_5 = m0[FStar_UInt32.uint_to_t(5)];
  m[FStar_UInt32.uint_to_t(5)] = FStar_UInt32.add_mod(m_5)(m0_5);
  const m_6 = m[FStar_UInt32.uint_to_t(6)];
  const m0_6 = m0[FStar_UInt32.uint_to_t(6)];
  m[FStar_UInt32.uint_to_t(6)] = FStar_UInt32.add_mod(m_6)(m0_6);
  const m_7 = m[FStar_UInt32.uint_to_t(7)];
  const m0_7 = m0[FStar_UInt32.uint_to_t(7)];
  m[FStar_UInt32.uint_to_t(7)] = FStar_UInt32.add_mod(m_7)(m0_7);
  const m_8 = m[FStar_UInt32.uint_to_t(8)];
  const m0_8 = m0[FStar_UInt32.uint_to_t(8)];
  m[FStar_UInt32.uint_to_t(8)] = FStar_UInt32.add_mod(m_8)(m0_8);
  const m_9 = m[FStar_UInt32.uint_to_t(9)];
  const m0_9 = m0[FStar_UInt32.uint_to_t(9)];
  m[FStar_UInt32.uint_to_t(9)] = FStar_UInt32.add_mod(m_9)(m0_9);
  const m_10 = m[FStar_UInt32.uint_to_t(10)];
  const m0_10 = m0[FStar_UInt32.uint_to_t(10)];
  m[FStar_UInt32.uint_to_t(10)] = FStar_UInt32.add_mod(m_10)(m0_10);
  const m_11 = m[FStar_UInt32.uint_to_t(11)];
  const m0_11 = m0[FStar_UInt32.uint_to_t(11)];
  m[FStar_UInt32.uint_to_t(11)] = FStar_UInt32.add_mod(m_11)(m0_11);
  const m_12 = m[FStar_UInt32.uint_to_t(12)];
  const m0_12 = m0[FStar_UInt32.uint_to_t(12)];
  m[FStar_UInt32.uint_to_t(12)] = FStar_UInt32.add_mod(m_12)(m0_12);
  const m_13 = m[FStar_UInt32.uint_to_t(13)];
  const m0_13 = m0[FStar_UInt32.uint_to_t(13)];
  m[FStar_UInt32.uint_to_t(13)] = FStar_UInt32.add_mod(m_13)(m0_13);
  const m_14 = m[FStar_UInt32.uint_to_t(14)];
  const m0_14 = m0[FStar_UInt32.uint_to_t(14)];
  m[FStar_UInt32.uint_to_t(14)] = FStar_UInt32.add_mod(m_14)(m0_14);
  const m_15 = m[FStar_UInt32.uint_to_t(15)];
  const m0_15 = m0[FStar_UInt32.uint_to_t(15)];
  m[FStar_UInt32.uint_to_t(15)] = FStar_UInt32.add_mod(m_15)(m0_15);
  _res = null;
  return _res;
});

export const xor_bytes_inplace = (output: u8s): ((_1: u8s) => ((_1: u32) => (null))) => ((in1: u8s) => ((len: u32) => {
  let _res;
  const _0_180 = FStar_UInt32.eq(len)(FStar_UInt32.uint_to_t(0));
  if( (_0_180 == true) ) {
    _res = null;
  } else {
    const uu____446 = _0_180;
    const i = FStar_UInt32.sub(len)(FStar_UInt32.uint_to_t(1));
    const in1i = in1[i];
    const oi = output[i];
    const _0_181 = oi;
    {
      const oi = FStar_UInt8.logxor(in1i)(_0_181);
      output[i] = oi;
      _res = xor_bytes_inplace(output)(in1)(i);
    }
  }
  return _res;
}));

export const lemma_euclidean_division = (r: number): ((_1: number) => ((_1: Prims.pos) => (null))) => ((b: number) => ((q: Prims.pos) => (null)));

export const memset = (b: u8s): ((_1: h8) => ((_1: u32) => (null))) => ((z: h8) => ((len: u32) => {
  let _res;
  const _0_182 = (len == FStar_UInt32.uint_to_t(0));
  if( (_0_182 == true) ) {
    _res = null;
  } else {
    const uu____496 = _0_182;
    const h0 = FStar_ST.get(null);
    const i = FStar_UInt32.sub(len)(FStar_UInt32.uint_to_t(1));
    memset(FStar_Buffer.offset(b)(FStar_UInt32.uint_to_t(1)))(z)(i);
    b[FStar_UInt32.uint_to_t(0)] = z;
    const h1 = FStar_ST.get(null);
    _res = null;
  }
  return _res;
}));


