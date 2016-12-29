/* @flow */
import * as FStar_UInt8 from "./FStar_UInt8";
import * as Utils from "./Utils";
import * as FStar_Int_Cast from "./FStar_Int_Cast";
import * as Hacl_UInt64 from "./Hacl_UInt64";
import * as FStar_UInt64 from "./FStar_UInt64";
import * as Hacl_Symmetric_Poly1305_Bignum from "./Hacl_Symmetric_Poly1305_Bignum";
import * as FStar_Buffer from "./FStar_Buffer";
import * as Prims from "./Prims";
import * as FStar_ST from "./FStar_ST";
import * as FStar_Seq from "./FStar_Seq";
import * as Hacl_UInt8 from "./Hacl_UInt8";
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_Ghost from "./FStar_Ghost";
import * as Hacl_Symmetric_Poly1305_Spec from "./Hacl_Symmetric_Poly1305_Spec";
import * as FStar_HyperStack from "./FStar_HyperStack";
import * as Hacl_Symmetric_Poly1305_Bigint from "./Hacl_Symmetric_Poly1305_Bigint";
export type elemB = Hacl_Symmetric_Poly1305_Bigint.bigint;

export type wordB = Hacl_Symmetric_Poly1305_Bigint.bytes;

export type wordB_16 = Hacl_Symmetric_Poly1305_Bigint.bytes;

export const sel_word = (h: FStar_HyperStack.mem): ((_1: wordB) => (null)) => ((b: wordB) => {
  let _res;
  _res = null;
  return _res;
});

export const esel_word = (h: FStar_HyperStack.mem) => ((b: wordB) => {
  let _res;
  _res = null;
  return _res;
});

export const esel_word_16 = (h: FStar_HyperStack.mem) => ((b: wordB_16) => {
  let _res;
  _res = null;
  return _res;
});

const read_word_ = (b: wordB_16): ((_1: FStar_Seq.seq<Hacl_UInt8.byte>) => ((_1: FStar_UInt32.t) => (Hacl_Symmetric_Poly1305_Spec.word_16))) => ((s: FStar_Seq.seq<Hacl_UInt8.byte>) => ((i: FStar_UInt32.t) => {
  let _res;
  const h = FStar_ST.get(null);
  const _0_188 = FStar_UInt32.eq(i)(FStar_UInt32.uint_to_t(16));
  if( (_0_188 == true) ) {
    _res = s;
  } else {
    const uu____215 = _0_188;
    const x = b[i];
    const s_ = FStar_Seq.op_At_Bar(s)(FStar_Seq.create(1)(x));
    _res = read_word_(b)(s_)(FStar_UInt32.add(i)(FStar_UInt32.uint_to_t(1)));
  }
  return _res;
}));
export const read_word = (b: wordB_16): (Hacl_Symmetric_Poly1305_Spec.word_16) => {
  let _res;
  const h = FStar_ST.get(null);
  const s0 = FStar_Seq.createEmpty(null);
  _res = read_word_(b)(s0)(FStar_UInt32.uint_to_t(0));
  return _res;
};

export const sel_elem = (h: FStar_HyperStack.mem): ((_1: elemB) => (null)) => ((b: elemB) => {
  let _res;
  _res = null;
  return _res;
});

export const sel_int = (h: FStar_HyperStack.mem): ((_1: elemB) => (null)) => ((b: elemB) => {
  let _res;
  _res = null;
  return _res;
});

export const lemma_bitweight_templ_values = (n: number): (null) => (null);

export const lemma_eval_norm_is_bounded = (ha: FStar_HyperStack.mem): ((_1: elemB) => ((_1: number) => (null))) => ((a: elemB) => ((len: number) => (null)));

export const lemma_elemB_equality = (ha: FStar_HyperStack.mem): ((_1: FStar_HyperStack.mem) => ((_1: elemB) => ((_1: elemB) => ((_1: Prims.pos) => (null))))) => ((hb: FStar_HyperStack.mem) => ((a: elemB) => ((b: elemB) => ((len: Prims.pos) => (null)))));

export const lemma_toField_is_injective_0 = (ha: FStar_HyperStack.mem): ((_1: FStar_HyperStack.mem) => ((_1: elemB) => ((_1: elemB) => ((_1: number) => (null))))) => ((hb: FStar_HyperStack.mem) => ((a: elemB) => ((b: elemB) => ((len: number) => (null)))));

export const lemma_toField_is_injective = (ha: FStar_HyperStack.mem): ((_1: FStar_HyperStack.mem) => ((_1: elemB) => ((_1: elemB) => (null)))) => ((hb: FStar_HyperStack.mem) => ((a: elemB) => ((b: elemB) => (null))));

export const bound27_isSum = (h0: FStar_HyperStack.mem): ((_1: FStar_HyperStack.mem) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null)))) => ((h1: FStar_HyperStack.mem) => ((a: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((b: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null))));

export const lemma_sel_elem = (h0: FStar_HyperStack.mem): ((_1: FStar_HyperStack.mem) => ((_1: elemB) => ((_1: elemB) => ((_1: elemB) => (null))))) => ((h1: FStar_HyperStack.mem) => ((acc: elemB) => ((block: elemB) => ((r: elemB) => (null)))));

export const add_and_multiply = (acc: elemB): ((_1: elemB) => ((_1: elemB) => (null))) => ((block: elemB) => ((r: elemB) => {
  let _res;
  const h0 = FStar_ST.get(null);
  Hacl_Symmetric_Poly1305_Bignum.fsum_(acc)(block);
  const h1 = FStar_ST.get(null);
  FStar_ST.push_frame(null);
  const tmp = FStar_Buffer.create(FStar_UInt64.uint_to_t(0))(FStar_UInt32.uint_to_t(9));
  const h2 = FStar_ST.get(null);
  Hacl_Symmetric_Poly1305_Bignum.multiplication(tmp)(acc)(r);
  const h3 = FStar_ST.get(null);
  Hacl_Symmetric_Poly1305_Bignum.modulo(tmp);
  const h4 = FStar_ST.get(null);
  FStar_Buffer.blit(tmp)(FStar_UInt32.uint_to_t(0))(acc)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(5));
  const h5 = FStar_ST.get(null);
  FStar_ST.pop_frame(null);
  const h6 = FStar_ST.get(null);
  _res = null;
  return _res;
}));

export const zeroB = (a: elemB): (null) => {
  let _res;
  const zero = FStar_UInt64.uint_to_t(0);
  a[FStar_UInt32.uint_to_t(0)] = zero;
  a[FStar_UInt32.uint_to_t(1)] = zero;
  a[FStar_UInt32.uint_to_t(2)] = zero;
  a[FStar_UInt32.uint_to_t(3)] = zero;
  a[FStar_UInt32.uint_to_t(4)] = zero;
  const h = FStar_ST.get(null);
  _res = null;
  return _res;
};

const mk_mask = (nbits: FStar_UInt32.t): (Hacl_UInt64.t) => (FStar_UInt64.sub(FStar_UInt64.shift_left(FStar_UInt64.uint_to_t(1))(nbits))(FStar_UInt64.uint_to_t(1)));
export const lemma_toField_1 = (b: elemB): ((_1: wordB_16) => ((_1: FStar_HyperStack.mem) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null))))))) => ((s: wordB_16) => ((h: FStar_HyperStack.mem) => ((n0: Hacl_UInt64.t) => ((n1: Hacl_UInt64.t) => ((n2: Hacl_UInt64.t) => ((n3: Hacl_UInt64.t) => (null)))))));

export const upd_elemB = (b: elemB): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null)))))) => ((n0: Hacl_UInt64.t) => ((n1: Hacl_UInt64.t) => ((n2: Hacl_UInt64.t) => ((n3: Hacl_UInt64.t) => ((n4: Hacl_UInt64.t) => {
  let _res;
  b[FStar_UInt32.uint_to_t(0)] = n0;
  b[FStar_UInt32.uint_to_t(1)] = n1;
  b[FStar_UInt32.uint_to_t(2)] = n2;
  b[FStar_UInt32.uint_to_t(3)] = n3;
  b[FStar_UInt32.uint_to_t(4)] = n4;
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
})))));

export const lemma_toField_2 = (n0: Hacl_UInt64.t): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null))))))))) => ((n1: Hacl_UInt64.t) => ((n2: Hacl_UInt64.t) => ((n3: Hacl_UInt64.t) => ((n0_: Hacl_UInt64.t) => ((n1_: Hacl_UInt64.t) => ((n2_: Hacl_UInt64.t) => ((n3_: Hacl_UInt64.t) => ((n4_: Hacl_UInt64.t) => (null)))))))));

export const lemma_toField_3 = (n0: Hacl_UInt64.t): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null))))))))) => ((n1: Hacl_UInt64.t) => ((n2: Hacl_UInt64.t) => ((n3: Hacl_UInt64.t) => ((n0_: Hacl_UInt64.t) => ((n1_: Hacl_UInt64.t) => ((n2_: Hacl_UInt64.t) => ((n3_: Hacl_UInt64.t) => ((n4_: Hacl_UInt64.t) => (null)))))))));

export const toField = (b: elemB): ((_1: wordB_16) => (null)) => ((s: wordB_16) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const mask_26 = mk_mask(FStar_UInt32.uint_to_t(26));
  const s0 = FStar_Buffer.sub(s)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(4));
  const s1 = FStar_Buffer.sub(s)(FStar_UInt32.uint_to_t(4))(FStar_UInt32.uint_to_t(4));
  const s2 = FStar_Buffer.sub(s)(FStar_UInt32.uint_to_t(8))(FStar_UInt32.uint_to_t(4));
  const s3 = FStar_Buffer.sub(s)(FStar_UInt32.uint_to_t(12))(FStar_UInt32.uint_to_t(4));
  const n0 = Utils.uint32_of_bytes(s0);
  const n1 = Utils.uint32_of_bytes(s1);
  const n2 = Utils.uint32_of_bytes(s2);
  const n3 = Utils.uint32_of_bytes(s3);
  const _0_192 = n0;
  {
    const n0 = FStar_Int_Cast.uint32_to_uint64(_0_192);
    const _0_191 = n1;
    {
      const n1 = FStar_Int_Cast.uint32_to_uint64(_0_191);
      const _0_190 = n2;
      {
        const n2 = FStar_Int_Cast.uint32_to_uint64(_0_190);
        const _0_189 = n3;
        {
          const n3 = FStar_Int_Cast.uint32_to_uint64(_0_189);
          const n0_ = FStar_UInt64.logand(n0)(mask_26);
          const n1_ = FStar_UInt64.logor(FStar_UInt64.shift_right(n0)(FStar_UInt32.uint_to_t(26)))(FStar_UInt64.logand(FStar_UInt64.shift_left(n1)(FStar_UInt32.uint_to_t(6)))(mask_26));
          const n2_ = FStar_UInt64.logor(FStar_UInt64.shift_right(n1)(FStar_UInt32.uint_to_t(20)))(FStar_UInt64.logand(FStar_UInt64.shift_left(n2)(FStar_UInt32.uint_to_t(12)))(mask_26));
          const n3_ = FStar_UInt64.logor(FStar_UInt64.shift_right(n2)(FStar_UInt32.uint_to_t(14)))(FStar_UInt64.logand(FStar_UInt64.shift_left(n3)(FStar_UInt32.uint_to_t(18)))(mask_26));
          const n4_ = FStar_UInt64.shift_right(n3)(FStar_UInt32.uint_to_t(8));
          _res = upd_elemB(b)(n0_)(n1_)(n2_)(n3_)(n4_);
          return _res;
        }
      }
    }
  }
});

export const lemma_toField_plus_2_128_0 = (ha: FStar_HyperStack.mem): ((_1: elemB) => (null)) => ((a: elemB) => (null));

export const lemma_toField_plus_2_128_1 = (uu____2603: null): (null) => (null);

export const lemma_toField_plus_2_128 = (ha: FStar_HyperStack.mem): ((_1: elemB) => ((_1: FStar_HyperStack.mem) => ((_1: elemB) => (null)))) => ((a: elemB) => ((hb: FStar_HyperStack.mem) => ((b: elemB) => (null))));

export const add_2_24 = (x: Hacl_UInt64.t): (Hacl_UInt64.t) => (FStar_UInt64.add(x)(FStar_UInt64.shift_left(FStar_UInt64.uint_to_t(1))(FStar_UInt32.uint_to_t(24))));

export const toField_plus_2_128 = (b: elemB): ((_1: wordB_16) => (null)) => ((s: wordB_16) => {
  let _res;
  toField(b)(s);
  const h0 = FStar_ST.get(null);
  const b4 = b[FStar_UInt32.uint_to_t(4)];
  const b4_ = add_2_24(b4);
  b[FStar_UInt32.uint_to_t(4)] = b4_;
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
});

export const toField_plus = (a: elemB): ((_1: wordB) => ((_1: Utils.u32) => (null))) => ((b: wordB) => ((len: Utils.u32) => {
  let _res;
  const h0 = FStar_ST.get(null);
  FStar_ST.push_frame(null);
  const n = FStar_Buffer.create(FStar_UInt8.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
  FStar_Buffer.blit(b)(FStar_UInt32.uint_to_t(0))(n)(FStar_UInt32.uint_to_t(0))(len);
  const h1 = FStar_ST.get(null);
  n[len] = FStar_UInt8.uint_to_t(1);
  const h2 = FStar_ST.get(null);
  toField(a)(n);
  const h3 = FStar_ST.get(null);
  FStar_ST.pop_frame(null);
  const h4 = FStar_ST.get(null);
  _res = null;
  return _res;
}));

export const upd_wordB_16 = (s: wordB_16): ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => ((_1: Hacl_UInt8.t) => (null))))))))))))))))) => ((s0: Hacl_UInt8.t) => ((s1: Hacl_UInt8.t) => ((s2: Hacl_UInt8.t) => ((s3: Hacl_UInt8.t) => ((s4: Hacl_UInt8.t) => ((s5: Hacl_UInt8.t) => ((s6: Hacl_UInt8.t) => ((s7: Hacl_UInt8.t) => ((s8: Hacl_UInt8.t) => ((s9: Hacl_UInt8.t) => ((s10: Hacl_UInt8.t) => ((s11: Hacl_UInt8.t) => ((s12: Hacl_UInt8.t) => ((s13: Hacl_UInt8.t) => ((s14: Hacl_UInt8.t) => ((s15: Hacl_UInt8.t) => {
  let _res;
  s[FStar_UInt32.uint_to_t(0)] = s0;
  s[FStar_UInt32.uint_to_t(1)] = s1;
  s[FStar_UInt32.uint_to_t(2)] = s2;
  s[FStar_UInt32.uint_to_t(3)] = s3;
  s[FStar_UInt32.uint_to_t(4)] = s4;
  s[FStar_UInt32.uint_to_t(5)] = s5;
  s[FStar_UInt32.uint_to_t(6)] = s6;
  s[FStar_UInt32.uint_to_t(7)] = s7;
  s[FStar_UInt32.uint_to_t(8)] = s8;
  s[FStar_UInt32.uint_to_t(9)] = s9;
  s[FStar_UInt32.uint_to_t(10)] = s10;
  s[FStar_UInt32.uint_to_t(11)] = s11;
  s[FStar_UInt32.uint_to_t(12)] = s12;
  s[FStar_UInt32.uint_to_t(13)] = s13;
  s[FStar_UInt32.uint_to_t(14)] = s14;
  s[FStar_UInt32.uint_to_t(15)] = s15;
  _res = null;
  return _res;
}))))))))))))))));

export const trunc1305 = (a: elemB): ((_1: wordB_16) => (null)) => ((b: wordB_16) => {
  let _res;
  const h0 = FStar_ST.get(null);
  Hacl_Symmetric_Poly1305_Bignum.finalize(a);
  const h1 = FStar_ST.get(null);
  const a0 = a[FStar_UInt32.uint_to_t(0)];
  const a1 = a[FStar_UInt32.uint_to_t(1)];
  const a2 = a[FStar_UInt32.uint_to_t(2)];
  const a3 = a[FStar_UInt32.uint_to_t(3)];
  const a4 = a[FStar_UInt32.uint_to_t(4)];
  const b0 = FStar_Int_Cast.uint64_to_uint8(a0);
  const b1 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a0)(FStar_UInt32.uint_to_t(8)));
  const b2 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a0)(FStar_UInt32.uint_to_t(16)));
  const b3 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.add_mod(FStar_UInt64.shift_right(a0)(FStar_UInt32.uint_to_t(24)))(FStar_UInt64.shift_left(a1)(FStar_UInt32.uint_to_t(2))));
  const b4 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a1)(FStar_UInt32.uint_to_t(6)));
  const b5 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a1)(FStar_UInt32.uint_to_t(14)));
  const b6 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.add_mod(FStar_UInt64.shift_right(a1)(FStar_UInt32.uint_to_t(22)))(FStar_UInt64.shift_left(a2)(FStar_UInt32.uint_to_t(4))));
  const b7 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a2)(FStar_UInt32.uint_to_t(4)));
  const b8 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a2)(FStar_UInt32.uint_to_t(12)));
  const b9 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.add_mod(FStar_UInt64.shift_right(a2)(FStar_UInt32.uint_to_t(20)))(FStar_UInt64.shift_left(a3)(FStar_UInt32.uint_to_t(6))));
  const b10 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a3)(FStar_UInt32.uint_to_t(2)));
  const b11 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a3)(FStar_UInt32.uint_to_t(10)));
  const b12 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a3)(FStar_UInt32.uint_to_t(18)));
  const b13 = FStar_Int_Cast.uint64_to_uint8(a4);
  const b14 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a4)(FStar_UInt32.uint_to_t(8)));
  const b15 = FStar_Int_Cast.uint64_to_uint8(FStar_UInt64.shift_right(a4)(FStar_UInt32.uint_to_t(16)));
  upd_wordB_16(b)(b0)(b1)(b2)(b3)(b4)(b5)(b6)(b7)(b8)(b9)(b10)(b11)(b12)(b13)(b14)(b15);
  const h2 = FStar_ST.get(null);
  _res = null;
  return _res;
});

export const fix = (r: FStar_Buffer.buffer): ((_1: FStar_UInt32.t) => ((_1: Hacl_UInt8.t) => (null))) => ((i: FStar_UInt32.t) => ((mask: Hacl_UInt8.t) => {
  let _res;
  const _0_36 = r[i];
  const _0_37 = Hacl_UInt8.op_Amp_Hat(_0_36)(mask);
  r[i] = _0_37;
  _res = null;
  return _res;
}));

export const clamp = (r: wordB): (null) => {
  let _res;
  const mask_15 = FStar_UInt8.uint_to_t(15);
  const mask_252 = FStar_UInt8.uint_to_t(252);
  fix(r)(FStar_UInt32.uint_to_t(3))(mask_15);
  fix(r)(FStar_UInt32.uint_to_t(7))(mask_15);
  fix(r)(FStar_UInt32.uint_to_t(11))(mask_15);
  fix(r)(FStar_UInt32.uint_to_t(15))(mask_15);
  fix(r)(FStar_UInt32.uint_to_t(4))(mask_252);
  fix(r)(FStar_UInt32.uint_to_t(8))(mask_252);
  _res = fix(r)(FStar_UInt32.uint_to_t(12))(mask_252);
  return _res;
};

export const poly1305_init = (r: elemB): ((_1: wordB_16) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bytes) => (null))) => ((s: wordB_16) => ((key: Hacl_Symmetric_Poly1305_Bigint.bytes) => {
  let _res;
  const h0 = FStar_ST.get(null);
  FStar_ST.push_frame(null);
  const r_16 = FStar_Buffer.create(FStar_UInt8.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
  FStar_Buffer.blit(key)(FStar_UInt32.uint_to_t(0))(r_16)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
  FStar_Buffer.blit(key)(FStar_UInt32.uint_to_t(16))(s)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
  clamp(r_16);
  toField(r)(r_16);
  const h1 = FStar_ST.get(null);
  FStar_ST.pop_frame(null);
  const h2 = FStar_ST.get(null);
  _res = null;
  return _res;
}));

export const poly1305_start = (a: elemB): (null) => (zeroB(a));

export const seq_head_snoc = <_Aa>(xs: FStar_Seq.seq<_Aa> ): ((_1: _Aa) => (null)) => ((x: _Aa) => (null));

export const poly1305_update = (msgB: wordB_16): ((_1: elemB) => ((_1: elemB) => (null))) => ((acc: elemB) => ((r: elemB) => {
  let _res;
  const h0 = FStar_ST.get(null);
  FStar_ST.push_frame(null);
  const block = FStar_Buffer.create(FStar_UInt64.uint_to_t(0))(FStar_UInt32.uint_to_t(5));
  toField_plus_2_128(block)(msgB);
  const h1 = FStar_ST.get(null);
  add_and_multiply(acc)(block)(r);
  const h2 = FStar_ST.get(null);
  FStar_ST.pop_frame(null);
  const h3 = FStar_ST.get(null);
  _res = null;
  return _res;
}));

export const append_as_seq_sub = (h: FStar_HyperStack.mem): ((_1: FStar_UInt32.t) => ((_1: FStar_UInt32.t) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bytes) => (null)))) => ((nn: FStar_UInt32.t) => ((m: FStar_UInt32.t) => ((msg: Hacl_Symmetric_Poly1305_Bigint.bytes) => (null))));

export const poly1305_loop = (msg: Hacl_Symmetric_Poly1305_Bigint.bytes): ((_1: elemB) => ((_1: elemB) => ((_1: Utils.u32) => (null)))) => ((acc: elemB) => ((r: elemB) => ((ctr: Utils.u32) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const _0_193 = FStar_UInt32.lte(ctr)(FStar_UInt32.uint_to_t(0));
  if( (_0_193 == true) ) {
    _res = null;
  } else {
    const uu____4872 = _0_193;
    const msg0 = FStar_Buffer.sub(msg)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
    poly1305_update(msg0)(acc)(r);
    const h1 = FStar_ST.get(null);
    const msg1 = FStar_Buffer.offset(msg)(FStar_UInt32.uint_to_t(16));
    poly1305_loop(msg1)(acc)(r)(FStar_UInt32.sub(ctr)(FStar_UInt32.uint_to_t(1)));
    const h2 = FStar_ST.get(null);
    _res = null;
  }
  return _res;
})));

export const poly1305_last = (msg: wordB): ((_1: elemB) => ((_1: elemB) => ((_1: Utils.u32) => (null)))) => ((acc: elemB) => ((r: elemB) => ((len: Utils.u32) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const _0_194 = FStar_UInt32.eq(len)(FStar_UInt32.uint_to_t(0));
  if( (_0_194 == true) ) {
    _res = null;
  } else {
    const uu____5167 = _0_194;
    FStar_ST.push_frame(null);
    const block = FStar_Buffer.create(FStar_UInt64.uint_to_t(0))(FStar_UInt32.uint_to_t(5));
    toField_plus(block)(msg)(len);
    const h1 = FStar_ST.get(null);
    add_and_multiply(acc)(block)(r);
    const h2 = FStar_ST.get(null);
    FStar_ST.pop_frame(null);
    const h3 = FStar_ST.get(null);
    _res = null;
  }
  return _res;
})));

const add_word = (a: wordB_16): ((_1: wordB_16) => (null)) => ((b: wordB_16) => {
  let _res;
  const carry = FStar_UInt32.uint_to_t(0);
  {
    const x = Utils.uint32_of_bytes(a);
    const a04 = FStar_Int_Cast.uint32_to_uint64(x);
    {
      const x = Utils.uint32_of_bytes(FStar_Buffer.offset(a)(FStar_UInt32.uint_to_t(4)));
      const a48 = FStar_Int_Cast.uint32_to_uint64(x);
      {
        const x = Utils.uint32_of_bytes(FStar_Buffer.offset(a)(FStar_UInt32.uint_to_t(8)));
        const a812 = FStar_Int_Cast.uint32_to_uint64(x);
        {
          const x = Utils.uint32_of_bytes(FStar_Buffer.offset(a)(FStar_UInt32.uint_to_t(12)));
          const a1216 = FStar_Int_Cast.uint32_to_uint64(x);
          {
            const x = Utils.uint32_of_bytes(b);
            const b04 = FStar_Int_Cast.uint32_to_uint64(x);
            {
              const x = Utils.uint32_of_bytes(FStar_Buffer.offset(b)(FStar_UInt32.uint_to_t(4)));
              const b48 = FStar_Int_Cast.uint32_to_uint64(x);
              {
                const x = Utils.uint32_of_bytes(FStar_Buffer.offset(b)(FStar_UInt32.uint_to_t(8)));
                const b812 = FStar_Int_Cast.uint32_to_uint64(x);
                const x = Utils.uint32_of_bytes(FStar_Buffer.offset(b)(FStar_UInt32.uint_to_t(12)));
                const b1216 = FStar_Int_Cast.uint32_to_uint64(x);
                const z0 = FStar_UInt64.add(a04)(b04);
                const z1 = FStar_UInt64.add(FStar_UInt64.add(a48)(b48))(FStar_UInt64.shift_right(z0)(FStar_UInt32.uint_to_t(32)));
                const z2 = FStar_UInt64.add(FStar_UInt64.add(a812)(b812))(FStar_UInt64.shift_right(z1)(FStar_UInt32.uint_to_t(32)));
                const z3 = FStar_UInt64.add(FStar_UInt64.add(a1216)(b1216))(FStar_UInt64.shift_right(z2)(FStar_UInt32.uint_to_t(32)));
                Utils.bytes_of_uint32(FStar_Buffer.sub(a)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(4)))(FStar_Int_Cast.uint64_to_uint32(z0));
                Utils.bytes_of_uint32(FStar_Buffer.sub(a)(FStar_UInt32.uint_to_t(4))(FStar_UInt32.uint_to_t(4)))(FStar_Int_Cast.uint64_to_uint32(z1));
                Utils.bytes_of_uint32(FStar_Buffer.sub(a)(FStar_UInt32.uint_to_t(8))(FStar_UInt32.uint_to_t(4)))(FStar_Int_Cast.uint64_to_uint32(z2));
                _res = Utils.bytes_of_uint32(FStar_Buffer.sub(a)(FStar_UInt32.uint_to_t(12))(FStar_UInt32.uint_to_t(4)))(FStar_Int_Cast.uint64_to_uint32(z3));
                return _res;
              }
            }
          }
        }
      }
    }
  }
});
export const poly1305_finish = (tag: wordB_16): ((_1: elemB) => ((_1: wordB_16) => (null))) => ((acc: elemB) => ((s: wordB_16) => {
  let _res;
  trunc1305(acc)(tag);
  _res = add_word(tag)(s);
  return _res;
}));

export const poly1305_mac = (tag: wordB): ((_1: Hacl_Symmetric_Poly1305_Bigint.bytes) => ((_1: Utils.u32) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bytes) => (null)))) => ((msg: Hacl_Symmetric_Poly1305_Bigint.bytes) => ((len: Utils.u32) => ((key: Hacl_Symmetric_Poly1305_Bigint.bytes) => {
  let _res;
  FStar_ST.push_frame(null);
  const tmp = FStar_Buffer.create(FStar_UInt64.uint_to_t(0))(FStar_UInt32.uint_to_t(10));
  const acc = FStar_Buffer.sub(tmp)(FStar_UInt32.uint_to_t(0))(FStar_UInt32.uint_to_t(5));
  const r = FStar_Buffer.sub(tmp)(FStar_UInt32.uint_to_t(5))(FStar_UInt32.uint_to_t(5));
  const s = FStar_Buffer.create(FStar_UInt8.uint_to_t(0))(FStar_UInt32.uint_to_t(16));
  poly1305_init(r)(s)(key);
  const _0_195 = null;
  if( (_0_195 == null) ) {
    poly1305_start(acc);
    const ctr = FStar_UInt32.div(len)(FStar_UInt32.uint_to_t(16));
    const rest = FStar_UInt32.rem(len)(FStar_UInt32.uint_to_t(16));
    poly1305_loop(msg)(acc)(r)(ctr);
    const last_block = FStar_Buffer.sub(msg)(FStar_UInt32.mul(ctr)(FStar_UInt32.uint_to_t(16)))(rest);
    poly1305_last(last_block)(acc)(r)(rest);
    poly1305_finish(tag)(acc)(FStar_Buffer.sub(key)(FStar_UInt32.uint_to_t(16))(FStar_UInt32.uint_to_t(16)));
    _res = FStar_ST.pop_frame(null);
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
})));


