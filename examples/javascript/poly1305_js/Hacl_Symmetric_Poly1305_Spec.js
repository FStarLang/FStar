/* @flow */
import * as FStar_UInt8 from "./FStar_UInt8";
import * as FStar_Mul from "./FStar_Mul";
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_Seq from "./FStar_Seq";
import * as Hacl_UInt8 from "./Hacl_UInt8";
import * as Prims from "./Prims";
export const p_1305: number = (Prims.pow2(130) - 5);

export type elem = number;

export type word = FStar_Seq.seq<Hacl_UInt8.byte> ;

export type word_16 = FStar_Seq.seq<Hacl_UInt8.byte> ;

export type text = FStar_Seq.seq<elem> ;

export type tag = word_16;

export const taglen = <_Auu____17>(id: _Auu____17): (FStar_UInt32.t) => (FStar_UInt32.uint_to_t(16));

export const field_add = (a: elem): ((_1: elem) => (elem)) => ((b: elem) => (((a + b) % p_1305)));

export const field_mul = (a: elem): ((_1: elem) => (elem)) => ((b: elem) => ((FStar_Mul.op_Star(a)(b) % p_1305)));

export const op_Plus_At: (_1: elem) => ((_1: elem) => (elem)) = field_add;

export const op_Star_At: (_1: elem) => ((_1: elem) => (elem)) = field_mul;

export const little_endian = (b: word): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const lemma_euclidean_division = (a: number): ((_1: number) => (null)) => ((b: number) => (null));

export const lemma_factorise = (a: number): ((_1: number) => (null)) => ((b: number) => (null));

export const little_endian_null = (len: number): (null) => (null);

export const little_endian_singleton = (n: Hacl_UInt8.t): (null) => (null);

export const little_endian_append = (w1: word): ((_1: word) => (null)) => ((w2: word) => (null));

export const lemma_little_endian_is_bounded = (b: word): (null) => (null);

export const lemma_little_endian_lt_2_128 = (b: word): (null) => (null);

export const encode = (w: word): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const pad_0 = (b: FStar_Seq.seq<FStar_UInt8.t> ): ((_1: number) => (FStar_Seq.seq<FStar_UInt8.t> )) => ((l: number) => (FStar_Seq.append(b)(FStar_Seq.create(l)(FStar_UInt8.uint_to_t(0)))));

export const encode_pad = (prefix: FStar_Seq.seq<elem> ): ((_1: FStar_Seq.seq<Hacl_UInt8.t>) => (null)) => ((txt: FStar_Seq.seq<Hacl_UInt8.t>) => {
  let _res;
  _res = null;
  return _res;
});

export const trunc_1305 = (e: elem): (elem) => ((e % Prims.pow2(128)));

export const lemma_little_endian_is_injective_0 = (b: word): (null) => (null);

export const lemma_little_endian_is_injective_1 = (b: Prims.pos): ((_1: number) => ((_1: number) => ((_1: number) => ((_1: number) => (null))))) => ((q: number) => ((r: number) => ((q_: number) => ((r_: number) => (null)))));

export const lemma_little_endian_is_injective_2 = (b: word): ((_1: Prims.pos) => (null)) => ((len: Prims.pos) => (null));

export const lemma_little_endian_is_injective_3 = (b: word): ((_1: word) => ((_1: Prims.pos) => (null))) => ((b_: word) => ((len: Prims.pos) => (null)));

export const lemma_little_endian_is_injective = (b: word): ((_1: word) => ((_1: number) => (null))) => ((b_: word) => ((len: number) => (null)));

export const lemma_pad_0_injective = (b0: FStar_Seq.seq<FStar_UInt8.t> ): ((_1: FStar_Seq.seq<FStar_UInt8.t>) => ((_1: number) => (null))) => ((b1: FStar_Seq.seq<FStar_UInt8.t>) => ((l: number) => (null)));

export const lemma_encode_injective = (w0: word): ((_1: word) => (null)) => ((w1: word) => (null));

export const lemma_encode_pad_injective = (p0: FStar_Seq.seq<elem> ): ((_1: FStar_Seq.seq<Hacl_UInt8.t>) => ((_1: FStar_Seq.seq<elem>) => ((_1: FStar_Seq.seq<Hacl_UInt8.t>) => (null)))) => ((t0: FStar_Seq.seq<Hacl_UInt8.t>) => ((p1: FStar_Seq.seq<elem>) => ((t1: FStar_Seq.seq<Hacl_UInt8.t>) => (null))));

export const encode_pad_empty = (prefix: FStar_Seq.seq<elem> ): ((_1: FStar_Seq.seq<Hacl_UInt8.t>) => (null)) => ((txt: FStar_Seq.seq<Hacl_UInt8.t>) => (null));

export const encode_pad_snoc = (prefix: FStar_Seq.seq<elem> ): ((_1: FStar_Seq.seq<Hacl_UInt8.t>) => ((_1: word_16) => (null))) => ((txt: FStar_Seq.seq<Hacl_UInt8.t>) => ((w: word_16) => (null)));

export const seq_head = <_a>(vs: FStar_Seq.seq<_a> ): (FStar_Seq.seq<_a>) => (FStar_Seq.slice(vs)(0)((FStar_Seq.length(vs) - 1)));

export const poly = (vs: FStar_Seq.seq<elem> ): ((_1: elem) => (elem)) => ((r: elem) => {
  let _res;
  const _0_183 = (FStar_Seq.length(vs) == 0);
  if( (_0_183 == true) ) {
    _res = 0;
  } else {
    const uu____850 = _0_183;
    _res = op_Star_At(op_Plus_At(poly(seq_head(vs))(r))(FStar_Seq.index(vs)((FStar_Seq.length(vs) - 1))))(r);
  }
  return _res;
});

const fix = (r: word_16): ((_1: number) => ((_1: Hacl_UInt8.t) => (word_16))) => ((i: number) => ((m: Hacl_UInt8.t) => (FStar_Seq.upd(r)(i)(FStar_UInt8.logand(FStar_Seq.index(r)(i))(m)))));
export const clamp = (r: word_16): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const mac_1305 = (vs: FStar_Seq.seq<elem> ): ((_1: elem) => ((_1: word) => (null))) => ((r: elem) => ((s: word) => {
  let _res;
  _res = null;
  return _res;
}));


