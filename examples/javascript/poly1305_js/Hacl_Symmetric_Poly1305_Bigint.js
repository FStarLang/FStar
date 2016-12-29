/* @flow */
import * as FStar_Buffer from "./FStar_Buffer";
import * as Prims from "./Prims";
import * as FStar_HyperStack from "./FStar_HyperStack";
import * as Hacl_UInt64 from "./Hacl_UInt64";
import * as FStar_UInt64 from "./FStar_UInt64";
import * as Hacl_UInt8 from "./Hacl_UInt8";
import * as FStar_UInt8 from "./FStar_UInt8";
export type u8 = FStar_UInt8.t;

export type h8 = Hacl_UInt8.t;

export type u64 = FStar_UInt64.t;

export type h64 = Hacl_UInt64.t;

export type heap = FStar_HyperStack.mem;

export type template = (_1: number) => (Prims.pos);

export type bigint = FStar_Buffer.buffer;

export type bytes = FStar_Buffer.buffer;

export type norm<_Ah,_Ab> = null;

export type _null<_Ah,_Ab> = null;

export type filled<_Ah,_Ab> = null;

export const bitweight = (t: template): ((_1: number) => (null)) => ((n: number) => {
  let _res;
  _res = null;
  return _res;
});

export const bitweight_def = (t: template): ((_1: number) => (null)) => ((n: number) => (null));

export const _eval = (h: heap): ((_1: bigint) => ((_1: number) => (null))) => ((b: bigint) => ((n: number) => {
  let _res;
  _res = null;
  return _res;
}));

export const eval_def = (h: heap): ((_1: bigint) => ((_1: number) => (null))) => ((b: bigint) => ((n: number) => (null)));

export const eval_bytes = (h: heap): ((_1: bytes) => ((_1: number) => (null))) => ((b: bytes) => ((n: number) => {
  let _res;
  _res = null;
  return _res;
}));

export const maxValue = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => (null))) => ((b: bigint) => ((l: Prims.pos) => {
  let _res;
  _res = null;
  return _res;
}));

export const maxValue_increases = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => ((_1: Prims.pos) => (null)))) => ((b: bigint) => ((n: Prims.pos) => ((m: Prims.pos) => (null))));

export const maxValue_lemma_aux = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => (null))) => ((b: bigint) => ((l: Prims.pos) => (null)));

export const maxValue_lemma = (h: heap): ((_1: bigint) => (null)) => ((b: bigint) => (null));

export const maxValue_bound_lemma_aux = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => ((_1: number) => (null)))) => ((b: bigint) => ((l: Prims.pos) => ((bound: number) => (null))));

export const maxValue_bound_lemma = (h: heap): ((_1: bigint) => ((_1: number) => (null))) => ((b: bigint) => ((bound: number) => (null)));

export const maxValueNorm = (h: heap): ((_1: bigint) => (null)) => ((b: bigint) => {
  let _res;
  _res = null;
  return _res;
});

export const maxValueIdx = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => (null))) => ((b: bigint) => ((l: Prims.pos) => {
  let _res;
  _res = null;
  return _res;
}));

export const maxValue_eq_lemma = (ha: heap): ((_1: heap) => ((_1: bigint) => ((_1: bigint) => ((_1: Prims.pos) => (null))))) => ((hb: heap) => ((a: bigint) => ((b: bigint) => ((l: Prims.pos) => (null)))));

export const maxValueNorm_eq_lemma = (ha: heap): ((_1: heap) => ((_1: bigint) => ((_1: bigint) => (null)))) => ((hb: heap) => ((a: bigint) => ((b: bigint) => (null))));

export const eval_eq_lemma = (ha: heap): ((_1: heap) => ((_1: bigint) => ((_1: bigint) => ((_1: number) => (null))))) => ((hb: heap) => ((a: bigint) => ((b: bigint) => ((len: number) => (null)))));

export const norm_eq_lemma = (ha: heap): ((_1: heap) => ((_1: bigint) => ((_1: bigint) => (null)))) => ((hb: heap) => ((a: bigint) => ((b: bigint) => (null))));

export const eval_partial_eq_lemma = (ha: heap): ((_1: heap) => ((_1: bigint) => ((_1: bigint) => ((_1: number) => ((_1: number) => (null)))))) => ((hb: heap) => ((a: bigint) => ((b: bigint) => ((ctr: number) => ((len: number) => (null))))));

export const eval_null = (h: heap): ((_1: bigint) => ((_1: number) => (null))) => ((b: bigint) => ((len: number) => (null)));

export const max_value_of_null_lemma = (h: heap): ((_1: bigint) => ((_1: Prims.pos) => (null))) => ((b: bigint) => ((l: Prims.pos) => (null)));


