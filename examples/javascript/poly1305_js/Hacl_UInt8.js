/* @flow */
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_UInt8 from "./FStar_UInt8";
export const n: number = 8;

export type t = FStar_UInt8.t;

export const v = (x: t): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const add = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.add(a)(b)));

export const add_mod = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.add_mod(a)(b)));

export const sub = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.sub(a)(b)));

export const sub_mod = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.sub_mod(a)(b)));

export const mul = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.mul(a)(b)));

export const mul_mod = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.mul_mod(a)(b)));

export const logand = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logand(a)(b)));

export const logxor = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logxor(a)(b)));

export const logor = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logor(a)(b)));

export const lognot = (a: t): (t) => (FStar_UInt8.lognot(a));

export const shift_right = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => (FStar_UInt8.shift_right(a)(s)));

export const shift_left = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => (FStar_UInt8.shift_left(a)(s)));

export const eq_mask = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.eq_mask(a)(b)));

export const gte_mask = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.gte_mask(a)(b)));

export const gt_mask = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.lognot(FStar_UInt8.gte_mask(b)(a))));

export const lt_mask = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.lognot(FStar_UInt8.gte_mask(a)(b))));

export const lte_mask = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.lognot(FStar_UInt8.lognot(FStar_UInt8.gte_mask(b)(a)))));

export const op_Plus_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.add(a)(b)));

export const op_Plus_Percent_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.add_mod(a)(b)));

export const op_Subtraction_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.sub(a)(b)));

export const op_Subtraction_Percent_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.sub_mod(a)(b)));

export const op_Star_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.mul(a)(b)));

export const op_Star_Percent_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.mul_mod(a)(b)));

export const op_Amp_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logand(a)(b)));

export const op_Hat_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logxor(a)(b)));

export const op_Bar_Hat = (a: t): ((_1: t) => (t)) => ((b: t) => (FStar_UInt8.logor(a)(b)));

export const op_Greater_Greater_Hat = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => (FStar_UInt8.shift_right(a)(s)));

export const op_Less_Less_Hat = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => (FStar_UInt8.shift_left(a)(s)));

export const of_string = (uu____309: string) => {
  throw "Not yet implemented!";
};

export type _byte = t;


