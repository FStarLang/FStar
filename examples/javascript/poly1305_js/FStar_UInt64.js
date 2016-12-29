/* @flow */
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_UInt from "./FStar_UInt";
export const n: number = 64;

export type Mk = {_tag: "Mk", _0: FStar_UInt.uint_t<null>};

export type t_ = Mk;

const uu___is_Mk = (projectee: t_): (boolean) => (true);
const __proj__Mk__item__v = (projectee: t_): (FStar_UInt.uint_t<null>) => {
  let _res;
  const _0_112 = projectee;
  if( (_0_112._tag === "Mk") ) {
    const v = _0_112._0;
    _res = v;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};
export type t = t_;

export const v = (x: t): (FStar_UInt.uint_t<null>) => (__proj__Mk__item__v(x));

export const add = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.add(n)(v(a))(v(b))
}));

export const add_underspec = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.add_underspec(n)(v(a))(v(b))
}));

export const add_mod = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.add_mod(n)(v(a))(v(b))
}));

export const sub = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.sub(n)(v(a))(v(b))
}));

export const sub_underspec = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.sub_underspec(n)(v(a))(v(b))
}));

export const sub_mod = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.sub_mod(n)(v(a))(v(b))
}));

export const mul = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.mul(n)(v(a))(v(b))
}));

export const mul_underspec = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.mul_underspec(n)(v(a))(v(b))
}));

export const mul_mod = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.mul_mod(n)(v(a))(v(b))
}));

export const div = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.div(n)(v(a))(v(b))
}));

export const div_underspec = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.div_underspec(n)(v(a))(v(b))
}));

export const rem = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.mod_(n)(v(a))(v(b))
}));

export const logand = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.logand(n)(v(a))(v(b))
}));

export const logxor = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.logxor(n)(v(a))(v(b))
}));

export const logor = (a: t): ((_1: t) => (t)) => ((b: t) => ({
  _tag: "Mk",
  _0: FStar_UInt.logor(n)(v(a))(v(b))
}));

export const lognot = (a: t): (t) => ({
  _tag: "Mk",
  _0: FStar_UInt.lognot(n)(v(a))
});

export const uint_to_t = (x: FStar_UInt.uint_t<null> ): (t) => ({
  _tag: "Mk",
  _0: x
});

export const shift_right = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => ({
  _tag: "Mk",
  _0: FStar_UInt.shift_right(n)(v(a))(FStar_UInt32.v(s))
}));

export const shift_left = (a: t): ((_1: FStar_UInt32.t) => (t)) => ((s: FStar_UInt32.t) => ({
  _tag: "Mk",
  _0: FStar_UInt.shift_left(n)(v(a))(FStar_UInt32.v(s))
}));

export const eq = (a: t): ((_1: t) => (boolean)) => ((b: t) => (FStar_UInt.eq(n)(v(a))(v(b))));

export const gt = (a: t): ((_1: t) => (boolean)) => ((b: t) => (FStar_UInt.gt(n)(v(a))(v(b))));

export const gte = (a: t): ((_1: t) => (boolean)) => ((b: t) => (FStar_UInt.gte(n)(v(a))(v(b))));

export const lt = (a: t): ((_1: t) => (boolean)) => ((b: t) => (FStar_UInt.lt(n)(v(a))(v(b))));

export const lte = (a: t): ((_1: t) => (boolean)) => ((b: t) => (FStar_UInt.lte(n)(v(a))(v(b))));

export const eq_mask = (a: t) => ((b: t) => {
  throw "Not yet implemented!";
});

export const gte_mask = (a: t) => ((b: t) => {
  throw "Not yet implemented!";
});

export const op_Plus_Hat: (_1: t) => ((_1: t) => (t)) = add;

export const op_Plus_Question_Hat: (_1: t) => ((_1: t) => (t)) = add_underspec;

export const op_Plus_Percent_Hat: (_1: t) => ((_1: t) => (t)) = add_mod;

export const op_Subtraction_Hat: (_1: t) => ((_1: t) => (t)) = sub;

export const op_Subtraction_Question_Hat: (_1: t) => ((_1: t) => (t)) = sub_underspec;

export const op_Subtraction_Percent_Hat: (_1: t) => ((_1: t) => (t)) = sub_mod;

export const op_Star_Hat: (_1: t) => ((_1: t) => (t)) = mul;

export const op_Star_Question_Hat: (_1: t) => ((_1: t) => (t)) = mul_underspec;

export const op_Star_Percent_Hat: (_1: t) => ((_1: t) => (t)) = mul_mod;

export const op_Slash_Hat: (_1: t) => ((_1: t) => (t)) = div;

export const op_Percent_Hat: (_1: t) => ((_1: t) => (t)) = rem;

export const op_Hat_Hat: (_1: t) => ((_1: t) => (t)) = logxor;

export const op_Amp_Hat: (_1: t) => ((_1: t) => (t)) = logand;

export const op_Bar_Hat: (_1: t) => ((_1: t) => (t)) = logor;

export const op_Less_Less_Hat: (_1: t) => ((_1: FStar_UInt32.t) => (t)) = shift_left;

export const op_Greater_Greater_Hat: (_1: t) => ((_1: FStar_UInt32.t) => (t)) = shift_right;

export const op_Equals_Hat: (_1: t) => ((_1: t) => (boolean)) = eq;

export const op_Greater_Hat: (_1: t) => ((_1: t) => (boolean)) = gt;

export const op_Greater_Equals_Hat: (_1: t) => ((_1: t) => (boolean)) = gte;

export const op_Less_Hat: (_1: t) => ((_1: t) => (boolean)) = lt;

export const op_Less_Equals_Hat: (_1: t) => ((_1: t) => (boolean)) = lte;

export const to_string = (uu____999: t) => {
  throw "Not yet implemented!";
};

export const of_string = (uu____1004: string) => {
  throw "Not yet implemented!";
};


