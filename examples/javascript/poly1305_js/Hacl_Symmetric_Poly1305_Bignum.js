/* @flow */
import * as Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4 from "./Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4";
import * as Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1 from "./Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1";
import * as Hacl_UInt64 from "./Hacl_UInt64";
import * as FStar_ST from "./FStar_ST";
import * as FStar_UInt64 from "./FStar_UInt64";
import * as Hacl_Symmetric_Poly1305_Bigint from "./Hacl_Symmetric_Poly1305_Bigint";
import * as FStar_UInt32 from "./FStar_UInt32";
import * as FStar_Ghost from "./FStar_Ghost";
import * as Prims from "./Prims";
export const prime: any = null;

export type satisfiesModuloConstraints<_Ah,_Ab> = null;

export type isSum<_Ah,_Ah1,_Aa,_Ab> = null;

export type bound27<_Ah,_Ab> = null;

export const w: (_1: FStar_UInt32.t) => (number) = FStar_UInt32.v;

const fsum_ = (a: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null)) => ((b: Hacl_Symmetric_Poly1305_Bigint.bigint) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const a0 = a[FStar_UInt32.uint_to_t(0)];
  const a1 = a[FStar_UInt32.uint_to_t(1)];
  const a2 = a[FStar_UInt32.uint_to_t(2)];
  const a3 = a[FStar_UInt32.uint_to_t(3)];
  const a4 = a[FStar_UInt32.uint_to_t(4)];
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  const b4 = b[FStar_UInt32.uint_to_t(4)];
  const ab0 = FStar_UInt64.add(a0)(b0);
  const ab1 = FStar_UInt64.add(a1)(b1);
  const ab2 = FStar_UInt64.add(a2)(b2);
  const ab3 = FStar_UInt64.add(a3)(b3);
  const ab4 = FStar_UInt64.add(a4)(b4);
  a[FStar_UInt32.uint_to_t(0)] = ab0;
  a[FStar_UInt32.uint_to_t(1)] = ab1;
  a[FStar_UInt32.uint_to_t(2)] = ab2;
  a[FStar_UInt32.uint_to_t(3)] = ab3;
  a[FStar_UInt32.uint_to_t(4)] = ab4;
  _res = null;
  return _res;
});
export const fsum_ = (a: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null)) => ((b: Hacl_Symmetric_Poly1305_Bigint.bigint) => {
  let _res;
  const h0 = FStar_ST.get(null);
  fsum_(a)(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
});

const update_9 = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null)))))))))) => ((c0: Hacl_UInt64.t) => ((c1: Hacl_UInt64.t) => ((c2: Hacl_UInt64.t) => ((c3: Hacl_UInt64.t) => ((c4: Hacl_UInt64.t) => ((c5: Hacl_UInt64.t) => ((c6: Hacl_UInt64.t) => ((c7: Hacl_UInt64.t) => ((c8: Hacl_UInt64.t) => {
  let _res;
  c[FStar_UInt32.uint_to_t(0)] = c0;
  c[FStar_UInt32.uint_to_t(1)] = c1;
  c[FStar_UInt32.uint_to_t(2)] = c2;
  c[FStar_UInt32.uint_to_t(3)] = c3;
  c[FStar_UInt32.uint_to_t(4)] = c4;
  c[FStar_UInt32.uint_to_t(5)] = c5;
  c[FStar_UInt32.uint_to_t(6)] = c6;
  c[FStar_UInt32.uint_to_t(7)] = c7;
  c[FStar_UInt32.uint_to_t(8)] = c8;
  _res = null;
  return _res;
})))))))));
const multiplication_0 = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => (null))))))))))) => ((a0: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((a1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((a2: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((a3: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((a4: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u27) => ((b0: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((b1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((b2: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((b3: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => ((b4: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.u26) => {
  let _res;
  const ab00 = FStar_UInt64.mul(a0)(b0);
  const ab01 = FStar_UInt64.mul(a0)(b1);
  const ab02 = FStar_UInt64.mul(a0)(b2);
  const ab03 = FStar_UInt64.mul(a0)(b3);
  const ab04 = FStar_UInt64.mul(a0)(b4);
  const ab10 = FStar_UInt64.mul(a1)(b0);
  const ab11 = FStar_UInt64.mul(a1)(b1);
  const ab12 = FStar_UInt64.mul(a1)(b2);
  const ab13 = FStar_UInt64.mul(a1)(b3);
  const ab14 = FStar_UInt64.mul(a1)(b4);
  const ab20 = FStar_UInt64.mul(a2)(b0);
  const ab21 = FStar_UInt64.mul(a2)(b1);
  const ab22 = FStar_UInt64.mul(a2)(b2);
  const ab23 = FStar_UInt64.mul(a2)(b3);
  const ab24 = FStar_UInt64.mul(a2)(b4);
  const ab30 = FStar_UInt64.mul(a3)(b0);
  const ab31 = FStar_UInt64.mul(a3)(b1);
  const ab32 = FStar_UInt64.mul(a3)(b2);
  const ab33 = FStar_UInt64.mul(a3)(b3);
  const ab34 = FStar_UInt64.mul(a3)(b4);
  const ab40 = FStar_UInt64.mul(a4)(b0);
  const ab41 = FStar_UInt64.mul(a4)(b1);
  const ab42 = FStar_UInt64.mul(a4)(b2);
  const ab43 = FStar_UInt64.mul(a4)(b3);
  const ab44 = FStar_UInt64.mul(a4)(b4);
  const c0 = ab00;
  const c1 = FStar_UInt64.add(ab01)(ab10);
  const c2 = FStar_UInt64.add(FStar_UInt64.add(ab02)(ab11))(ab20);
  const c3 = FStar_UInt64.add(FStar_UInt64.add(FStar_UInt64.add(ab03)(ab12))(ab21))(ab30);
  const c4 = FStar_UInt64.add(FStar_UInt64.add(FStar_UInt64.add(FStar_UInt64.add(ab04)(ab13))(ab22))(ab31))(ab40);
  const c5 = FStar_UInt64.add(FStar_UInt64.add(FStar_UInt64.add(ab14)(ab23))(ab32))(ab41);
  const c6 = FStar_UInt64.add(FStar_UInt64.add(ab24)(ab33))(ab42);
  const c7 = FStar_UInt64.add(ab34)(ab43);
  const c8 = ab44;
  _res = update_9(c)(c0)(c1)(c2)(c3)(c4)(c5)(c6)(c7)(c8);
  return _res;
}))))))))));
const multiplication_ = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null))) => ((a: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((b: Hacl_Symmetric_Poly1305_Bigint.bigint) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const a0 = a[FStar_UInt32.uint_to_t(0)];
  const a1 = a[FStar_UInt32.uint_to_t(1)];
  const a2 = a[FStar_UInt32.uint_to_t(2)];
  const a3 = a[FStar_UInt32.uint_to_t(3)];
  const a4 = a[FStar_UInt32.uint_to_t(4)];
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  const b4 = b[FStar_UInt32.uint_to_t(4)];
  _res = multiplication_0(c)(a0)(a1)(a2)(a3)(a4)(b0)(b1)(b2)(b3)(b4);
  return _res;
}));
export const multiplication = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((_1: Hacl_Symmetric_Poly1305_Bigint.bigint) => (null))) => ((a: Hacl_Symmetric_Poly1305_Bigint.bigint) => ((b: Hacl_Symmetric_Poly1305_Bigint.bigint) => {
  let _res;
  const h0 = FStar_ST.get(null);
  multiplication_(c)(a)(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
}));

export const times_5 = (b: Hacl_UInt64.t): (Hacl_UInt64.t) => (FStar_UInt64.add(FStar_UInt64.shift_left(b)(FStar_UInt32.uint_to_t(2)))(b));

export const freduce_degree_ = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  const b5 = b[FStar_UInt32.uint_to_t(5)];
  const b6 = b[FStar_UInt32.uint_to_t(6)];
  const b7 = b[FStar_UInt32.uint_to_t(7)];
  const b8 = b[FStar_UInt32.uint_to_t(8)];
  const b0_ = FStar_UInt64.add(b0)(times_5(b5));
  const b1_ = FStar_UInt64.add(b1)(times_5(b6));
  const b2_ = FStar_UInt64.add(b2)(times_5(b7));
  const b3_ = FStar_UInt64.add(b3)(times_5(b8));
  b[FStar_UInt32.uint_to_t(0)] = b0_;
  b[FStar_UInt32.uint_to_t(1)] = b1_;
  b[FStar_UInt32.uint_to_t(2)] = b2_;
  b[FStar_UInt32.uint_to_t(3)] = b3_;
  _res = null;
  return _res;
};

export const freduce_degree = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  freduce_degree_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

const mod2_26 = (x: Hacl_UInt64.t): (Hacl_UInt64.t) => (FStar_UInt64.logand(x)(FStar_UInt64.uint_to_t(0x3ffffff)));
const div2_26 = (x: Hacl_UInt64.t): (Hacl_UInt64.t) => (FStar_UInt64.shift_right(x)(FStar_UInt32.uint_to_t(26)));
const update_5 = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null)))))) => ((c0: Hacl_UInt64.t) => ((c1: Hacl_UInt64.t) => ((c2: Hacl_UInt64.t) => ((c3: Hacl_UInt64.t) => ((c4: Hacl_UInt64.t) => {
  let _res;
  c[FStar_UInt32.uint_to_t(0)] = c0;
  c[FStar_UInt32.uint_to_t(1)] = c1;
  c[FStar_UInt32.uint_to_t(2)] = c2;
  c[FStar_UInt32.uint_to_t(3)] = c3;
  c[FStar_UInt32.uint_to_t(4)] = c4;
  _res = null;
  return _res;
})))));
const update_6 = (c: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => ((_1: Hacl_UInt64.t) => (null))))))) => ((c0: Hacl_UInt64.t) => ((c1: Hacl_UInt64.t) => ((c2: Hacl_UInt64.t) => ((c3: Hacl_UInt64.t) => ((c4: Hacl_UInt64.t) => ((c5: Hacl_UInt64.t) => {
  let _res;
  c[FStar_UInt32.uint_to_t(0)] = c0;
  c[FStar_UInt32.uint_to_t(1)] = c1;
  c[FStar_UInt32.uint_to_t(2)] = c2;
  c[FStar_UInt32.uint_to_t(3)] = c3;
  c[FStar_UInt32.uint_to_t(4)] = c4;
  c[FStar_UInt32.uint_to_t(5)] = c5;
  _res = null;
  return _res;
}))))));
const carry_1_0 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((_1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => (null)))))) => ((b0: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((b1: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((b2: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((b3: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => ((b4: Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.u633) => {
  let _res;
  const b0_ = mod2_26(b0);
  const r0 = div2_26(b0);
  const b1_ = mod2_26(FStar_UInt64.add(b1)(r0));
  const r1 = div2_26(FStar_UInt64.add(b1)(r0));
  const b2_ = mod2_26(FStar_UInt64.add(b2)(r1));
  const r2 = div2_26(FStar_UInt64.add(b2)(r1));
  const b3_ = mod2_26(FStar_UInt64.add(b3)(r2));
  const r3 = div2_26(FStar_UInt64.add(b3)(r2));
  const b4_ = mod2_26(FStar_UInt64.add(b4)(r3));
  const b5_ = div2_26(FStar_UInt64.add(b4)(r3));
  _res = update_6(b)(b0_)(b1_)(b2_)(b3_)(b4_)(b5_);
  return _res;
})))));
const carry_1_ = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  const b4 = b[FStar_UInt32.uint_to_t(4)];
  _res = carry_1_0(b)(b0)(b1)(b2)(b3)(b4);
  return _res;
};
export const carry_1 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  carry_1_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

export const carry_2_ = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => (carry_1_(b));

export const carry_2 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  carry_2_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

export const carry_top_ = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b5 = b[FStar_UInt32.uint_to_t(5)];
  b[FStar_UInt32.uint_to_t(0)] = FStar_UInt64.add(b0)(times_5(b5));
  _res = null;
  return _res;
};

export const carry_top_1 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  carry_top_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

export const carry_top_2 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  carry_top_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

const carry_0_to_1_ = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b0_ = mod2_26(b0);
  const r0 = div2_26(b0);
  b[FStar_UInt32.uint_to_t(0)] = b0_;
  b[FStar_UInt32.uint_to_t(1)] = FStar_UInt64.add(b1)(r0);
  _res = null;
  return _res;
};
export const carry_0_to_1 = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const h0 = FStar_ST.get(null);
  carry_0_to_1_(b);
  const h1 = FStar_ST.get(null);
  _res = null;
  return _res;
};

export const freduce_coefficients = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  carry_1(b);
  carry_top_1(b);
  _res = carry_0_to_1(b);
  return _res;
};

export const modulo = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  freduce_degree(b);
  _res = freduce_coefficients(b);
  return _res;
};

export const finalize = (b: Hacl_Symmetric_Poly1305_Bigint.bigint): (null) => {
  let _res;
  const one = FStar_UInt64.uint_to_t(1);
  const mask_26 = FStar_UInt64.sub(FStar_UInt64.shift_left(one)(FStar_UInt32.uint_to_t(26)))(one);
  const mask2_26m5 = FStar_UInt64.sub(mask_26)(FStar_UInt64.shift_left(one)(FStar_UInt32.uint_to_t(2)));
  const b0 = b[FStar_UInt32.uint_to_t(0)];
  const b1 = b[FStar_UInt32.uint_to_t(1)];
  const b2 = b[FStar_UInt32.uint_to_t(2)];
  const b3 = b[FStar_UInt32.uint_to_t(3)];
  const b4 = b[FStar_UInt32.uint_to_t(4)];
  const mask = FStar_UInt64.eq_mask(b4)(mask_26);
  const _0_187 = mask;
  {
    const mask = FStar_UInt64.logand(FStar_UInt64.eq_mask(b3)(mask_26))(_0_187);
    const _0_186 = mask;
    {
      const mask = FStar_UInt64.logand(FStar_UInt64.eq_mask(b2)(mask_26))(_0_186);
      const _0_185 = mask;
      {
        const mask = FStar_UInt64.logand(FStar_UInt64.eq_mask(b1)(mask_26))(_0_185);
        const _0_184 = mask;
        {
          const mask = FStar_UInt64.logand(FStar_UInt64.gte_mask(b0)(mask2_26m5))(_0_184);
          b[FStar_UInt32.uint_to_t(0)] = FStar_UInt64.sub(b0)(FStar_UInt64.logand(mask)(mask2_26m5));
          b[FStar_UInt32.uint_to_t(1)] = FStar_UInt64.sub(b1)(FStar_UInt64.logand(b1)(mask));
          b[FStar_UInt32.uint_to_t(2)] = FStar_UInt64.sub(b2)(FStar_UInt64.logand(b2)(mask));
          b[FStar_UInt32.uint_to_t(3)] = FStar_UInt64.sub(b3)(FStar_UInt64.logand(b3)(mask));
          b[FStar_UInt32.uint_to_t(4)] = FStar_UInt64.sub(b4)(FStar_UInt64.logand(b4)(mask));
          _res = null;
          return _res;
        }
      }
    }
  }
};


