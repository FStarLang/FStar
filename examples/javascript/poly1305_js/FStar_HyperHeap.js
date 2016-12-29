/* @flow */
import * as FStar_Set from "./FStar_Set";
import * as FStar_Map from "./FStar_Map";
import * as FStar_Heap from "./FStar_Heap";
import * as Prims from "./Prims";
export type rid = Prims.list<[number,number]> ;

export const reveal = (r: rid): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const color = (x: rid): (null) => {
  let _res;
  _res = null;
  return _res;
};

export type t = FStar_Map.t<rid,FStar_Heap.heap> ;

export const has_eq_rid = (u: null): (null) => (null);

export const root: rid = [];

export const lemma_root_has_color_zero = (r: rid): (null) => (null);

export const root_has_color_zero = (u: null): (null) => (null);

export type rref<_Aid,_Aa> = FStar_Heap.ref<_Aa> ;

export const has_eq_rref = (id: rid): ((_1: null) => (null)) => ((a: null) => (null));

export const as_ref = <_Aa>(id: rid): ((_1: rref<null,_Aa>) => (FStar_Heap.ref<_Aa> )) => ((r: rref<null,_Aa>) => (r));

export const ref_as_rref = <_a>(i: rid): ((_1: FStar_Heap.ref<_a>) => (null)) => ((r: FStar_Heap.ref<_a>) => {
  let _res;
  _res = null;
  return _res;
});

export const lemma_as_ref_inj = <_Aa>(i: rid): ((_1: rref<null,_Aa>) => (null)) => ((r: rref<null,_Aa>) => (null));

export const includes = (r1: rid): ((_1: rid) => (null)) => ((r2: rid) => {
  let _res;
  _res = null;
  return _res;
});

export const disjoint = (i: rid): ((_1: rid) => (null)) => ((j: rid) => {
  let _res;
  _res = null;
  return _res;
});

const lemma_aux = (k: rid): ((_1: rid) => (null)) => ((i: rid) => (null));
export const lemma_disjoint_includes = (i: rid): ((_1: rid) => ((_1: rid) => (null))) => ((j: rid) => ((k: rid) => (null)));

export const _extends = (r0: rid): ((_1: rid) => (null)) => ((r1: rid) => {
  let _res;
  _res = null;
  return _res;
});

export const parent = (r: rid): (rid) => (Prims.__proj__Cons__item__tl(r));

export const lemma_includes_refl = (i: rid): (null) => (null);

export const lemma_extends_includes = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

export const lemma_includes_anti_symmetric = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

export const lemma_extends_disjoint = (i: rid): ((_1: rid) => ((_1: rid) => (null))) => ((j: rid) => ((k: rid) => (null)));

export const lemma_extends_parent = (i: rid): (null) => (null);

export const lemma_extends_not_root = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

export const lemma_extends_only_parent = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

const test0: null = null;
const test1 = (r1: rid): ((_1: rid) => (null)) => ((r2: rid) => (null));
export type fresh_region<_Ai,_Am0,_Am1> = null;

export const sel = <_Aa>(i: rid): ((_1: t) => ((_1: rref<null,_Aa>) => (null))) => ((m: t) => ((r: rref<null,_Aa>) => {
  let _res;
  _res = null;
  return _res;
}));

export const op_String_Access = <_Aa>(i: rid): ((_1: t) => ((_1: rref<null,_Aa>) => (null))) => ((m: t) => ((r: rref<null,_Aa>) => {
  let _res;
  _res = null;
  return _res;
}));

export const upd = <_Aa>(i: rid): ((_1: t) => ((_1: rref<null,_Aa>) => ((_1: _Aa) => (null)))) => ((m: t) => ((r: rref<null,_Aa>) => ((v: _Aa) => {
  let _res;
  _res = null;
  return _res;
})));

export const op_String_Assignment = <_Aa>(i: rid): ((_1: t) => ((_1: rref<null,_Aa>) => ((_1: _Aa) => (null)))) => ((m: t) => ((r: rref<null,_Aa>) => ((v: _Aa) => {
  let _res;
  _res = null;
  return _res;
})));

export const mod_set = (uu____429: FStar_Set.set<rid>) => {
  throw "Not yet implemented!";
};

export type modifies<_As,_Am0,_Am1> = null;

export type modifies_just<_As,_Am0,_Am1> = null;

export type modifies_one<_Ar,_Am0,_Am1> = null;

export type equal_on<_As,_Am0,_Am1> = null;

export const lemma_modifies_just_trans = (m1: t): ((_1: t) => ((_1: t) => ((_1: FStar_Set.set<rid>) => ((_1: FStar_Set.set<rid>) => (null))))) => ((m2: t) => ((m3: t) => ((s1: FStar_Set.set<rid>) => ((s2: FStar_Set.set<rid>) => (null)))));

export const lemma_modifies_trans = (m1: t): ((_1: t) => ((_1: t) => ((_1: FStar_Set.set<rid>) => ((_1: FStar_Set.set<rid>) => (null))))) => ((m2: t) => ((m3: t) => ((s1: FStar_Set.set<rid>) => ((s2: FStar_Set.set<rid>) => (null)))));

export const lemma_includes_trans = (i: rid): ((_1: rid) => ((_1: rid) => (null))) => ((j: rid) => ((k: rid) => (null)));

export const lemma_modset = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

export const lemma_modifies_includes = (m1: t): ((_1: t) => ((_1: rid) => ((_1: rid) => (null)))) => ((m2: t) => ((s1: rid) => ((s2: rid) => (null))));

export const lemma_modifies_includes2 = (m1: t): ((_1: t) => ((_1: FStar_Set.set<rid>) => ((_1: FStar_Set.set<rid>) => (null)))) => ((m2: t) => ((s1: FStar_Set.set<rid>) => ((s2: FStar_Set.set<rid>) => (null))));

export const lemma_disjoint_parents = (pr: rid): ((_1: rid) => ((_1: rid) => ((_1: rid) => (null)))) => ((r: rid) => ((ps: rid) => ((s: rid) => (null))));

export const contains_ref = <_Aa>(i: rid): ((_1: rref<null,_Aa>) => ((_1: t) => (null))) => ((r: rref<null,_Aa>) => ((m: t) => {
  let _res;
  _res = null;
  return _res;
}));

export const weak_contains_ref = <_Aa>(i: rid): ((_1: rref<null,_Aa>) => ((_1: t) => (null))) => ((r: rref<null,_Aa>) => ((m: t) => {
  let _res;
  _res = null;
  return _res;
}));

export type fresh_rref<_Aa,_Ai,_Ar,_Am0,_Am1> = null;

export type modifies_rref<_Ar,_As,_Ah0,_Ah1> = null;

export const lemma_include_cons = (i: rid): ((_1: rid) => (null)) => ((j: rid) => (null));

export type map_invariant<_Am> = null;

export const lemma_extends_fresh_disjoint = (i: rid): ((_1: rid) => ((_1: rid) => ((_1: rid) => ((_1: t) => ((_1: t) => (null)))))) => ((j: rid) => ((ipar: rid) => ((jpar: rid) => ((m0: t) => ((m1: t) => (null))))));

export type disjoint_regions<_As1,_As2> = null;

export const extends_parent = (tip: rid): ((_1: rid) => (null)) => ((r: rid) => (null));

export const includes_child = (tip: rid): ((_1: rid) => (null)) => ((r: rid) => (null));

export const root_is_root = (s: rid): (null) => (null);


