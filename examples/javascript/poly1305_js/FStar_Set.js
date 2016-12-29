/* @flow */
import * as Prims from "./Prims";
import * as FStar_TSet from "./FStar_TSet";
export type set<_Aa> = (_1: _Aa) => (boolean);

export type equal<_Aa,_As1,_As2> = null;

export const mem = <_Aa>(x: _Aa): ((_1: set<_Aa>) => (boolean)) => ((s: set<_Aa>) => (s(x)));

export const empty = <_Aa>(x: _Aa) => (false);

export const singleton = <_Aa>(x: _Aa): (set<_Aa>) => ((y: _Aa) => ((y == x)));

export const union = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (set<_Aa> )) => ((s2: set<_Aa>) => ((x: _Aa) => (s1(x) || s2(x))));

export const intersect = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (set<_Aa> )) => ((s2: set<_Aa>) => ((x: _Aa) => (s1(x) && s2(x))));

export const complement = <_Aa>(s: set<_Aa> ): (set<_Aa>) => ((x: _Aa) => (!s(x)));

export type subset<_Aa,_As1,_As2> = null;

export const mem_empty = <_Aa>(x: _Aa): (null) => (null);

export const mem_singleton = <_Aa>(x: _Aa): ((_1: _Aa) => (null)) => ((y: _Aa) => (null));

export const mem_union = <_Aa>(x: _Aa): ((_1: set<_Aa>) => ((_1: set<_Aa>) => (null))) => ((s1: set<_Aa>) => ((s2: set<_Aa>) => (null)));

export const mem_intersect = <_Aa>(x: _Aa): ((_1: set<_Aa>) => ((_1: set<_Aa>) => (null))) => ((s1: set<_Aa>) => ((s2: set<_Aa>) => (null)));

export const mem_complement = <_Aa>(x: _Aa): ((_1: set<_Aa>) => (null)) => ((s: set<_Aa>) => (null));

export const subset_mem = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (null)) => ((s2: set<_Aa>) => (null));

export const mem_subset = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (null)) => ((s2: set<_Aa>) => (null));

export const lemma_equal_intro = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (null)) => ((s2: set<_Aa>) => (null));

export const lemma_equal_elim = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (null)) => ((s2: set<_Aa>) => (null));

export const lemma_equal_refl = <_Aa>(s1: set<_Aa> ): ((_1: set<_Aa>) => (null)) => ((s2: set<_Aa>) => (null));

export const set_to_tset = <_Akey>(uu____405: set<_Akey>) => {
  throw "Not yet implemented!";
};

export const lemma_set_to_tset = <_Akey>(s: set<_Akey>) => ((x: _Akey) => {
  throw "Not yet implemented!";
});

export type eqtype = any;

export const as_set_ = <_Aa>(l: Prims.list<_Aa> ): (set<_Aa>) => {
  let _res;
  const _0_129 = l;
  if( (_0_129.length == 0) ) {
    _res = empty;
  } else {
    if( (_0_129.length > 0) ) {
      const hd = _0_129[0];
      const tl = _0_129.slice(1);
      _res = union(singleton(hd))(as_set_(tl));
    } else {
      throw "This value doesn\'t match!";
    }
  }
  return _res;
};

export const as_set = <_Aa>(l: Prims.list<_Aa> ): (set<_Aa>) => {
  let _res;
  const _0_130 = l;
  if( (_0_130.length == 0) ) {
    _res = empty;
  } else {
    if( (_0_130.length > 0) ) {
      const hd = _0_130[0];
      const tl = _0_130.slice(1);
      _res = union(singleton(hd))(as_set_(tl));
    } else {
      throw "This value doesn\'t match!";
    }
  }
  return _res;
};


