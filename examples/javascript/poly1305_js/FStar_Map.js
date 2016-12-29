/* @flow */
import * as FStar_Set from "./FStar_Set";
export type t<_Akey,_Avalue> = {_tag: "Record", _mappings: (_1: _Akey) => (_Avalue), _domain: FStar_Set.set<_Akey>};

export const sel = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => (_Avalue)) => ((k: _Akey) => (m._mappings(k)));

export const upd = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Avalue) => (t<_Akey,_Avalue> ))) => ((k: _Akey) => ((v: _Avalue) => {
  let _res;
  const _0_131 = (x: _Akey) => {
    let _res;
    const _0_132 = (x == k);
    if( (_0_132 == true) ) {
      _res = v;
    } else {
      const uu____142 = _0_132;
      _res = m._mappings(x);
    }
    return _res;
  };
  _res = {
    _tag: "Record",
    _mappings: _0_131,
    _domain: FStar_Set.union(m._domain)(FStar_Set.singleton(k))
  };
  return _res;
}));

export const _const = <_Akey,_Avalue>(v: _Avalue): (t<_Akey,_Avalue>) => {
  let _res;
  const _0_133 = (uu____166: _Akey) => (v);
  _res = {
    _tag: "Record",
    _mappings: _0_133,
    _domain: FStar_Set.complement(FStar_Set.empty)
  };
  return _res;
};

export const concat = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => (t<_Akey,_Avalue> )) => ((m2: t<_Akey,_Avalue>) => {
  let _res;
  const _0_134 = (x: _Akey) => {
    let _res;
    const _0_135 = FStar_Set.mem(x)(m2._domain);
    if( (_0_135 == true) ) {
      _res = m2._mappings(x);
    } else {
      const uu____211 = _0_135;
      _res = m1._mappings(x);
    }
    return _res;
  };
  _res = {
    _tag: "Record",
    _mappings: _0_134,
    _domain: FStar_Set.union(m1._domain)(m2._domain)
  };
  return _res;
});

export const contains = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => (boolean)) => ((k: _Akey) => (FStar_Set.mem(k)(m._domain)));

export const restrict = <_Akey,_Avalue>(s: FStar_Set.set<_Akey> ): ((_1: t<_Akey,_Avalue>) => (t<_Akey,_Avalue> )) => ((m: t<_Akey,_Avalue>) => ({
  _tag: "Record",
  _mappings: m._mappings,
  _domain: FStar_Set.intersect(s)(m._domain)
}));

export const domain = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): (FStar_Set.set<_Akey>) => (m._domain);

export const lemma_SelUpd1 = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Avalue) => (null))) => ((k: _Akey) => ((v: _Avalue) => (null)));

export const lemma_SelUpd2 = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Akey) => ((_1: _Avalue) => (null)))) => ((k1: _Akey) => ((k2: _Akey) => ((v: _Avalue) => (null))));

export const lemma_SelConst = <_Akey,_Avalue>(v: _Avalue): ((_1: _Akey) => (null)) => ((k: _Akey) => (null));

export const lemma_SelRestrict = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: FStar_Set.set<_Akey>) => ((_1: _Akey) => (null))) => ((ks: FStar_Set.set<_Akey>) => ((k: _Akey) => (null)));

export const lemma_SelConcat1 = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => ((_1: _Akey) => (null))) => ((m2: t<_Akey,_Avalue>) => ((k: _Akey) => (null)));

export const lemma_SelConcat2 = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => ((_1: _Akey) => (null))) => ((m2: t<_Akey,_Avalue>) => ((k: _Akey) => (null)));

export const lemma_InDomUpd1 = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Akey) => ((_1: _Avalue) => (null)))) => ((k1: _Akey) => ((k2: _Akey) => ((v: _Avalue) => (null))));

export const lemma_InDomUpd2 = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Akey) => ((_1: _Avalue) => (null)))) => ((k1: _Akey) => ((k2: _Akey) => ((v: _Avalue) => (null))));

export const lemma_InDomConstMap = <_Akey,_Avalue>(v: _Avalue): ((_1: _Akey) => (null)) => ((k: _Akey) => (null));

export const lemma_InDomConcat = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => ((_1: _Akey) => (null))) => ((m2: t<_Akey,_Avalue>) => ((k: _Akey) => (null)));

export const lemma_InDomRestrict = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: FStar_Set.set<_Akey>) => ((_1: _Akey) => (null))) => ((ks: FStar_Set.set<_Akey>) => ((k: _Akey) => (null)));

export const lemma_ContainsDom = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => (null)) => ((k: _Akey) => (null));

export const lemma_UpdDomain = <_Akey,_Avalue>(m: t<_Akey,_Avalue> ): ((_1: _Akey) => ((_1: _Avalue) => (null))) => ((k: _Akey) => ((v: _Avalue) => (null)));

export type equal<_Akey,_Avalue,_Am1,_Am2> = null;

export const lemma_equal_intro = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => (null)) => ((m2: t<_Akey,_Avalue>) => (null));

export const lemma_equal_elim = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => (null)) => ((m2: t<_Akey,_Avalue>) => (null));

export const lemma_equal_refl = <_Akey,_Avalue>(m1: t<_Akey,_Avalue> ): ((_1: t<_Akey,_Avalue>) => (null)) => ((m2: t<_Akey,_Avalue>) => (null));

export const const_on = <_Akey,_Avalue>(dom: FStar_Set.set<_Akey> ): ((_1: _Avalue) => (t<_Akey,_Avalue> )) => ((v: _Avalue) => (restrict(dom)(_const(v))));

export type disjoint_dom<_Akey,_Avalue,_Am1,_Am2> = null;

export type has_dom<_Akey,_Avalue,_Am,_Adom> = null;


