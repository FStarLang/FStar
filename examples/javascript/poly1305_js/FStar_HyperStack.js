/* @flow */
import * as Prims from "./Prims";
import * as FStar_Heap from "./FStar_Heap";
import * as FStar_Set from "./FStar_Set";
import * as FStar_Map from "./FStar_Map";
import * as FStar_HyperHeap from "./FStar_HyperHeap";
export const is_in = (r: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.t) => (boolean)) => ((h: FStar_HyperHeap.t) => (FStar_Map.contains(h)(r)));

export const is_stack_region = (r: FStar_HyperHeap.rid): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const is_eternal_color = (c: number): (boolean) => ((c <= 0));

export const is_eternal_region = (r: FStar_HyperHeap.rid): (null) => {
  let _res;
  _res = null;
  return _res;
};

export type sid = FStar_HyperHeap.rid;

export const is_above = (r1: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.rid) => (null)) => ((r2: FStar_HyperHeap.rid) => {
  let _res;
  _res = null;
  return _res;
});

export const is_just_below = (r1: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.rid) => (null)) => ((r2: FStar_HyperHeap.rid) => {
  let _res;
  _res = null;
  return _res;
});

export const is_below = (r1: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.rid) => (null)) => ((r2: FStar_HyperHeap.rid) => {
  let _res;
  _res = null;
  return _res;
});

export const is_strictly_below = (r1: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.rid) => (null)) => ((r2: FStar_HyperHeap.rid) => {
  let _res;
  _res = null;
  return _res;
});

export const is_strictly_above = (r1: FStar_HyperHeap.rid): ((_1: FStar_HyperHeap.rid) => (null)) => ((r2: FStar_HyperHeap.rid) => {
  let _res;
  _res = null;
  return _res;
});

export type downward_closed<_Ah> = null;

export type is_tip<_Atip,_Ah> = null;

export type hh = FStar_HyperHeap.t;

export type HS = {_tag: "HS", _0: hh, _1: FStar_HyperHeap.rid};

export type mem = HS;

export const uu___is_HS = (projectee: mem): (boolean) => (true);

export const __proj__HS__item__h = (projectee: mem): (hh) => {
  let _res;
  const _0_136 = projectee;
  if( (_0_136._tag === "HS") ) {
    const h = _0_136._0;
    const tip = _0_136._1;
    _res = h;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export const __proj__HS__item__tip = (projectee: mem): (FStar_HyperHeap.rid) => {
  let _res;
  const _0_137 = projectee;
  if( (_0_137._tag === "HS") ) {
    const h = _0_137._0;
    const tip = _0_137._1;
    _res = tip;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export const empty_mem = (m: FStar_HyperHeap.t): (mem) => ({
  _tag: "HS",
  _0: FStar_Map.upd(FStar_Map.restrict(FStar_Set.empty)(m))(FStar_HyperHeap.root)(FStar_Heap.emp),
  _1: FStar_HyperHeap.root
});

export const test0 = (m: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const test1 = (m: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const test2 = (m: mem): ((_1: sid) => (null)) => ((r: sid) => (null));

export const dc_elim = (h: FStar_HyperHeap.t): ((_1: FStar_HyperHeap.rid) => ((_1: FStar_HyperHeap.rid) => (null))) => ((r: FStar_HyperHeap.rid) => ((s: FStar_HyperHeap.rid) => (null)));

export const test3 = (m: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const test4 = (m: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const eternal_region_does_not_overlap_with_tip = (m: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const poppable = (m: mem): (boolean) => ((__proj__HS__item__tip(m) != FStar_HyperHeap.root));

export const remove_elt = <_Aa>(s: FStar_Set.set<_Aa> ): ((_1: _Aa) => (FStar_Set.set<_Aa> )) => ((x: _Aa) => (FStar_Set.intersect(s)(FStar_Set.complement(FStar_Set.singleton(x)))));

export type popped<_Am0,_Am1> = null;

export const pop = (m0: mem): (null) => {
  let _res;
  _res = null;
  return _res;
};

export type MkRef<_Aa> = {_tag: "MkRef", _0: FStar_HyperHeap.rid, _1: boolean, _2: FStar_HyperHeap.rref<null,_Aa>};

export type reference<_Aa> = MkRef<_Aa> ;

export const uu___is_MkRef = <_Aa>(projectee: reference<_Aa> ): (boolean) => (true);

export const __proj__MkRef__item__id = <_Aa>(projectee: reference<_Aa> ): (FStar_HyperHeap.rid) => {
  let _res;
  const _0_138 = projectee;
  if( (_0_138._tag === "MkRef") ) {
    const id = _0_138._0;
    const mm = _0_138._1;
    const ref = _0_138._2;
    _res = id;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export const __proj__MkRef__item__mm = <_Aa>(projectee: reference<_Aa> ): (boolean) => {
  let _res;
  const _0_139 = projectee;
  if( (_0_139._tag === "MkRef") ) {
    const id = _0_139._0;
    const mm = _0_139._1;
    const ref = _0_139._2;
    _res = mm;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export const __proj__MkRef__item__ref = <_Aa>(projectee: reference<_Aa> ): (FStar_HyperHeap.rref<null,_Aa>) => {
  let _res;
  const _0_140 = projectee;
  if( (_0_140._tag === "MkRef") ) {
    const id = _0_140._0;
    const mm = _0_140._1;
    const ref = _0_140._2;
    _res = ref;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export type stackref<_Aa> = reference<_Aa> ;

export type ref<_Aa> = reference<_Aa> ;

export type mmstackref<_Aa> = reference<_Aa> ;

export type mmref<_Aa> = reference<_Aa> ;

export type live_region<_Am,_Ai> = null;

export type weak_live_region<_Am,_Ai> = null;

export type contains<_Aa,_Am,_As> = null;

const weak_live_region_implies_eternal_or_in_map = (r: FStar_HyperHeap.rid): ((_1: mem) => (null)) => ((m: mem) => (null));
export type weak_contains<_Aa,_Am,_As> = null;

export const upd = <_Aa>(m: mem): ((_1: reference<_Aa>) => ((_1: _Aa) => (null))) => ((s: reference<_Aa>) => ((v: _Aa) => {
  let _res;
  _res = null;
  return _res;
}));

export const sel = <_Aa>(m: mem): ((_1: reference<_Aa>) => (null)) => ((s: reference<_Aa>) => {
  let _res;
  _res = null;
  return _res;
});

export type equal_domains<_Am0,_Am1> = null;

export const lemma_equal_domains_trans = (m0: mem): ((_1: mem) => ((_1: mem) => (null))) => ((m1: mem) => ((m2: mem) => (null)));

export type equal_stack_domains<_Am0,_Am1> = null;

export const lemma_equal_stack_domains_trans = (m0: mem): ((_1: mem) => ((_1: mem) => (null))) => ((m1: mem) => ((m2: mem) => (null)));

export type modifies<_As,_Am0,_Am1> = null;

export type modifies_transitively<_As,_Am0,_Am1> = null;

export const heap_only = (m0: mem): (boolean) => ((__proj__HS__item__tip(m0) == FStar_HyperHeap.root));

export const top_frame = (m: mem): (FStar_Heap.heap) => (FStar_Map.sel(__proj__HS__item__h(m))(__proj__HS__item__tip(m)));

export type fresh_frame<_Am0,_Am1> = null;

export const modifies_drop_tip = (m0: mem): ((_1: mem) => ((_1: mem) => ((_1: FStar_Set.set<FStar_HyperHeap.rid>) => (null)))) => ((m1: mem) => ((m2: mem) => ((s: FStar_Set.set<FStar_HyperHeap.rid>) => (null))));

export const lemma_pop_is_popped = (m0: mem): (null) => (null);

export type s_ref<_Ai,_Aa> = reference<_Aa> ;

export const frameOf = <_Aa>(s: reference<_Aa> ): (FStar_HyperHeap.rid) => (__proj__MkRef__item__id(s));

export const as_ref = <_Aa>(x: reference<_Aa> ): (null) => {
  let _res;
  _res = null;
  return _res;
};

export const as_aref = <_Aa>(x: reference<_Aa> ): (null) => {
  let _res;
  _res = null;
  return _res;
};

export type modifies_one<_Aid,_Ah0,_Ah1> = null;

export type modifies_ref<_Aid,_As,_Ah0,_Ah1> = null;

export const lemma_upd_1 = <_Aa>(h: mem): ((_1: reference<_Aa>) => ((_1: _Aa) => (null))) => ((x: reference<_Aa>) => ((v: _Aa) => (null)));

export const lemma_upd_2 = <_Aa>(h: mem): ((_1: reference<_Aa>) => ((_1: _Aa) => (null))) => ((x: reference<_Aa>) => ((v: _Aa) => (null)));

export const lemma_live_1 = <_Aa,_Aa_>(h: mem): ((_1: reference<_Aa>) => ((_1: reference<_Aa_>) => (null))) => ((x: reference<_Aa>) => ((x_: reference<_Aa_>) => (null)));

export const above_tip_is_live = <_Aa>(m: mem): ((_1: reference<_Aa>) => (null)) => ((x: reference<_Aa>) => (null));

export const contains_implies_weak_contains = <_Aa>(h: mem): ((_1: reference<_Aa>) => (null)) => ((x: reference<_Aa>) => (null));

export type Ref = {_tag: "Ref", _0: null, _1: reference<any>};

export type some_ref = Ref;

export const uu___is_Ref = (projectee: some_ref): (boolean) => (true);

export type __proj__Ref__item__a<_Aprojectee> = any;

export const __proj__Ref__item___1 = (projectee: some_ref): (reference<__proj__Ref__item__a<null>>) => {
  let _res;
  const _0_141 = projectee;
  if( (_0_141._tag === "Ref") ) {
    const a = _0_141._0;
    const _1 = _0_141._1;
    _res = _1;
  } else {
    throw "This value doesn\'t match!";
  }
  return _res;
};

export type some_refs = Prims.list<some_ref> ;

export const regions_of_some_refs = (rs: some_refs): (FStar_Set.set<FStar_HyperHeap.rid>) => {
  let _res;
  const _0_142 = rs;
  if( (_0_142.length == 0) ) {
    _res = FStar_Set.empty;
  } else {
    if( (_0_142.length > 0) ) {
      const _0_143 = _0_142[0];
      if( (_0_143._tag === "Ref") ) {
        const uu____1872 = _0_143._0;
        const r = _0_143._1;
        const tl = _0_142.slice(1);
        _res = FStar_Set.union(FStar_Set.singleton(__proj__MkRef__item__id(r)))(regions_of_some_refs(tl));
      } else {
        throw "This value doesn\'t match!";
      }
    } else {
      throw "This value doesn\'t match!";
    }
  }
  return _res;
};

export const refs_in_region = (r: FStar_HyperHeap.rid): ((_1: some_refs) => (null)) => ((rs: some_refs) => {
  let _res;
  _res = null;
  return _res;
});

export type mods<_Ars,_Ah0,_Ah1> = null;

export const eternal_disjoint_from_tip = (h: mem): ((_1: FStar_HyperHeap.rid) => (null)) => ((r: FStar_HyperHeap.rid) => (null));

export const f = <_Aa,_Ab>(x: reference<_Aa> ): ((_1: reference<_Aa>) => ((_1: reference<_Ab>) => ((_1: reference<number>) => ((_1: mem) => ((_1: mem) => (null)))))) => ((x_: reference<_Aa>) => ((y: reference<_Ab>) => ((z: reference<number>) => ((h0: mem) => ((h1: mem) => (null))))));


