/* @flow */
import * as Prims from "./Prims";
export type set<_Aa> = (_1: _Aa) => (Prims.prop);

export type equal<_Aa,_As1,_As2> = null;

export type mem<_a,_Ax,_As> = _As;

export const empty = <_Aa>(x: _Aa) => (null);

export const singleton = <_a>(x: _a) => ((y: _a) => (null));

export const union = <_a>(s1: set<_a>) => ((s2: set<_a>) => ((x: _a) => (null)));

export const intersect = <_a>(s1: set<_a>) => ((s2: set<_a>) => ((x: _a) => (null)));

export const complement = <_a>(s: set<_a>) => ((x: _a) => (null));

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


