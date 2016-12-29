/* @flow */
export type erased<_Aa> = _Aa;

export const reveal = <_Aa>(x: erased<_Aa>) => {
  let _res;
  _res = null;
  return _res;
};

export const hide = <_Aa>(x: _Aa): (erased<_Aa>) => (x);

export const lemma_hide_reveal = <_Aa>(x: erased<_Aa>) => (null);

export const as_ghost = <_Aa>(f: (_1: null) => (_Aa)): (erased<_Aa>) => (f(null));

export const elift1 = <_Aa,_Ab>(f: (_1: _Aa) => (null)) => ((ga: erased<_Aa>) => {
  let _res;
  _res = null;
  return _res;
});

export const elift2 = <_Aa,_Ab,_Ac>(f: (_1: _Aa) => ((_1: _Ac) => (null))) => ((ga: erased<_Aa>) => ((gc: erased<_Ac>) => {
  let _res;
  _res = null;
  return _res;
}));

export const elift3 = <_Aa,_Ab,_Ac,_Ad>(f: (_1: _Aa) => ((_1: _Ac) => ((_1: _Ad) => (null)))) => ((ga: erased<_Aa>) => ((gc: erased<_Ac>) => ((gd: erased<_Ad>) => {
  let _res;
  _res = null;
  return _res;
})));

export const elift1_p = <_Aa,_Ab,_Ap>(f: (_1: _Aa) => (null)) => ((ga: erased<_Aa>) => {
  let _res;
  _res = null;
  return _res;
});

export const elift2_p = <_Aa,_Ac,_Ap,_Ab>(f: (_1: _Aa) => ((_1: _Ac) => (null))) => ((ga: erased<_Aa>) => ((gc: erased<_Ac>) => {
  let _res;
  _res = null;
  return _res;
}));


