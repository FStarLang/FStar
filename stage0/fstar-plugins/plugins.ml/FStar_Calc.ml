open Fstarcompiler
open Prims
type ('a, 'dummyV0, 'dummyV1, 'dummyV2) calc_chain =
  | CalcRefl of 'a 
  | CalcStep of unit Prims.list * unit * 'a * 'a * 'a * ('a, Obj.t, Obj.t,
  Obj.t) calc_chain * unit 
let uu___is_CalcRefl (uu___ : unit Prims.list) (uu___1 : 'a) (uu___2 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : Prims.bool=
  match projectee with | CalcRefl x -> true | uu___3 -> false
let __proj__CalcRefl__item__x (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : 
  'a= match projectee with | CalcRefl x -> x
let uu___is_CalcStep (uu___ : unit Prims.list) (uu___1 : 'a) (uu___2 : 'a)
  (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : Prims.bool=
  match projectee with
  | CalcStep (rs, p, x, y, z, _5, _6) -> true
  | uu___3 -> false
let __proj__CalcStep__item__rs (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) :
  unit Prims.list=
  match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> rs
let __proj__CalcStep__item__x (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : 
  'a= match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> x
let __proj__CalcStep__item__y (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : 
  'a= match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> y
let __proj__CalcStep__item__z (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) : 
  'a= match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> z
let __proj__CalcStep__item___5 (uu___ : unit Prims.list) (uu___1 : 'a)
  (uu___2 : 'a) (projectee : ('a, Obj.t, Obj.t, Obj.t) calc_chain) :
  ('a, Obj.t, Obj.t, Obj.t) calc_chain=
  match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> _5
type ('a, 'rs, 'x, 'y) calc_chain_related = Obj.t
type ('t, 'rs, 'p) calc_chain_compatible = unit
type ('a, 'rs, 'x, 'y) calc_pack = unit
let _calc_init (x : 'a) : ('a, Obj.t, Obj.t, Obj.t) calc_chain= CalcRefl x


