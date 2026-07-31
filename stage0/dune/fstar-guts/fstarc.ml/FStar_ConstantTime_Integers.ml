open Prims
type sw = FStar_Integers.signed_width
type ('sl, 'l, 's) secret_int = ('sl, 'l, Obj.t) FStar_IFC.protected
let promote (sl : unit) (l0 : unit) (s : sw)
  (x : (Obj.t, Obj.t, Obj.t) secret_int) (l1 : unit) :
  (Obj.t, Obj.t, Obj.t) secret_int=
  FStar_IFC.join () () () ()
    (Obj.magic (FStar_IFC.hide () () () (Obj.magic x)))
type qual =
  | Secret of unit * unit * sw 
  | Public of FStar_Integers.signed_width 
let uu___is_Secret (projectee : qual) : Prims.bool=
  match projectee with | Secret (sl, l, sw1) -> true | uu___ -> false


let __proj__Secret__item__sw (projectee : qual) : sw=
  match projectee with | Secret (sl, l, sw1) -> sw1
let uu___is_Public (projectee : qual) : Prims.bool=
  match projectee with | Public sw1 -> true | uu___ -> false
let __proj__Public__item__sw (projectee : qual) :
  FStar_Integers.signed_width= match projectee with | Public sw1 -> sw1
let sw_qual (uu___ : qual) : FStar_Integers.signed_width=
  match uu___ with | Secret (uu___1, uu___2, sw1) -> sw1 | Public sw1 -> sw1

type 'q t = Obj.t
let as_secret (uu___1 : qual) (uu___ : Obj.t) :
  (Obj.t, Obj.t, Obj.t) secret_int= (fun q x -> Obj.magic x) uu___1 uu___
let as_public (q : qual) (x : Obj.t) : Obj.t= x
