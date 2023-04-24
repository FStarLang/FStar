open Prims
type sw = FStar_Integers.signed_width
type ('sl, 'l, 's) secret_int = (unit, unit, Obj.t) FStar_IFC.protected
let (promote :
  unit ->
    unit ->
      sw ->
        (unit, unit, unit) secret_int ->
          unit -> (unit, unit, unit) secret_int)
  =
  fun sl ->
    fun l0 ->
      fun s ->
        fun x ->
          fun l1 ->
            FStar_IFC.join () () () ()
              (Obj.magic (FStar_IFC.hide () () () (Obj.magic x)))
type qual =
  | Secret of unit * unit * sw 
  | Public of FStar_Integers.signed_width 
let (uu___is_Secret : qual -> Prims.bool) =
  fun projectee ->
    match projectee with | Secret (sl, l, sw1) -> true | uu___ -> false


let (__proj__Secret__item__sw : qual -> sw) =
  fun projectee -> match projectee with | Secret (sl, l, sw1) -> sw1
let (uu___is_Public : qual -> Prims.bool) =
  fun projectee -> match projectee with | Public sw1 -> true | uu___ -> false
let (__proj__Public__item__sw : qual -> FStar_Integers.signed_width) =
  fun projectee -> match projectee with | Public sw1 -> sw1
let (sw_qual : qual -> FStar_Integers.signed_width) =
  fun uu___ ->
    match uu___ with
    | Secret (uu___1, uu___2, sw1) -> sw1
    | Public sw1 -> sw1

type 'q t = Obj.t
let (as_secret : qual -> Obj.t -> (unit, unit, unit) secret_int) =
  fun uu___1 -> fun uu___ -> (fun q -> fun x -> Obj.magic x) uu___1 uu___
let (as_public : qual -> Obj.t -> Obj.t) = fun q -> fun x -> x