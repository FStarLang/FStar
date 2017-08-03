open Prims
type 'Aheap st_pre_h = 'Aheap -> Obj.t
type ('Aheap,'Aa) st_post_h = 'Aa -> 'Aheap -> Obj.t
type ('Aheap,'Aa) st_wp_h = Prims.unit -> 'Aheap st_pre_h
type ('Aheap,'Aa,'Ax,'Ap,'Auu____55) st_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) st_bind_wp = 'Awp1
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) st_if_then_else =
  Prims.unit
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) st_ite_wp = Prims.unit
type ('Aheap,'Aa,'Awp1,'Awp2) st_stronger = Prims.unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) st_close_wp = Prims.unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) st_assert_p = Prims.unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) st_assume_p = Prims.unit
type ('Aheap,'Aa,'Ap,'Ah) st_null_wp = Prims.unit
type ('Aheap,'Aa,'Awp) st_trivial = Prims.unit
type 'Aa result =
  | V of 'Aa
  | E of Prims.exn
  | Err of Prims.string
let uu___is_V: 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | V v -> true | uu____548 -> false
let __proj__V__item__v: 'Aa . 'Aa result -> 'Aa =
  fun projectee  -> match projectee with | V v -> v
let uu___is_E: 'Aa . 'Aa result -> Prims.bool =
  fun projectee  -> match projectee with | E e -> true | uu____582 -> false
let __proj__E__item__e: 'Aa . 'Aa result -> Prims.exn =
  fun projectee  -> match projectee with | E e -> e
let uu___is_Err: 'Aa . 'Aa result -> Prims.bool =
  fun projectee  ->
    match projectee with | Err msg -> true | uu____616 -> false
let __proj__Err__item__msg: 'Aa . 'Aa result -> Prims.string =
  fun projectee  -> match projectee with | Err msg -> msg
type ex_pre = Obj.t
type 'Aa ex_post = 'Aa result -> Obj.t
type 'Aa ex_wp = Prims.unit -> ex_pre
type ('Aa,'Ax,'Ap) ex_return = 'Ap
type ('Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap) ex_bind_wp = Prims.unit
type ('Aa,'Awp,'Apost) ex_ite_wp = Prims.unit
type ('Aa,'Ap,'Awp_then,'Awp_else,'Apost) ex_if_then_else = Prims.unit
type ('Aa,'Awp1,'Awp2) ex_stronger = Prims.unit
type ('Aa,'Ab,'Awp,'Ap) ex_close_wp = Prims.unit
type ('Aa,'Aq,'Awp,'Ap) ex_assert_p = Prims.unit
type ('Aa,'Aq,'Awp,'Ap) ex_assume_p = Prims.unit
type ('Aa,'Ap) ex_null_wp = Prims.unit
type ('Aa,'Awp) ex_trivial = 'Awp
type ('Aa,'Awp,'Ap) lift_div_exn = 'Awp
type 'Ah all_pre_h = 'Ah -> Obj.t
type ('Ah,'Aa) all_post_h = 'Aa result -> 'Ah -> Obj.t
type ('Ah,'Aa) all_wp_h = Prims.unit -> 'Ah all_pre_h
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) all_ite_wp = Prims.unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu____1149) all_return = 'Ap
type ('Aheap,'Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap,'Ah0) all_bind_wp = 'Awp1
type ('Aheap,'Aa,'Ap,'Awp_then,'Awp_else,'Apost,'Ah0) all_if_then_else =
  Prims.unit
type ('Aheap,'Aa,'Awp1,'Awp2) all_stronger = Prims.unit
type ('Aheap,'Aa,'Ab,'Awp,'Ap,'Ah) all_close_wp = Prims.unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) all_assert_p = Prims.unit
type ('Aheap,'Aa,'Ap,'Awp,'Aq,'Ah) all_assume_p = Prims.unit
type ('Aheap,'Aa,'Ap,'Ah0) all_null_wp = Prims.unit
type ('Aheap,'Aa,'Awp) all_trivial = Prims.unit
type 'Aa inversion = Prims.unit
let allow_inversion: 'Aa . Prims.unit = ()
let invertOption: 'Aa . Prims.unit -> Prims.unit = fun uu____1543  -> ()
type ('a,'b) either =
  | Inl of 'a
  | Inr of 'b
let uu___is_Inl: 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  ->
    match projectee with | Inl v -> true | uu____1589 -> false
let __proj__Inl__item__v: 'a 'b . ('a,'b) either -> 'a =
  fun projectee  -> match projectee with | Inl v -> v
let uu___is_Inr: 'a 'b . ('a,'b) either -> Prims.bool =
  fun projectee  ->
    match projectee with | Inr v -> true | uu____1639 -> false
let __proj__Inr__item__v: 'a 'b . ('a,'b) either -> 'b =
  fun projectee  -> match projectee with | Inr v -> v
let dfst: 'Aa 'Ab . ('Aa,'Ab) Prims.dtuple2 -> 'Aa =
  fun t  -> Prims.__proj__Mkdtuple2__item___1 t
let dsnd: 'Aa 'Ab . ('Aa,'Ab) Prims.dtuple2 -> 'Ab =
  fun t  -> Prims.__proj__Mkdtuple2__item___2 t
type ('Aa,'Ab,'Ac) dtuple3 =
  | Mkdtuple3 of 'Aa* 'Ab* 'Ac
let uu___is_Mkdtuple3: 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> Prims.bool =
  fun projectee  -> true
let __proj__Mkdtuple3__item___1: 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Aa =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _1
let __proj__Mkdtuple3__item___2: 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Ab =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _2
let __proj__Mkdtuple3__item___3: 'Aa 'Ab 'Ac . ('Aa,'Ab,'Ac) dtuple3 -> 'Ac =
  fun projectee  -> match projectee with | Mkdtuple3 (_1,_2,_3) -> _3
type ('Aa,'Ab,'Ac,'Ad) dtuple4 =
  | Mkdtuple4 of 'Aa* 'Ab* 'Ac* 'Ad
let uu___is_Mkdtuple4:
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> Prims.bool =
  fun projectee  -> true
let __proj__Mkdtuple4__item___1:
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Aa =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _1
let __proj__Mkdtuple4__item___2:
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ab =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _2
let __proj__Mkdtuple4__item___3:
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ac =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _3
let __proj__Mkdtuple4__item___4:
  'Aa 'Ab 'Ac 'Ad . ('Aa,'Ab,'Ac,'Ad) dtuple4 -> 'Ad =
  fun projectee  -> match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _4
let ignore: 'Aa . 'Aa -> Prims.unit = fun x  -> ()
let rec false_elim: 'Aa . Prims.unit -> 'Aa = fun u  -> false_elim ()
type __internal_ocaml_attributes =
  | PpxDerivingShow
  | PpxDerivingShowConstant of Prims.string
let uu___is_PpxDerivingShow: __internal_ocaml_attributes -> Prims.bool =
  fun projectee  ->
    match projectee with | PpxDerivingShow  -> true | uu____2259 -> false
let uu___is_PpxDerivingShowConstant:
  __internal_ocaml_attributes -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PpxDerivingShowConstant _0 -> true
    | uu____2265 -> false
let __proj__PpxDerivingShowConstant__item___0:
  __internal_ocaml_attributes -> Prims.string =
  fun projectee  -> match projectee with | PpxDerivingShowConstant _0 -> _0