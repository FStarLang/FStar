open Fstarcompiler
open Prims
type pattern = unit


type eqtype_u = unit
type 'p spinoff = 'p
let id (x : 'a) : 'a= x
type ('a, 'uuuuu) trivial_pure_post = unit
type ('uuuuu, 'uuuuu1) ambient = unit
type ('a, 'x, 'uuuuu) pure_return = unit
type ('a, 'b, 'wp1, 'wp2, 'uuuuu) pure_bind_wp = 'wp1
type ('a, 'p, 'wputhen, 'wpuelse, 'uuuuu) pure_if_then_else = unit
type ('a, 'wp, 'uuuuu) pure_ite_wp = unit
type ('a, 'b, 'wp, 'uuuuu) pure_close_wp = unit
type ('a, 'uuuuu) pure_null_wp = unit
type ('p, 'uuuuu) pure_assert_wp = unit
type ('p, 'uuuuu) pure_assume_wp = unit
type ('a, 'wp, 'uuuuu) pure_wp_intro = 'wp
type ('a, 'pre, 'post, 'uuuuu) div_hoare_to_wp = unit
type 'heap st_pre_h = unit
type ('heap, 'a, 'pre) st_post_h' = unit
type ('heap, 'a) st_post_h = unit
type ('heap, 'a) st_wp_h = unit
type ('heap, 'a, 'x, 'p, 'uuuuu) st_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) st_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) st_if_then_else = unit
type ('heap, 'a, 'wp, 'post, 'h0) st_ite_wp = unit
type ('heap, 'a, 'wp1, 'wp2) st_stronger = unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) st_close_wp = unit
type ('heap, 'a, 'wp) st_trivial = unit
type 'a result =
  | V of 'a 
  | E of Prims.exn 
  | Err of Prims.string 
let uu___is_V (projectee : 'a result) : Prims.bool=
  match projectee with | V v -> true | uu___ -> false
let __proj__V__item__v (projectee : 'a result) : 'a=
  match projectee with | V v -> v
let uu___is_E (projectee : 'a result) : Prims.bool=
  match projectee with | E e -> true | uu___ -> false
let __proj__E__item__e (projectee : 'a result) : Prims.exn=
  match projectee with | E e -> e
let uu___is_Err (projectee : 'a result) : Prims.bool=
  match projectee with | Err msg -> true | uu___ -> false
let __proj__Err__item__msg (projectee : 'a result) : Prims.string=
  match projectee with | Err msg -> msg
type ex_pre = unit
type ('a, 'pre) ex_post' = unit
type 'a ex_post = unit
type 'a ex_wp = unit
type ('a, 'x, 'p) ex_return = 'p
type ('a, 'b, 'wp1, 'wp2, 'p) ex_bind_wp = unit
type ('a, 'p, 'wputhen, 'wpuelse, 'post) ex_if_then_else = unit
type ('a, 'wp, 'post) ex_ite_wp = unit
type ('a, 'wp1, 'wp2) ex_stronger = unit
type ('a, 'b, 'wp, 'p) ex_close_wp = unit
type ('a, 'wp) ex_trivial = 'wp
type ('a, 'wp, 'p) lift_div_exn = 'wp
type 'h all_pre_h = unit
type ('h, 'a, 'pre) all_post_h' = unit
type ('h, 'a) all_post_h = unit
type ('h, 'a) all_wp_h = unit
type ('heap, 'a, 'x, 'p, 'uuuuu) all_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) all_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) all_if_then_else = unit
type ('heap, 'a, 'wp, 'post, 'h0) all_ite_wp = unit
type ('heap, 'a, 'wp1, 'wp2) all_stronger = unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) all_close_wp = unit
type ('heap, 'a, 'wp) all_trivial = unit
type 'uuuuu inversion = unit
type ('a, 'b) either =
  | Inl of 'a 
  | Inr of 'b 
let uu___is_Inl (projectee : ('a, 'b) Fstarcompiler.FStar_Pervasives.either)
  : Prims.bool=
  match projectee with
  | Fstarcompiler.FStar_Pervasives.Inl v -> true
  | uu___ -> false
let __proj__Inl__item__v
  (projectee : ('a, 'b) Fstarcompiler.FStar_Pervasives.either) : 'a=
  match projectee with | Fstarcompiler.FStar_Pervasives.Inl v -> v
let uu___is_Inr (projectee : ('a, 'b) Fstarcompiler.FStar_Pervasives.either)
  : Prims.bool=
  match projectee with
  | Fstarcompiler.FStar_Pervasives.Inr v -> true
  | uu___ -> false
let __proj__Inr__item__v
  (projectee : ('a, 'b) Fstarcompiler.FStar_Pervasives.either) : 'b=
  match projectee with | Fstarcompiler.FStar_Pervasives.Inr v -> v
let dfst (t : ('a, 'b) Fstarcompiler.Prims.dtuple2) : 'a=
  Prims.__proj__Mkdtuple2__item___1 t
let dsnd (t : ('a, 'b) Fstarcompiler.Prims.dtuple2) : 'b=
  Prims.__proj__Mkdtuple2__item___2 t
type ('a, 'b, 'c) dtuple3 =
  | Mkdtuple3 of 'a * 'b * 'c 
let uu___is_Mkdtuple3 (projectee : ('a, 'b, 'c) dtuple3) : Prims.bool= true
let __proj__Mkdtuple3__item___1 (projectee : ('a, 'b, 'c) dtuple3) : 
  'a= match projectee with | Mkdtuple3 (_1, _2, _3) -> _1
let __proj__Mkdtuple3__item___2 (projectee : ('a, 'b, 'c) dtuple3) : 
  'b= match projectee with | Mkdtuple3 (_1, _2, _3) -> _2
let __proj__Mkdtuple3__item___3 (projectee : ('a, 'b, 'c) dtuple3) : 
  'c= match projectee with | Mkdtuple3 (_1, _2, _3) -> _3
type ('a, 'b, 'c, 'd) dtuple4 =
  | Mkdtuple4 of 'a * 'b * 'c * 'd 
let uu___is_Mkdtuple4 (projectee : ('a, 'b, 'c, 'd) dtuple4) : Prims.bool=
  true
let __proj__Mkdtuple4__item___1 (projectee : ('a, 'b, 'c, 'd) dtuple4) : 
  'a= match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _1
let __proj__Mkdtuple4__item___2 (projectee : ('a, 'b, 'c, 'd) dtuple4) : 
  'b= match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _2
let __proj__Mkdtuple4__item___3 (projectee : ('a, 'b, 'c, 'd) dtuple4) : 
  'c= match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _3
let __proj__Mkdtuple4__item___4 (projectee : ('a, 'b, 'c, 'd) dtuple4) : 
  'd= match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _4
type ('a, 'b, 'c, 'd, 'e) dtuple5 =
  | Mkdtuple5 of 'a * 'b * 'c * 'd * 'e 
let uu___is_Mkdtuple5 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  Prims.bool= true
let __proj__Mkdtuple5__item___1 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  'a= match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _1
let __proj__Mkdtuple5__item___2 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  'b= match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _2
let __proj__Mkdtuple5__item___3 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  'c= match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _3
let __proj__Mkdtuple5__item___4 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  'd= match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _4
let __proj__Mkdtuple5__item___5 (projectee : ('a, 'b, 'c, 'd, 'e) dtuple5) :
  'e= match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _5
let rec false_elim : 'uuuuu . unit -> 'uuuuu = fun uu___ -> false_elim ()
let singleton (x : 'uuuuu) : 'uuuuu= x
type 'a eqtype_as_type = 'a
let coerce_eq (uu___1 : unit) (uu___ : 'a) : 'b=
  (fun uu___ x -> Obj.magic x) uu___1 uu___
