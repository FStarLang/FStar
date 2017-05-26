open Prims
type 'Aheap st_pre_h = 'Aheap -> Obj.t
type ('Aheap,'Aa) st_post_h = 'Aa -> 'Aheap -> Obj.t
type ('Aheap,'Aa) st_wp_h = Prims.unit -> 'Aheap st_pre_h
type ('Aheap,'Aa,'Ax,'Ap,'Auu____49) st_return = 'Ap
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
let uu___is_V projectee =
  match projectee with | V v -> true | uu____378 -> false
let __proj__V__item__v projectee = match projectee with | V v -> v
let uu___is_E projectee =
  match projectee with | E e -> true | uu____403 -> false
let __proj__E__item__e projectee = match projectee with | E e -> e
let uu___is_Err projectee =
  match projectee with | Err msg -> true | uu____428 -> false
let __proj__Err__item__msg projectee = match projectee with | Err msg -> msg
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
let raise uu____700 = failwith "Not yet implemented:raise"
type 'Ah all_pre_h = 'Ah -> Obj.t
type ('Ah,'Aa) all_post_h = 'Aa result -> 'Ah -> Obj.t
type ('Ah,'Aa) all_wp_h = Prims.unit -> 'Ah all_pre_h
type ('Aheap,'Aa,'Awp,'Apost,'Ah0) all_ite_wp = Prims.unit
type ('Aheap,'Aa,'Ax,'Ap,'Auu____805) all_return = 'Ap
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
let allow_inversion = ()
let uu___is_None projectee =
  match projectee with | None  -> true | uu____1080 -> false
let uu___is_Some projectee =
  match projectee with | Some v -> true | uu____1092 -> false
let __proj__Some__item__v projectee = match projectee with | Some v -> v
let invertOption uu____1109 = ()
type ('a,'b) either =
  | Inl of 'a
  | Inr of 'b
let uu___is_Inl projectee =
  match projectee with | Inl v -> true | uu____1141 -> false
let __proj__Inl__item__v projectee = match projectee with | Inl v -> v
let uu___is_Inr projectee =
  match projectee with | Inr v -> true | uu____1175 -> false
let __proj__Inr__item__v projectee = match projectee with | Inr v -> v
type ('a,'b) tuple2 =
  | Mktuple2 of 'a* 'b
let uu___is_Mktuple2 projectee = true
let __proj__Mktuple2__item___1 projectee =
  match projectee with | (_1,_2) -> _1
let __proj__Mktuple2__item___2 projectee =
  match projectee with | (_1,_2) -> _2
let fst x = __proj__Mktuple2__item___1 x
let snd x = __proj__Mktuple2__item___2 x
type ('a,'b,'c) tuple3 =
  | Mktuple3 of 'a* 'b* 'c
let uu___is_Mktuple3 projectee = true
let __proj__Mktuple3__item___1 projectee =
  match projectee with | (_1,_2,_3) -> _1
let __proj__Mktuple3__item___2 projectee =
  match projectee with | (_1,_2,_3) -> _2
let __proj__Mktuple3__item___3 projectee =
  match projectee with | (_1,_2,_3) -> _3
type ('a,'b,'c,'d) tuple4 =
  | Mktuple4 of 'a* 'b* 'c* 'd
let uu___is_Mktuple4 projectee = true
let __proj__Mktuple4__item___1 projectee =
  match projectee with | (_1,_2,_3,_4) -> _1
let __proj__Mktuple4__item___2 projectee =
  match projectee with | (_1,_2,_3,_4) -> _2
let __proj__Mktuple4__item___3 projectee =
  match projectee with | (_1,_2,_3,_4) -> _3
let __proj__Mktuple4__item___4 projectee =
  match projectee with | (_1,_2,_3,_4) -> _4
type ('a,'b,'c,'d,'e) tuple5 =
  | Mktuple5 of 'a* 'b* 'c* 'd* 'e
let uu___is_Mktuple5 projectee = true
let __proj__Mktuple5__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _1
let __proj__Mktuple5__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _2
let __proj__Mktuple5__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _3
let __proj__Mktuple5__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _4
let __proj__Mktuple5__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5) -> _5
type ('a,'b,'c,'d,'e,'f) tuple6 =
  | Mktuple6 of 'a* 'b* 'c* 'd* 'e* 'f
let uu___is_Mktuple6 projectee = true
let __proj__Mktuple6__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _1
let __proj__Mktuple6__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _2
let __proj__Mktuple6__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _3
let __proj__Mktuple6__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _4
let __proj__Mktuple6__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _5
let __proj__Mktuple6__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6) -> _6
type ('a,'b,'c,'d,'e,'f,'g) tuple7 =
  | Mktuple7 of 'a* 'b* 'c* 'd* 'e* 'f* 'g
let uu___is_Mktuple7 projectee = true
let __proj__Mktuple7__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _1
let __proj__Mktuple7__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _2
let __proj__Mktuple7__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _3
let __proj__Mktuple7__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _4
let __proj__Mktuple7__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _5
let __proj__Mktuple7__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _6
let __proj__Mktuple7__item___7 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7) -> _7
type ('a,'b,'c,'d,'e,'f,'g,'h) tuple8 =
  | Mktuple8 of 'a* 'b* 'c* 'd* 'e* 'f* 'g* 'h
let uu___is_Mktuple8 projectee = true
let __proj__Mktuple8__item___1 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _1
let __proj__Mktuple8__item___2 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _2
let __proj__Mktuple8__item___3 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _3
let __proj__Mktuple8__item___4 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _4
let __proj__Mktuple8__item___5 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _5
let __proj__Mktuple8__item___6 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _6
let __proj__Mktuple8__item___7 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _7
let __proj__Mktuple8__item___8 projectee =
  match projectee with | (_1,_2,_3,_4,_5,_6,_7,_8) -> _8
let dfst t = Prims.__proj__Mkdtuple2__item___1 t
let dsnd t = Prims.__proj__Mkdtuple2__item___2 t
type ('Aa,'Ab,'Ac) dtuple3 =
  | Mkdtuple3 of 'Aa* 'Ab* 'Ac
let uu___is_Mkdtuple3 projectee = true
let __proj__Mkdtuple3__item___1 projectee =
  match projectee with | Mkdtuple3 (_1,_2,_3) -> _1
let __proj__Mkdtuple3__item___2 projectee =
  match projectee with | Mkdtuple3 (_1,_2,_3) -> _2
let __proj__Mkdtuple3__item___3 projectee =
  match projectee with | Mkdtuple3 (_1,_2,_3) -> _3
type ('Aa,'Ab,'Ac,'Ad) dtuple4 =
  | Mkdtuple4 of 'Aa* 'Ab* 'Ac* 'Ad
let uu___is_Mkdtuple4 projectee = true
let __proj__Mkdtuple4__item___1 projectee =
  match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _1
let __proj__Mkdtuple4__item___2 projectee =
  match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _2
let __proj__Mkdtuple4__item___3 projectee =
  match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _3
let __proj__Mkdtuple4__item___4 projectee =
  match projectee with | Mkdtuple4 (_1,_2,_3,_4) -> _4
type ('Aa,'Ab,'Ac,'Ad,'Ae) dtuple5 =
  | Mkdtuple5 of 'Aa* 'Ab* 'Ac* 'Ad* 'Ae
let uu___is_Mkdtuple5 projectee = true
let __proj__Mkdtuple5__item___1 projectee =
  match projectee with | Mkdtuple5 (_1,_2,_3,_4,_5) -> _1
let __proj__Mkdtuple5__item___2 projectee =
  match projectee with | Mkdtuple5 (_1,_2,_3,_4,_5) -> _2
let __proj__Mkdtuple5__item___3 projectee =
  match projectee with | Mkdtuple5 (_1,_2,_3,_4,_5) -> _3
let __proj__Mkdtuple5__item___4 projectee =
  match projectee with | Mkdtuple5 (_1,_2,_3,_4,_5) -> _4
let __proj__Mkdtuple5__item___5 projectee =
  match projectee with | Mkdtuple5 (_1,_2,_3,_4,_5) -> _5
type ('Aa,'Ab,'Ac,'Ad,'Ae,'Af) dtuple6 =
  | Mkdtuple6 of 'Aa* 'Ab* 'Ac* 'Ad* 'Ae* 'Af
let uu___is_Mkdtuple6 projectee = true
let __proj__Mkdtuple6__item___1 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _1
let __proj__Mkdtuple6__item___2 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _2
let __proj__Mkdtuple6__item___3 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _3
let __proj__Mkdtuple6__item___4 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _4
let __proj__Mkdtuple6__item___5 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _5
let __proj__Mkdtuple6__item___6 projectee =
  match projectee with | Mkdtuple6 (_1,_2,_3,_4,_5,_6) -> _6
type ('Aa,'Ab,'Ac,'Ad,'Ae,'Af,'Ag) dtuple7 =
  | Mkdtuple7 of 'Aa* 'Ab* 'Ac* 'Ad* 'Ae* 'Af* 'Ag
let uu___is_Mkdtuple7 projectee = true
let __proj__Mkdtuple7__item___1 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _1
let __proj__Mkdtuple7__item___2 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _2
let __proj__Mkdtuple7__item___3 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _3
let __proj__Mkdtuple7__item___4 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _4
let __proj__Mkdtuple7__item___5 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _5
let __proj__Mkdtuple7__item___6 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _6
let __proj__Mkdtuple7__item___7 projectee =
  match projectee with | Mkdtuple7 (_1,_2,_3,_4,_5,_6,_7) -> _7
type ('Aa,'Ab,'Ac,'Ad,'Ae,'Af,'Ag,'Ah) dtuple8 =
  | Mkdtuple8 of 'Aa* 'Ab* 'Ac* 'Ad* 'Ae* 'Af* 'Ag* 'Ah
let uu___is_Mkdtuple8 projectee = true
let __proj__Mkdtuple8__item___1 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _1
let __proj__Mkdtuple8__item___2 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _2
let __proj__Mkdtuple8__item___3 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _3
let __proj__Mkdtuple8__item___4 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _4
let __proj__Mkdtuple8__item___5 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _5
let __proj__Mkdtuple8__item___6 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _6
let __proj__Mkdtuple8__item___7 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _7
let __proj__Mkdtuple8__item___8 projectee =
  match projectee with | Mkdtuple8 (_1,_2,_3,_4,_5,_6,_7,_8) -> _8
let ignore x = ()
let rec false_elim u = false_elim ()