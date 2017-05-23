open Prims
type 'Aa inversion = Prims.unit
let allow_inversion = ()
let invertOption uu____11 = ()
type ('a,'b) either =
  | Inl of 'a
  | Inr of 'b
let uu___is_Inl projectee =
  match projectee with | Inl v -> true | uu____48 -> false
let __proj__Inl__item__v projectee = match projectee with | Inl v -> v
let uu___is_Inr projectee =
  match projectee with | Inr v -> true | uu____92 -> false
let __proj__Inr__item__v projectee = match projectee with | Inr v -> v
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