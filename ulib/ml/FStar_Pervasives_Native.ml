
type nonrec 'a option = 'a option =
  | None
  | Some of 'a

let uu___is_None = function None -> true | _ -> false
let uu___is_Some = function Some _ -> true | _ -> false
let __proj__Some_v = function Some x -> x | _ -> assert false

(* 'a * 'b *)
type ('a,'b) tuple2 = 'a * 'b

let fst = Pervasives.fst
let snd = Pervasives.snd

let __proj__Mktuple2__1 = fst
let __proj__Mktuple2__2 = snd

type ('a,'b,'c) tuple3 =
 'a* 'b* 'c
let uu___is_Mktuple3 projectee = true
let __proj__Mktuple3__item___1 projectee =
  match projectee with | (_1,_2,_3) -> _1
let __proj__Mktuple3__item___2 projectee =
  match projectee with | (_1,_2,_3) -> _2
let __proj__Mktuple3__item___3 projectee =
  match projectee with | (_1,_2,_3) -> _3
type ('a,'b,'c,'d) tuple4 =
 'a* 'b* 'c* 'd
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
 'a* 'b* 'c* 'd* 'e
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
 'a* 'b* 'c* 'd* 'e* 'f
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
 'a* 'b* 'c* 'd* 'e* 'f* 'g
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
 'a* 'b* 'c* 'd* 'e* 'f* 'g* 'h
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
