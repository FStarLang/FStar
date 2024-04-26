type ('a,'b,'c) tuple3 =
 'a* 'b* 'c
[@@deriving yojson,show]
let uu___is_Mktuple3 projectee = true
let __proj__Mktuple3__item___1 projectee =
  match projectee with | (_1,_2,_3) -> _1
let __proj__Mktuple3__item___2 projectee =
  match projectee with | (_1,_2,_3) -> _2
let __proj__Mktuple3__item___3 projectee =
  match projectee with | (_1,_2,_3) -> _3
