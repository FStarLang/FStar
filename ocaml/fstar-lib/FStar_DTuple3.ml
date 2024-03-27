type ('a, 'b, 'c) dtuple3 =
  | Mkdtuple3 of 'a * 'b * 'c 
let uu___is_Mkdtuple3 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> Prims.bool =
  fun projectee -> true
let __proj__Mkdtuple3__item___1 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'a =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _1
let __proj__Mkdtuple3__item___2 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'b =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _2
let __proj__Mkdtuple3__item___3 : 'a 'b 'c . ('a, 'b, 'c) dtuple3 -> 'c =
  fun projectee -> match projectee with | Mkdtuple3 (_1, _2, _3) -> _3
