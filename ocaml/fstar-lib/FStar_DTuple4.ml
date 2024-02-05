type ('a, 'b, 'c, 'd) dtuple4 =
  | Mkdtuple4 of 'a * 'b * 'c * 'd 
let uu___is_Mkdtuple4 : 'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> Prims.bool
  = fun projectee -> true
let __proj__Mkdtuple4__item___1 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'a =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _1
let __proj__Mkdtuple4__item___2 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'b =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _2
let __proj__Mkdtuple4__item___3 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'c =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _3
let __proj__Mkdtuple4__item___4 :
  'a 'b 'c 'd . ('a, 'b, 'c, 'd) dtuple4 -> 'd =
  fun projectee -> match projectee with | Mkdtuple4 (_1, _2, _3, _4) -> _4
