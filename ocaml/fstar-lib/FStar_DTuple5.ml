type ('a, 'b, 'c, 'd, 'e) dtuple5 =
  | Mkdtuple5 of 'a * 'b * 'c * 'd * 'e 
let uu___is_Mkdtuple5 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> Prims.bool =
  fun projectee -> true
let __proj__Mkdtuple5__item___1 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'a =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _1
let __proj__Mkdtuple5__item___2 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'b =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _2
let __proj__Mkdtuple5__item___3 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'c =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _3
let __proj__Mkdtuple5__item___4 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'd =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _4
let __proj__Mkdtuple5__item___5 :
  'a 'b 'c 'd 'e . ('a, 'b, 'c, 'd, 'e) dtuple5 -> 'e =
  fun projectee ->
    match projectee with | Mkdtuple5 (_1, _2, _3, _4, _5) -> _5
