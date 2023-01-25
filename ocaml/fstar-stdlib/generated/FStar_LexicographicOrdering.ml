open Prims
type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) lex_t =
  | Left_lex of 'a * 'a * 'b * 'b * 'rua 
  | Right_lex of 'a * 'b * 'b * 'rub 
let uu___is_Left_lex :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Left_lex (x1, x2, y1, y2, _4) -> true
        | uu___2 -> false
let __proj__Left_lex__item__x1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x1
let __proj__Left_lex__item__x2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> x2
let __proj__Left_lex__item__y1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y1
let __proj__Left_lex__item__y2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> y2
let __proj__Left_lex__item___4 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'rua
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with | Left_lex (x1, x2, y1, y2, _4) -> _4
let uu___is_Right_lex :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Right_lex (x, y1, y2, _3) -> true
        | uu___2 -> false
let __proj__Right_lex__item__x :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> x
let __proj__Right_lex__item__y1 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> y1
let __proj__Right_lex__item__y2 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 -> ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> y2
let __proj__Right_lex__item___3 :
  'a 'b 'rua 'rub .
    ('a, 'b) Prims.dtuple2 ->
      ('a, 'b) Prims.dtuple2 ->
        ('a, 'b, 'rua, 'rub, unit, unit) lex_t -> 'rub
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_lex (x, y1, y2, _3) -> _3

type ('a, 'b, 'rua, 'rub, 'uuuuu, 'uuuuu1) lex_aux = Obj.t
type ('a, 'b, 'rua, 'rub, 'wfua, 'wfub, 'uuuuu, 'uuuuu1) lex = Obj.t
let tuple_to_dep_tuple : 'a 'b . ('a * 'b) -> ('a, 'b) Prims.dtuple2 =
  fun x ->
    Prims.Mkdtuple2
      ((FStar_Pervasives_Native.fst x), (FStar_Pervasives_Native.snd x))
type ('a, 'b, 'rua, 'rub, 'x, 'y) lex_t_non_dep =
  ('a, 'b, 'rua, 'rub, unit, unit) lex_t

type ('a, 'b, 'rua, 'rub, 'dummyV0, 'dummyV1) sym =
  | Left_sym of 'a * 'a * 'b * 'rua 
  | Right_sym of 'a * 'b * 'b * 'rub 
let uu___is_Left_sym :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Left_sym (x1, x2, y, _3) -> true
        | uu___2 -> false
let __proj__Left_sym__item__x1 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> x1
let __proj__Left_sym__item__x2 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> x2
let __proj__Left_sym__item__y :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> y
let __proj__Left_sym__item___3 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'rua
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Left_sym (x1, x2, y, _3) -> _3
let uu___is_Right_sym :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee ->
        match projectee with
        | Right_sym (x, y1, y2, _3) -> true
        | uu___2 -> false
let __proj__Right_sym__item__x :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> x
let __proj__Right_sym__item__y1 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> y1
let __proj__Right_sym__item__y2 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'b
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> y2
let __proj__Right_sym__item___3 :
  'a 'b 'rua 'rub .
    ('a * 'b) -> ('a * 'b) -> ('a, 'b, 'rua, 'rub, unit, unit) sym -> 'rub
  =
  fun uu___ ->
    fun uu___1 ->
      fun projectee -> match projectee with | Right_sym (x, y1, y2, _3) -> _3
let sym_sub_lex :
  'a 'b 'rua 'rub .
    ('a * 'b) ->
      ('a * 'b) ->
        ('a, 'b, 'rua, 'rub, unit, unit) sym ->
          ('a, 'b, 'rua, 'rub, unit, unit) lex_t_non_dep
  =
  fun t1 ->
    fun t2 ->
      fun p ->
        match p with
        | Left_sym (x1, x2, y, p1) -> Left_lex (x1, x2, y, y, p1)
        | Right_sym (x, y1, y2, p1) -> Right_lex (x, y1, y2, p1)
