open Prims
type ('a, 'dummyV0, 'dummyV1, 'dummyV2) calc_chain =
  | CalcRefl of 'a 
  | CalcStep of unit Prims.list * unit * 'a * 'a * 'a * ('a, unit, unit,
  unit) calc_chain * unit 
let uu___is_CalcRefl :
  'a .
    unit Prims.list ->
      'a -> 'a -> ('a, unit, unit, unit) calc_chain -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcRefl x -> true | uu___3 -> false
let __proj__CalcRefl__item__x :
  'a . unit Prims.list -> 'a -> 'a -> ('a, unit, unit, unit) calc_chain -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 -> fun projectee -> match projectee with | CalcRefl x -> x
let uu___is_CalcStep :
  'a .
    unit Prims.list ->
      'a -> 'a -> ('a, unit, unit, unit) calc_chain -> Prims.bool
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with
          | CalcStep (rs, p, x, y, z, _5, _6) -> true
          | uu___3 -> false
let __proj__CalcStep__item__rs :
  'a .
    unit Prims.list ->
      'a -> 'a -> ('a, unit, unit, unit) calc_chain -> unit Prims.list
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> rs
let __proj__CalcStep__item__x :
  'a . unit Prims.list -> 'a -> 'a -> ('a, unit, unit, unit) calc_chain -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> x
let __proj__CalcStep__item__y :
  'a . unit Prims.list -> 'a -> 'a -> ('a, unit, unit, unit) calc_chain -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> y
let __proj__CalcStep__item__z :
  'a . unit Prims.list -> 'a -> 'a -> ('a, unit, unit, unit) calc_chain -> 'a
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> z
let __proj__CalcStep__item___5 :
  'a .
    unit Prims.list ->
      'a ->
        'a ->
          ('a, unit, unit, unit) calc_chain ->
            ('a, unit, unit, unit) calc_chain
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun projectee ->
          match projectee with | CalcStep (rs, p, x, y, z, _5, _6) -> _5
type ('a, 'rs, 'x, 'y) calc_chain_related = Obj.t
type ('t, 'rs, 'p) calc_chain_compatible = unit
type ('a, 'rs, 'x, 'y) calc_pack = unit
let _calc_init : 'a . 'a -> ('a, unit, unit, unit) calc_chain =
  fun x -> CalcRefl x

