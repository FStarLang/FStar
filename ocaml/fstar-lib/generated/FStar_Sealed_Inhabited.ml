open Prims
type ('a, 'witness) sealed_ = 'a FStar_Sealed.sealed
type ('a, 'witness, 'x) is_sealed = unit
type ('a, 'witness) sealed = ('a, unit) sealed_
let seal : 'a . 'a -> 'a -> ('a, unit) sealed =
  fun w -> fun x -> FStar_Sealed.seal x