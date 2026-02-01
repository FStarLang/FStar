open Fstarcompiler
open Prims
type ('a, 'witness) sealed_ = 'a FStar_Sealed.sealed
type ('a, 'witness, 'x) is_sealed = unit
type ('a, 'witness) sealed = ('a, 'witness) sealed_
let seal (w : 'a) (x : 'a) : ('a, Obj.t) sealed= FStar_Sealed.seal x
