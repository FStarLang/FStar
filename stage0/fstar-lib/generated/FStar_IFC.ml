open Prims
type ('a, 'f) associative = unit
type ('a, 'f) commutative = unit
type ('a, 'f) idempotent = unit
type semilattice =
  | SemiLattice of unit * Obj.t * (Obj.t -> Obj.t -> Obj.t) 
let (uu___is_SemiLattice : semilattice -> Prims.bool) = fun projectee -> true
let (__proj__SemiLattice__item__top : semilattice -> Obj.t) =
  fun projectee ->
    match projectee with | SemiLattice (carrier, top, lub) -> top
let (__proj__SemiLattice__item__lub : semilattice -> Obj.t -> Obj.t -> Obj.t)
  =
  fun projectee ->
    match projectee with | SemiLattice (carrier, top, lub) -> lub
type sl = unit
type 'sl1 lattice_element = unit

type ('sl1, 'l, 'b) protected = 'b
let (hide : unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl1 -> fun l -> fun b -> fun x -> x
let (return : unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl1 -> fun a -> fun l -> fun x -> hide () () () x
let map :
  'a 'b .
    unit ->
      unit ->
        (unit, unit, 'a) protected ->
          ('a -> 'b) -> (unit, unit, 'b) protected
  = fun sl1 -> fun l -> fun x -> fun f -> f x
let (join : unit -> unit -> unit -> unit -> Obj.t -> Obj.t) =
  fun sl1 -> fun l1 -> fun l2 -> fun a -> fun x -> x
let (op_let_Greater_Greater :
  unit -> unit -> unit -> Obj.t -> unit -> unit -> (Obj.t -> Obj.t) -> Obj.t)
  =
  fun sl1 ->
    fun l1 ->
      fun a ->
        fun x -> fun l2 -> fun b -> fun f -> join () () () () (map () () x f)