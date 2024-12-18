open Prims
let bool_of_or : 'p 'q . ('p, 'q) Prims.sum -> Prims.bool =
  fun t ->
    match t with | Prims.Left uu___ -> true | Prims.Right uu___ -> false
type 'p pow = unit
type ('a, 'b) retract =
  | MkR of unit * unit * unit 
let uu___is_MkR : 'a 'b . ('a, 'b) retract -> Prims.bool =
  fun projectee -> true
type ('a, 'b) retract_cond =
  | MkC of unit * unit * unit 
let uu___is_MkC : 'a 'b . ('a, 'b) retract_cond -> Prims.bool =
  fun projectee -> true
let false_elim : 'a . unit -> 'a =
  fun uu___ -> (fun f -> Obj.magic (failwith "unreachable")) uu___
type u = unit