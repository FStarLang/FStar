module Bug1056

open FStar.All
open FStar.ST

(* Bound variables 'c#246404' escapes; add a type annotation
let new_counter_no_annot init =
  let c = alloc init in
  fun () -> c := !c + 1; !c
*)

(* This works *)
val new_counter_ml : int -> ML (unit -> ML int)
let new_counter_ml init =
  let c = alloc init in
  fun () -> c := !c + 1; !c

(* This does not work, but it should! *)
val new_counter : int -> St (unit -> St int)
let new_counter init =
  let c = alloc init in
  fun () -> c := !c + 1; !c
(* (Error) assertion failed(Also see: /home/hritcu/Projects/fstar/pub/ulib/FStar.ST.fst(31,26-31,40)) *)
