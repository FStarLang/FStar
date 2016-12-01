module Bug578

val t : bool -> Tot Type0
let t b = if b then int else (int -> Tot int)

(* CH: at the top level everything explodes  *)
(* val f0 : t false *)
(* let f0 n = n *)
(* Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error. *)
(* Failure("Impossible! let-bound lambda Bug578.f0 = (fun n -> n@0) has a type that's not a function: ((_:Prims.int -> Tot Prims.int) : Type)\n") *)

(* CH: or just fails to work *)
(* val f1 : unit -> t false *)
(* let f1 () n = n *)
(* ./bug578.fst(13,24-14,15) : Error *)
(* Expected a term of type "(uu___:Prims.unit -> (Bug578.t false))"; *)
(* got a function "(fun uu___ n -> n@0)" (Function definition takes more arguments than expected from its annotated type) *)

(* CH: If we move this inside then this sometimes works -- !This dosn't work any more! *)
(* val f2 : unit -> t false *)
(* let f2 () = (fun n -> n) *)
(* ./bug578.fst(21,24-22,24) : Error *)
(* Expected a term of type "(uu___:Prims.unit -> (Bug578.t false))"; *)
(* got a function "(fun uu___ n -> n@0)" (Function definition takes more arguments than expected from its annotated type) *)

(* CH: But as soon as things get trickier, things fail again *)
(* val f3 : b:bool -> (if b then int else int -> Tot int) *)
(* let f3 b = if b then 42 else (fun n -> n) *)
(* ./bug578.fst(29,29-29,41): Failed to resolve implicit argument of type 'Type' introduced in (?39422 b uu___) because user-provided implicit term *)

(* CH: ... and again *)
(* val f4 : b:bool -> t b *)
(* let f4 b = if b then 42 else (fun n -> n) *)
(* ./bug578.fst(31,29-31,41): Failed to resolve implicit argument of type '((fun b uu___ -> Type) b uu___)' introduced in (?17835 b uu___) because user-provided implicit term *)
(* ./bug578.fst(30,22-31,41): could not prove post-condition *)

(* CH: ... or they succeed with additional type annotations *)
val f5 : b:bool -> t b
let f5 b = if b then 42 else (fun (n:int) -> n)

val aux : int -> Tot int
let aux n = n
val f6 : b:bool -> t b
let f6 b = if b then 42 else aux
