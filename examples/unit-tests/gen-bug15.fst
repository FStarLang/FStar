
module GenBug15

(* This simple thing fails pre-type-checking *)

assume val foo : int -> unit

val foo2 : bool -> int -> unit
let foo2 (b : bool) = foo
