module SyntaxTests

(* Random tests for parsing and the like *)

(* #int is indeed implicit *)
val g : #int -> int
let g #x = x
