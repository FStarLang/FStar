module ML.ExternalFunctions

val trim : string -> Tot string (* trim function in ocaml *)
  
val int_of_string : string -> Tot int (* int_of_string function in ocaml (OR) use Prims.parse_Int *)

val substringImpl : s:string -> i:nat -> l:nat -> Tot (ns:string{String.length ns = l}) (* Use ocaml substr function *)
(* How do we ensure that it holds in OCaml? *)

val randomVal : nat -> Tot string
