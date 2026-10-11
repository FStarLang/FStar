module OcamlOnly

(* A module that only exists for the ocaml target. *)
val twice (x:int) : y:int{y == x + x}
