module Counter

(* A module whose implementation depends on the compilation target. *)
val name : string
val double (x:int) : y:int{y == x + x}
