module Bug818

(* this works: val find : a:Type -> (option a) -> Tot int *)

val find : a:Type -> Tot ((option a) -> Tot int)
let rec find a l = 42
