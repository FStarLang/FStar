module Test

(* let f (x:int) : int = 0 *)

(* val f : int -> Tot int *)
let f x =
  let rec aux : int -> Tot int = fun x -> aux x in
  aux 0
