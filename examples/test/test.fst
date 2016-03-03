module Test

(* val f : int -> Tot int *)
let f x = 
  let rec aux : int -> Tot int = fun x -> aux x in 
  aux 0
