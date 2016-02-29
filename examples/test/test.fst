module Test

(* assume val f : x:int -> Div int  *)
(*   (requires (b2t (x >= 0))) *)
(*   (ensures (fun y -> x == y)) *)

(* val test : nat -> Dv nat *)
(* let test x = f x *)

assume val f : x:int -> #r:range_of x -> unit -> Pure int
  (requires (labeled r "Pre-condition of f" (x >= 0)))
  (ensures (fun y -> x = y))

val test : int -> Tot int
let test x = f (x + 1) ()
