module PolyBug21

assume val constfun : 'a -> 'b -> Tot 'a
(* let constfun x _ = x *)

val ftrue : 'b -> Tot bool
let ftrue = constfun true
