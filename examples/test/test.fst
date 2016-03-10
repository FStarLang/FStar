module Test

assume type t : int -> Type0

type state (i:bool) = 
  | Mk : t (if i then 0 else 1) -> state i

module Test2
open Test
val f : i:bool -> state i -> Tot (t (if i then 0 else 1))
let f i (Mk x) = x
