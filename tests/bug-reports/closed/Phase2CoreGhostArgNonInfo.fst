module Phase2CoreGhostArgNonInfo

(* A ghost argument, here [g (reveal n)], for a non-informative formal, here
   of type [int -> GTot int], is total. *)
assume val g (n:nat) (x:int) : Tot int
let use (f: int -> GTot int) : int = 0
let test (n: Ghost.erased nat) : int = use (g n)
