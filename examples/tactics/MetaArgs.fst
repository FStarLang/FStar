module MetaArgs

open FStar.Tactics

(* Quick test for a meta arg *)
let solve_with_42 () = exact (`42)
let test1 (#[solve_with_42] i : int) : int = i

let _ = assert (test1 == 42)


(* Testing that previous arguments are in-scope for the metaprogarm *)
let same_as (i:int) () = exact (quote i)

(* By default, a diagonal function, but allows to be overriden *)
let diag (x:int) (#[same_as x] y:int) : int * int = (x, y)

let _ = assert (diag 42 #43 == (42, 43))
let _ = assert (diag 42     == (42, 42))
