module Bug213

open Constructive

type intPair =
  | IP : f:int -> s:int -> intPair

(* This does not work *)
val foo : cexists (fun p -> ceq (IP.f p) (IP.s p)) -> Tot unit
let foo h =
  let ExIntro (IP p1 p2) hp = h in
  ()

(* This works *)
val foo' : cexists (fun p -> ceq (IP.f p) (IP.s p)) -> Tot unit
let foo' h =
  let ExIntro p hp = h in
  let IP p1 p2 = p in
  ()
