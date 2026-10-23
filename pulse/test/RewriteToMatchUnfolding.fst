module RewriteToMatchUnfolding
#lang-pulse
open Pulse
module SZ = FStar.SizeT

(* Rewriting [p ** q] as [side n (SZ.v tid) it], where [side] unfolds to an
   [if] whose branch is [p ** q]: the equation is to be stated on the
   unfolding, which the SMT solver proves by cases, rather than on [side ..]
   itself, whose unfolding by the solver would yield abstractions (the bodies
   of the [exists*]) encoded apart from those of [p ** q]. *)

let even (x:int) : bool = x % 2 = 0

let side (n:nat) (tid:nat) : nat -> slprop =
  fun it ->
    if it >= 2 * n then emp
    else if even it then (exists* (r:int). pure (r == tid)) ** (exists* (r:int). pure (r == tid + 1))
    else emp

fn test (n:nat) (vj:nat{vj < n}) (tid:SZ.t)
requires (exists* (r:int). pure (r == SZ.v tid)) ** (exists* (r:int). pure (r == SZ.v tid + 1))
ensures side n (SZ.v tid) (2 * vj)
{
  assert pure (even (2 * vj));
  rewrite ((exists* (r:int). pure (r == SZ.v tid)) ** (exists* (r:int). pure (r == SZ.v tid + 1)))
       as (side n (SZ.v tid) (2 * vj));
}
