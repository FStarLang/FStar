module Bug4498
#lang-pulse

(* Issue #4498: unfolding inside the scrutinee of a stuck projection (see
   #4472) must not break rewrites on ghost values.  Unfolding [mk] here leaves
   its [Tot] ascription around a body that is ghost, because [v] is erased, and
   core checking of that term fails; the projection stays stuck anyway, so no
   unfolding must happen and the equality is left to the SMT solver. *)

open Pulse
module G = FStar.Ghost

noeq type t = | A : nat -> t | B : nat -> t

let mk (x: t) : Tot (n: nat & nat) =
  match x with
  | A n -> (| n, n |)
  | B n -> (| n + 1, n |)

assume val p (n: nat) : slprop

ghost
fn test (v: G.erased t) (h: nat) (k: nat)
requires p (dfst (mk v)) ** pure (mk v == (| h, k |))
ensures p h
{
  rewrite each dfst (mk v) as h;
}
