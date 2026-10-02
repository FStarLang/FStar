module Bug4619

(* FStarLang/FStar#4619: a lemma call in a branch returns a [squash]; the
   inferred post of the branch must not mention that result variable. *)
#lang-pulse
open Pulse

let guarded (x : int)
  : Lemma (requires x > 0) (ensures x > 0)
= ()

fn test (x : int)
  requires emp
  ensures emp
{
  if (x > 0) {
    guarded x;
    ();
  } else {
    ()
  };
  ()
}
