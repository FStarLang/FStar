module LetInLemmaBinder
#lang-pulse
open Pulse.Lib.Pervasives

(* Pulse checks Tot subterms with FStarC.TypeChecker.Core, and a binder's type
   reaches Core as the desugarer left it: a [let] inside a type still carries
   [Tm_unknown] for its annotation, which [do_check]'s [Tm_let] case used to
   check unconditionally.  An [ensures] is a refinement on the result type now,
   so a [Lemma]-typed binder puts such a [let] squarely inside a type.
   Minimized from an EverParse Pulse module. *)

let lemty = (x: nat) -> Tot (squash (let y = x + 1 in y > 0))

fn take_lemma_binder (lem: lemty)
  requires emp
  returns _: unit
  ensures emp
{ () }

(* The same thing written with the surface [Lemma] syntax, and used. *)
fn call_lemma_binder
  (l : (x:nat -> Lemma (ensures (let y = x + 1 in y > x))))
  (n : nat)
  requires emp
  ensures emp
{
  l n;
  ()
}
