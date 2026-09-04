module CalcSquashSubtyping
#lang-pulse
open Pulse.Lib.Pervasives

(* Pulse checks Tot subterms with FStarC.TypeChecker.Core. A calc justification
   is a [unit -> Tot (squash (p y z))], and a lemma call used as one now has a
   refined result type [squash q]. Core must relate [squash q] to
   [squash (p y z)] by implication; its congruence rule for applications would
   otherwise demand that the two propositions be syntactically equal. *)
ghost
fn calc_with_lemma_justification (a b c : nat)
  requires emp
  ensures emp
{
  let _ : squash (2 * ((a + b) * c) == 2 * (a * c + b * c)) =
    calc (==) {
      2 * ((a + b) * c);
      == { FStar.Math.Lemmas.distributivity_add_left a b c }
      2 * (a * c + b * c);
    };
  ()
}

(* The same subtyping question, without going through calc. *)
ghost
fn squash_subtyping (a b c : nat)
  requires emp
  ensures emp
{
  let _ : squash (a * c + b * c == (a + b) * c) =
    FStar.Math.Lemmas.distributivity_add_left a b c;
  ()
}
