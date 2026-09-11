(*
   Regression test for issue #4423: `!r` sugar used inside a refinement
   type that is passed as an *explicit type argument* to a function call
   (as opposed to appearing in a `requires`/`ensures`/`assert` spec) used
   to be left unpurified, causing the resulting proof obligation to
   contain the raw (unrewritten) stateful `op_Bang` application, which the
   prover could not relate to the concrete known value -- yielding a
   "Cannot prove ..." error even though the equivalent `assert` typechecks
   fine.
*)
module CallArgPurify
open Pulse
open Pulse.Lib.ForEvery
#lang-pulse

assume val p : nat -> slprop

fn test ()
  requires forall+ (i:nat{i < 0}). p i
{
  let mut z = 0;
  assert (forall+ (i:nat{i < 0}). p i);
  forevery_elim_empty
    #(i:nat{i < !z})
    (fun (i:nat{i < !z}) -> p i);
  ()
}
