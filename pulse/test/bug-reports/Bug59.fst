module Bug59
#lang-pulse

open Pulse.Lib.Pervasives

(* Not a great test, what we want to check for is that
the precondition fails to typecheck, the error code is not
really giving us that.

Two obligations fail here -- the ill-typed precondition and the
[1 == 2] assertion -- and now that they are deferred rather than
discharged as they arise, the first no longer aborts before the
second is reached, so both are reported. *)
[@@expect_failure [19; 19]]
ghost
fn bad_pre (#a #b : Type0) (x:a) (y:b)
  requires pure (x == y)
  returns _:unit
{
  assert (pure (1 == 2));
  admit();
}

