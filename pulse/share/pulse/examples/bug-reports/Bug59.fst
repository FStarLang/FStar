module Bug59
#lang-pulse

open Pulse.Lib.Pervasives

(* Not a great test, what we want to check for is that
the precondition fails to typecheck, the error code is not
really giving us that. *)
[@@expect_failure [228; 19]]

ghost
fn bad_pre (#a #b : Type0) (x:a) (y:b)
  requires pure (x == y)
  returns _:unit
  ensures emp
{
  assert (pure (1 == 2));
  admit();
}

