module Test.Break

open FStar.Pure.Break

(* This should cause 4 separate SMT queries *)

let test () : unit =
  assert (forall x. x+1 > x);
  break();
  assert (forall x. x+2 > x);
  break();
  assert (forall x. x+3 > x);
  break();
  assert (forall x. x+4 > x);
  ()
