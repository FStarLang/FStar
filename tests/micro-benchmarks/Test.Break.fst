module Test.Break

open FStar.Pure.BreakVC

(* This should cause 4 separate SMT queries *)

let test () : unit =
  assert (forall x. x+1 > x);
  break_vc();
  assert (forall x. x+2 > x);
  break_vc();
  assert (forall x. x+3 > x);
  break_vc();
  assert (forall x. x+4 > x);
  ()
