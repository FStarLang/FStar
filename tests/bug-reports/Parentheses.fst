module Parentheses

let forall_intro #t (#p: t->Type0) (h: (x:t -> squash (p x))) : squash (forall x. p x) =
  Classical.Sugar.forall_intro _ _ h

let trailing_fun_does_not_require_parens :
    squash (forall (x: nat) (y: nat). x + y >= 0) =
  forall_intro fun x -> forall_intro fun y -> ()

let trailing_fun_swallows_seqs :
    squash (forall (x: nat) (y: nat). x + y >= 0) =
  forall_intro fun x -> forall_intro fun y -> (); ()

let assert_does_not_require_parens : unit =
  assert 8 < 42;
  ()

let assume_does_not_require_parens : False =
  assume 0 == 1;
  ()