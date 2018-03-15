module Tautology
module P = FStar.Tactics.PatternMatching

open FStar.Tactics

// Note: putting ``P.done ()`` inside each call to ``gpm`` would give early
// errors, at the price of verbosity.
let rec tauto (): Tac unit =
  // dump "[tauto]";
  P.repeat' (fun () -> P.tfirst #unit [
    P.gpm (fun (g: P.goal (squash True)) ->
      trivial ()
    );
    P.gpm (fun (a b: Type0) (g: P.goal (squash (a /\ b))) ->
      split ();
      tauto ()
    );
    P.gpm (fun (a b: Type0) (g: P.goal (squash (a \/ b))) ->
      (fun () -> left (); tauto ()) `or_else`
      (fun () -> right (); tauto ())
    );
    P.gpm (fun (a b: Type0) (g: P.goal (squash (a ==> b))) ->
      P.implies_intro' ();
      tauto ()
    );
    P.gpm (fun (a: Type0) (h: P.hyp a) (g: P.goal (squash a)) ->
      P.exact_hyp a h
    );
    P.gpm (fun (a: Type0) (h: P.hyp a) (g: P.goal a) ->
      P.exact_hyp' h
    );
  ]);
  P.done ()


assume val p: prop

// This one exercises matching on squash p
let _ =
  assume p;
  assert_by_tactic p tauto

// This one exercises matching on p (without the squash)
let _ =
  assert_by_tactic (p ==> (True /\ False \/ True) /\ p) tauto
