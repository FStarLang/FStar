module Tautology
module P = FStar.Tactics.PatternMatching

open FStar.Tactics

// Note: putting ``qed ()`` inside each call to ``gpm`` would give early
// errors, at the price of verbosity.
let rec tauto (): Tac unit =
  // dump "[tauto]";
  P.repeat' (fun () -> first #unit [
    P.gpm (fun (g: P.pm_goal (squash True)) ->
      trivial ()
    );
    P.gpm (fun (a b: Type0) (g: P.pm_goal (squash (a /\ b))) ->
      split ()
    );
    P.gpm (fun (a b: Type0) (g: P.pm_goal (squash (a \/ b))) ->
      (fun () -> left (); tauto ()) `or_else`
      (fun () -> right (); tauto ())
    );
    P.gpm (fun (a b: Type0) (g: P.pm_goal (squash (a ==> b))) ->
      P.implies_intro' ()
    );
    P.gpm (fun (a: Type0) (h: P.hyp a) (g: P.pm_goal (squash a)) ->
      P.exact_hyp a h
    );
    P.gpm (fun (a: Type0) (h: P.hyp a) (g: P.pm_goal a) ->
      P.exact_hyp' h
    );
  ]);
  qed ()


assume val p: prop

// This one exercises matching on squash p
let _ =
  assume p;
  assert_by_tactic p tauto

// This one exercises matching on p (without the squash)
let _ =
  assert_by_tactic (p ==> (True /\ False \/ True) /\ p) tauto
