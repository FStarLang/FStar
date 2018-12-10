(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
