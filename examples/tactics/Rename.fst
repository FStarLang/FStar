module Rename

(* Testing the new printing based on the static environment *)

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

let l1 (x : bool) (y : int) (z : unit) =
    assert_by_tactic (phi ==> (psi ==> xi))
            (h0 <-- implies_intro;
             h1 <-- implies_intro;
             dump "Test";;
             exact (quote p)
             )

// this error should show pretty binders too
(* let _ = *)
(*     assert_by_tactic (False ==> True) *)
(*             (h0 <-- implies_intro; *)
(*              x <-- quote (fun x -> 1 + x); *)
(*              let t = mk_e_app x [pack (Tv_Const C_Unit)] in *)
(*              tc t;; *)
(*              trivial) *)
