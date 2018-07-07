module Goals

open FStar.Tactics

(* A sanity check that we cannot trick the engine into dropping VCs *)

let id x = x
let intro_sq (x:'a) : squash 'a = ()
let elim (#a:Type) (x:False) : a = ()

(* First things first... *)
[@expect_failure] let _ = assert False

[@expect_failure] let _ = assert False by (fun () -> dismiss ())
[@expect_failure] let _ = assert False by (fun () -> set_goals [])

(* Leaving an active goal *)
[@expect_failure] let _ = assert False by (fun () -> ()) // original implicit
[@expect_failure] let _ = assert False by (fun () -> apply (`id)) // new implicit of same type
[@expect_failure] let _ = assert False by (fun () -> apply (`intro_sq)) // unsquashed new goal
[@expect_failure] let _ = assert False by (fun () -> apply (`elim)) // a different type

(* Leaving an SMT goal *)
[@expect_failure] let _ = assert False by (fun () -> smt ())
[@expect_failure] let _ = assert False by (fun () -> apply (`id); smt ())
[@expect_failure] let _ = assert False by (fun () -> apply (`intro_sq); smt ())
[@expect_failure] let _ = assert False by (fun () -> apply (`elim); smt ())

(* Dropping the goal, implicit remains *)
[@expect_failure] let _ = assert False by (fun () -> dismiss ())
[@expect_failure] let _ = assert False by (fun () -> apply (`id); dismiss ())
[@expect_failure] let _ = assert False by (fun () -> apply (`intro_sq); dismiss ())
[@expect_failure] let _ = assert False by (fun () -> apply (`elim); dismiss ())

(* I know! I'll use the unifier to solve my witness and drop it! *)
(* No, you still need to prove it. *)

[@expect_failure] let _ = assert False by (fun () -> let g = _cur_goal () in
                                              let e = cur_env () in
                                              let _ = unify_env e (goal_witness g) (`()) in
                                              ())

[@expect_failure] let _ = assert False by (fun () -> let g = _cur_goal () in
                                              let e = cur_env () in
                                              let _ = unify_env e (goal_witness g) (`()) in
                                              smt ())

[@expect_failure] let _ = assert False by (fun () -> let g = _cur_goal () in
                                              let e = cur_env () in
                                              let _ = unify_env e (goal_witness g) (`()) in
                                              dismiss ())
