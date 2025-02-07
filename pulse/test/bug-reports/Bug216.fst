module Bug216

#lang-pulse

open Pulse
open FStar.Tactics.V2

(* These should work. *)

assume
val foo (x:int) (f : unit -> Tac unit) : unit

(*
* Error 76 at Spur.fst(15,2-15,5):
  - tc_term callback failed:  Top ()
    > top (Spur.foo 1 (fun _ -> ()))
    >> app subtyping ()
    >>> check_subtype (_: Prims.unit -> Prims.unit ( <:? fun _ -> ()) _: Prims.unit -> FStar.Tactics.Effect.Tac Prims.unit)
    >>>> subtype arrow ()
    >>>>> check_subcomp ()
    Subcomp failed: Unequal computation types Prims.PURE and FStar.Tactics.Effect.TAC
  - Raised within Tactics.refl_tc_term

* Error 228 at Spur.fst(15,2-15,2):
  - Ill-typed term:Spur.foo 1 (fun _ -> ())
*)
[@@expect_failure]
fn test0 ()
  requires emp
  ensures emp
{
  foo 1 (fun _ -> ());
  ()
}

(*
* Error 76 at Spur.fst(38,2-38,5):
  - tc_term callback failed:  Top ()
    > top (Spur.foo 1 (fun _ -> FStar.Stubs.Tactics.V2.Builtins.dump ""))
    >> app arg (fun _ -> FStar.Stubs.Tactics.V2.Builtins.dump "")
    >>> abs body (FStar.Stubs.Tactics.V2.Builtins.dump "")
    >>>> is_arrow ()
    Expected total or gtot arrow, got FStar.Tactics.Effect.Tac
  - Raised within Tactics.refl_tc_term

* Error 228 at Spur.fst(38,2-38,2):
  - Ill-typed term:Spur.foo 1 (fun _ -> FStar.Stubs.Tactics.V2.Builtins.dump "")
*)
[@@expect_failure]
fn test1 ()
  requires emp
  ensures emp
{
  foo 1 (fun _ -> dump "");
  ()
}

(*
* Error 76 at Spur.fst(60,2-60,18):
  - tc_term callback failed:  Top ()
    > top (FStar.Tactics.Effect.assert_by_tactic Prims.l_True
      (fun _ ->
          FStar.Tactics.SMT.set_rlimit 50;
          ()))
    >> app arg (fun _ ->
      FStar.Tactics.SMT.set_rlimit 50;
      ())
    >>> abs body (FStar.Tactics.SMT.set_rlimit 50;
    ())
    Let binding is effectful (lbeff = FStar.Tactics.Effect.TAC)
  - Raised within Tactics.refl_tc_term

* Error 228 at Spur.fst(60,2-60,2):
  - Ill-typed term:FStar.Tactics.Effect.assert_by_tactic Prims.l_True
      (fun _ ->
          FStar.Tactics.SMT.set_rlimit 50;
          ())
*)
[@@expect_failure]
fn test2 ()
  requires emp
  ensures emp
{
  assert_by_tactic True (fun _ -> Tactics.set_rlimit 50; ());
  ()
}
