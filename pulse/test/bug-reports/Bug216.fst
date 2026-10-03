module Bug216

#lang-pulse

open Pulse
open FStar.Tactics.V2

(* These used to fail, because Core only knew [Tot] and [GTot]: a [Tac]
   function, or an effectful [let] in one, was rejected. *)

assume
val foo (x:int) (f : unit -> Tac unit) : unit

fn test0 ()
{
  foo 1 (fun _ -> ());
  ()
}

fn test1 ()
{
  foo 1 (fun _ -> dump "");
  ()
}

fn test2 ()
{
  assert_by_tactic True (fun _ -> Tactics.set_rlimit 50; ());
  ()
}
