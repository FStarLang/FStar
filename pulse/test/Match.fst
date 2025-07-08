module Match

#lang-pulse
open Pulse

type abc = | A

fn foo (r : ref abc) (#zzz : erased abc)
  preserves r |-> zzz
{
  let z = !r;
  match z {
    A -> {
     (* There is an implicit `rewrite each z as A` here, using the match_rewrite_tac.
     The tactic relies on a particular shape of the goal and environment,
     so we must *not* apply the rewrites_to substitution to the sides of the
     rewrite. The implementation of rewrite_each will not apply the substitution
     if a tactic is provided. *)
     ()
   }
  };
}
