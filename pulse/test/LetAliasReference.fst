(*
   Regression test for issue #4421: `!r` in a spec used to lose its
   dereference elaboration when nested under a `let … in` in that spec,
   causing an ill-typed term error (the stateful `op_Bang` application was
   not rewritten into its pure value).
*)
module LetAliasReference
open Pulse
#lang-pulse

let predicate observe (x: nat) =
  pure (x == x)

(* Works: dereference a direct function parameter. *)
fn direct (p: ref nat)
  requires exists* v. pts_to p #1.0R v ** observe (!p)
  returns ret: unit
  ensures exists* v. pts_to p #1.0R v ** observe (!p)
{
}

(* Was Error 12 before the fix: same spec, wrapped in a let. *)
fn alias_with_deref (x: ref nat)
  requires
    (let p = x in
     exists* v. pts_to p #1.0R v ** observe (!p))
  returns ret: unit
  ensures
    (let p = x in
     exists* v. pts_to p #1.0R v ** observe (!p))
{
}

(* Narrowing variant from the issue: dereference the original parameter
   `x`, never the alias `p`; `p` is unused. This isolates that the trigger
   is entering the `let` at all, not the aliasing itself. *)
fn alias_unused_deref_original (x: ref nat)
  requires
    (let p = x in
     exists* v. pts_to x #1.0R v ** observe (!x))
  returns ret: unit
  ensures
    (let p = x in
     exists* v. pts_to x #1.0R v ** observe (!x))
{
}
