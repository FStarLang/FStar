(*
   Copyright 2026 Microsoft Research

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

(* Tests that a Pulse `match` gives each branch, in addition to the
   equation relating the scrutinee to its own pattern, the hypotheses
   that the scrutinee does *not* match any of the preceding patterns.

   Without those negated branch conditions, a wildcard (or variable)
   pattern learns nothing at all about the scrutinee, since its own
   branch equality `sc == x` is vacuous. *)

module MatchNegatedBranches
#lang-pulse
open Pulse.Lib.Pervasives

(* A wildcard after a constant pattern. *)

fn wild_after_const (n:nat)
  returns r:int
{
  match n {
    0 -> { 1 }
    _ -> { assert (pure (n =!= 0)); 0 }
  }
}

(* A named variable pattern after a constant pattern. *)

fn var_after_const (n:nat)
  returns r:int
{
  match n {
    0 -> { 1 }
    x -> { assert (pure (x =!= 0)); x }
  }
}

(* Several preceding constant patterns: all of them must be negated. *)

fn wild_after_two_consts (n:nat)
  returns r:int
{
  match n {
    0 -> { 1 }
    1 -> { 2 }
    _ -> { assert (pure (n =!= 0 /\ n =!= 1)); 0 }
  }
}

(* A wildcard after a constructor pattern: the wildcard branch knows the
   scrutinee is not None. *)

fn wild_after_ctor (n:option int)
  returns r:int
{
  match n {
    Prelude.None -> { (-1) }
    _ -> { assert (pure (Some? n)); Some?.v n }
  }
}

(* Same, with a bound variable in the last pattern. *)

fn var_after_ctor (n:option int)
  returns r:int
{
  match n {
    Prelude.None -> { (-1) }
    x -> { assert (pure (Some? x)); Some?.v x }
  }
}

(* The negated conditions must also account for patterns with binders. *)

fn wild_after_cons (xs:list int)
  returns r:int
{
  match xs {
    _ :: _ -> { 1 }
    _ -> { assert (pure (Nil? xs)); 0 }
  }
}

(* Nested/deep patterns are not supported by Pulse's surface syntax, but
   patterns with binders are, and their negation must be handled. *)

fn wild_after_ctor_with_binder (n:option int)
  returns r:int
{
  match n {
    Prelude.Some x -> { x }
    _ -> { assert (pure (None? n)); 0 }
  }
}

(* Boolean scrutinee: a wildcard after `true` knows the scrutinee is false. *)

assume
val bp ([@@@mkey] b:bool) : slprop

assume
val btrue () : stt_ghost unit [] (bp true) (fun _ -> emp)

assume
val bfalse () : stt_ghost unit [] (bp false) (fun _ -> emp)

fn wild_after_true (b:bool)
  requires bp b
  ensures emp
{
  match b {
    true -> { btrue () }
    _ -> { assert (pure (b == false)); rewrite each b as false; bfalse () }
  }
}

(* The negated hypotheses are strong enough to prove a branch unreachable. *)

fn unreachable_last (n:option int)
  requires pure (Some? n)
  returns r:int
{
  match n {
    Prelude.Some x -> { x }
    _ -> { unreachable () }
  }
}

(* When the scrutinee is not a variable, the checker cannot install a
   [rewrites_to] for it, and instead wraps each branch in a RENAME proof
   hint discharged by [match_rename_tac]. That tactic looks up the
   scrutinee/pattern equality as the *last* binding in scope, so the
   negated conditions for the preceding patterns must be pushed before
   it, not after. These tests pin that down: every branch below other
   than the first has at least one preceding pattern, and needs the
   rename to have happened in order to match its precondition. *)

assume
val mk_opt (n:int) : option int

assume
val opt_res ([@@@mkey] o:option int) : slprop

assume
val use_none () : stt_ghost unit [] (opt_res Prelude.None) (fun _ -> emp)

assume
val use_some (x:int) : stt_ghost unit [] (opt_res (Prelude.Some x)) (fun _ -> emp)

fn rename_nonvar_sc (n:int)
  requires opt_res (mk_opt n)
  ensures emp
{
  match (mk_opt n) {
    Prelude.None -> { use_none () }
    Prelude.Some x -> { use_some x }
  }
}

(* Same, but the second branch binds a variable rather than matching a
   constructor, so it relies on both the rename and the negated condition
   of the preceding pattern: [match_rename_tac] replaces [mk_opt n] by
   [o] in the context, and the negated condition is what tells us [o] is
   a [Some]. *)

fn rename_nonvar_sc_wild (n:int)
  requires opt_res (mk_opt n)
  ensures emp
{
  match (mk_opt n) {
    Prelude.None -> { use_none () }
    o -> {
      assert (pure (Some? o));
      rewrite opt_res o as opt_res (Prelude.Some (Some?.v o));
      use_some (Some?.v o);
    }
  }
}
