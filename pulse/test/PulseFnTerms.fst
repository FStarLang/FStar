module PulseFnTerms
open Pulse.Nolib
#lang-pulse

(* ================================================================
   Tests for fn-type-as-term syntax.

   The fn type can appear in type positions: binder annotations
   and type abbreviation RHS. Syntax:

     fn (x:t) ... requires pre ensures post
     ghost fn (x:t) ... requires pre ensures post
     atomic fn (x:t) ... requires pre ensures post

   This reuses F*'s existing (x : type) binder rule by extending
   simpleArrow with fn-type productions.
   ================================================================ *)

(* -------------------------------------------------------------- *)
(* 1. Type abbreviation — fn type as RHS                           *)
(* -------------------------------------------------------------- *)

type unit_action = fn (_u : unit) requires emp ensures emp

(* -------------------------------------------------------------- *)
(* 2. Type abbreviation with meaningful binders                    *)
(* -------------------------------------------------------------- *)

assume val my_res : nat -> slprop

type my_action = fn (v : nat) requires emp ensures my_res v

(* -------------------------------------------------------------- *)
(* 3. fn type in binder position — higher-order function           *)
(* -------------------------------------------------------------- *)

fn call_unit_action (f : fn (_u : unit) requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

fn call_unit_action' (f : unit_action)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 4. fn type binder with parameters                               *)
(* -------------------------------------------------------------- *)

fn apply_action (f : fn (v : nat) requires emp ensures my_res v)
  requires emp
  ensures my_res 42
{
  f 42
}

(* -------------------------------------------------------------- *)
(* 5. Multiple fn-typed binders                                    *)
(* -------------------------------------------------------------- *)

fn compose_actions
  (f : fn (_u : unit) requires emp ensures emp)
  (g : fn (_u : unit) requires emp ensures emp)
  requires emp
  ensures emp
{
  f ();
  g ()
}

(* -------------------------------------------------------------- *)
(* 6. ghost fn type in binder and type abbreviation                *)
(* -------------------------------------------------------------- *)

type ghost_unit_action = ghost fn (_u : unit) requires emp ensures emp

fn call_ghost (f : ghost fn (_u : unit) requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 7. Using a type abbreviation as a binder type                   *)
(* -------------------------------------------------------------- *)

fn call_via_abbrev (f : unit_action)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 8. fn type with preserves annotation                            *)
(* -------------------------------------------------------------- *)

type preserving_action (p : slprop) = fn (_u : unit) preserves p

fn call_preserving (p : slprop) (f : fn (_u : unit) preserves p)
  requires p
  ensures p
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 9. fn type with multiple binders                                *)
(* -------------------------------------------------------------- *)

fn apply_two_arg (f : fn (x : nat) (y : nat) requires emp ensures my_res (x + y))
  requires emp
  ensures my_res 42
{
  f 20 22
}

(* -------------------------------------------------------------- *)
(* 10. atomic fn type — abbreviation and binder                    *)
(* -------------------------------------------------------------- *)

type atomic_unit_action = atomic fn (_u : unit) requires emp ensures emp

fn call_atomic (f : atomic fn (_u : unit) requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 11. atomic fn type with opens                                   *)
(* -------------------------------------------------------------- *)

type atomic_action_opens (is : inames) =
  atomic fn (_u : unit) opens is requires emp ensures emp

fn call_atomic_opens
  (is : inames)
  (f : atomic fn (_u : unit) opens is requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 12. ghost fn type with opens                                    *)
(* -------------------------------------------------------------- *)

type ghost_action_opens (is : inames) =
  ghost fn (_u : unit) opens is requires emp ensures emp

fn call_ghost_opens
  (is : inames)
  (f : ghost fn (_u : unit) opens is requires emp ensures emp)
  requires emp
  ensures emp
{
  f ()
}

(* -------------------------------------------------------------- *)
(* 13. fn type with returns annotation                             *)
(* -------------------------------------------------------------- *)

type returning_action = fn (_u : unit) requires emp returns v : nat ensures my_res v

fn call_returning (f : fn (_u : unit) requires emp returns v : nat ensures my_res v)
  requires emp
  ensures (exists* v. my_res v)
{
  let v = f ();
  ()
}

(* -------------------------------------------------------------- *)
(* 14. atomic fn with opens and returns                            *)
(* -------------------------------------------------------------- *)

type atomic_returning (is : inames) =
  atomic fn (_u : unit) opens is requires emp returns v : nat ensures my_res v

fn call_atomic_returning
  (is : inames)
  (f : atomic fn (_u : unit) opens is requires emp returns v : nat ensures my_res v)
  requires emp
  ensures (exists* v. my_res v)
{
  let v = f ();
  ()
}

atomic
fn call_atomic_returning'
  (is : inames)
  (f : atomic fn (_u : unit) opens is requires emp returns v : nat ensures my_res v)
  requires emp
  ensures (exists* v. my_res v)
  opens is
{
  let v = f ();
  ()
}

(* -------------------------------------------------------------- *)
(* 15. bare fn type — no computation annotations                   *)
(* -------------------------------------------------------------- *)

// This is perhaps weird, but it returns unit with emp pre/post
type bare_fn_type = fn (x : nat) (y : nat)

fn call_bare (f : fn (x : nat))
  requires emp
  ensures emp
{
  f 1;
  f 2;
}

// Perhaps even weirder, this is exactly `stt unit emp (fun _ -> emp)`
type x = fn

(* -------------------------------------------------------------- *)
(* 16. fn type in record field position                            *)
(* -------------------------------------------------------------- *)

noeq
type record_with_fn = {
  action: fn (_u : unit) requires emp ensures emp;
  getter: fn (_u : unit) requires emp returns v : nat ensures my_res v;
}

fn call_record_action (r : record_with_fn)
  requires emp
  ensures emp
{
  let f = r.action;
  f ()
}

fn call_record_getter (r : record_with_fn)
  requires emp
  ensures (exists* v. my_res v)
{
  let f = r.getter;
  let v = f ();
  ()
}

(* -------------------------------------------------------------- *)
(* 17. fn type in val declaration                                   *)
(* -------------------------------------------------------------- *)

assume val val_unit_action : fn (_u : unit) requires emp ensures emp

assume val val_returning : fn (_u : unit) requires emp returns v : nat ensures my_res v

fn use_val_unit_action (_u : unit)
  requires emp
  ensures emp
{
  val_unit_action ()
}

fn use_val_returning (_u : unit)
  requires emp
  ensures (exists* v. my_res v)
{
  let v = val_returning ();
  ()
}
