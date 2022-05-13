(*
   Copyright 2008-2021 Microsoft Research

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

module IteSoundness

(*
 * This module intentionally admits goals etc., so silence warnings
 *)
#set-options "--warn_error -274 --warn_error -296 --warn_error -242"

(*
 * This module provides unit tests for checking the soundness of the layered
 *   effects if-then-else combinator using a tactic
 *)

open FStar.Tactics

let unit : Type0 = unit
irreducible let an_attr : unit = ()

(*
 * First a layer over PURE
 * This works without the tactic too, but just to illustrate
 *)

type repr (a:Type) (wp:pure_wp a) = unit -> PURE a wp

open FStar.Monotonic.Pure

unfold
let return_wp (#a:Type) (x:a) : pure_wp a = as_pure_wp (fun p -> p x)
let return (a:Type) (x:a) : repr a (return_wp x) = fun () -> x

unfold
let bind_wp (#a #b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_wp b =
  elim_pure_wp_monotonicity_forall ();
  as_pure_wp (fun p -> wp1 (fun x -> wp2 x p))
let bind (a b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b)
  (f:repr a wp1)
  (g:(x:a -> repr b (wp2 x)))
  : repr b (bind_wp wp1 wp2)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    fun () ->
    let x = f () in
    g x ()

let subcomp (a:Type) (wp1 wp2:pure_wp a) (f:repr a wp1)
  : Pure (repr a wp2)
      (requires forall p. wp2 p ==> wp1 p)
      (ensures fun _ -> True)
  = f

unfold
let ite_wp (#a:Type) (wp_then wp_else:pure_wp a) (b:bool) : pure_wp a =
  elim_pure_wp_monotonicity_forall ();
  as_pure_wp (fun p -> (b ==> wp_then p) /\ ((~ b) ==> wp_else p))
let if_then_else (a:Type) (wp_then wp_else:pure_wp a)
  (f:repr a wp_then) (g:repr a wp_else)
  (b:bool)
  : Type = repr a (ite_wp wp_then wp_else b)

(*
 * The tactic that will solve the implicits and guard for if-then-else soundness
 *)
[@@ resolve_implicits; an_attr]
let mtac () : Tac unit =
  let is_eq_goal g : Tac bool =
    match term_as_formula' (goal_type g) with
    | Comp (Eq _) _ _ -> true
    | _ -> false in
  let is_squash_goal g : Tac bool =
    match term_as_formula' (goal_type g) with
    | App t _ -> term_eq t (`squash)
    | _ -> false in
  let rec separate_eq_and_squash_goals gs : Tac (list goal & list goal & list goal) =
    match gs with
    | [] -> [], [], []
    | g::tl ->
      let eq_goals, squash_goals, rest_goals = separate_eq_and_squash_goals tl in
      if is_eq_goal g then g::eq_goals, squash_goals, rest_goals
      else if is_squash_goal g then eq_goals, g::squash_goals, rest_goals
      else eq_goals, squash_goals, g::rest_goals in

  let eq_goals, squash_goals, rest_goals = separate_eq_and_squash_goals (goals ()) in
  set_goals eq_goals;
  iterAll (fun () -> trefl ());
  set_goals squash_goals;
  iterAll (fun () -> smt ());
  set_goals rest_goals;
  iterAll (fun () -> dismiss ())

(*
 * Annotating the effect with ite_soundness_by attribute,
 *   that takes as argument another attribute, which is the tactic attribute
 *   to which the soundness goals will be dispatched
 *)
[@@ ite_soundness_by an_attr]
effect {
  MPURE (a:Type) (wp:pure_wp a) with {repr; return; bind; subcomp; if_then_else}
}


(*
 * In the next example, the if-then-else and subcomp
 *   have additional phi and squash phi binders, that are unconstrained,
 *   and hence when checking the soundness of the if-then-else combinator,
 *   they cannot be solved by unification in the typechecker
 *
  * Whereas the tactic can instantiate them at will
 *)

type mrepr (a:Type) = a

let mreturn (a:Type) (x:a) : mrepr a = x
let mbind (a:Type) (b:Type) (f:mrepr a) (g:a -> mrepr b) : mrepr b = g f

(*
 * The attribute annotations on the binders below are required,
 *   else we don't allow unconstrained binders
 *)

let mif_then_else (a:Type)
  ([@@@ an_attr] phi:Type0)
  ([@@@ an_attr] bb:squash phi) 
  (f:mrepr a)
  (g:mrepr a)
  (b:bool)
  : Type
  = mrepr a

let msubcomp (a:Type)
  ([@@@ an_attr] phi:Type0)
  ([@@@ an_attr] bb:squash phi)  (f:mrepr a)
  : mrepr a = f

[@@ resolve_implicits; an_attr]
let mtac1 () : Tac unit =
  smt ();
  smt ();
  exact (`True)  //just solve the unconstrained phi with True

[@@ ite_soundness_by an_attr]
effect {
  M (a:Type)
  with {repr=mrepr; return=mreturn; bind=mbind; if_then_else=mif_then_else; subcomp=msubcomp}
}

(*
 * Another example to make sure that we are indeed hitting the tactic
 *
 * This is a toy example that uses admit_smt_queries in the tactic
 *   to make a proof go through
 *)

type mmrepr (a:Type) = a
let mmreturn (a:Type) (x:a) : mmrepr a = x
let mmbind (a b:Type) (f:mmrepr a) (g:a -> mmrepr b) : mmrepr b = g f
let mmsubcomp (a:Type) (f:mmrepr a)
  : Pure (mmrepr a)
      (requires False)
      (ensures fun _ -> True)
  = f

(*
 * The following doesn't work since the proof of if-then-else soundness
 *   requires us to prove False
 *)

[@@ expect_failure]
effect {
  N (a:Type)
  with { repr = mmrepr; return = mmreturn; bind = mmbind; subcomp = mmsubcomp }
}

[@@ resolve_implicits; an_attr]
let mtac2 () : Tac unit =
  tadmit ()

(*
 * If-then-else proof is dispatched to mtac1 that admits it
 *)

[@@ ite_soundness_by an_attr]
effect {
  N (a:Type)
  with { repr = mmrepr; return = mmreturn; bind = mmbind; subcomp = mmsubcomp }
}
