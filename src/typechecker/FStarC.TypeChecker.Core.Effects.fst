(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core.Effects

(* See the interface. *)

open FStarC.TypeChecker.CommonBase
open FStarC
open FStar.List.Tot
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Errors.Msg { fquotes }
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module BU = FStarC.Util
module VCUtil = FStarC.TypeChecker.VCUtil
module UnivEq = FStarC.TypeChecker.UnivEq
module UniverseOf = FStarC.TypeChecker.UniverseOf
module Termination = FStarC.TypeChecker.Termination
module Err = FStarC.TypeChecker.Err
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Visit = FStarC.Syntax.Visit

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Syntax.Print {}

open FStarC.Pprint
open FStarC.Errors.Msg { text }
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad

let comp_eff (c:comp) : ML eff =
  if U.is_total_comp c then ETot
  else if U.is_tot_or_gtot_comp c then EGhost
  else EEff (U.comp_effect_name c)

let is_non_informative g t = N.non_info_norm g t

let non_informative g t
  : ML bool
  = is_non_informative g.tcenv t

let mk_comp_of_eff (m:I.lident) (t:typ) : ML comp =
  S.mk_Comp { effect_name = m; result_typ = t; flags = []; source_effect_name = m }

let as_comp (g:env) (et: (eff & typ))
  : ML comp
  = match et with
    | ETot, t -> S.mk_Total t
    | EGhost, t ->
      if non_informative g t
      then S.mk_Total t
      else S.mk_GTotal t
    | EEff m, t -> mk_comp_of_eff m t

let comp_as_eff_and_type (c:comp)
  : ML (eff & typ)
  = comp_eff c, U.comp_result c

let lid_to_eff (l:I.lident) : ML eff =
  if PC.is_tot_lid l then ETot
  else if PC.is_gtot_lid l then EGhost
  else EEff l

let is_tot_or_ghost_eff (e:eff) : ML bool =
  match e with
  | ETot | EGhost -> true
  | _ -> false

(* [e], of type [t_e] and effect [eff], was expected to have effect
   [target_eff] (and type [target_t]): reported as TcTerm's
   [Err.computed_computation_type_does_not_match_annotation], whose computed
   type carries the equation TcTerm adds to the type of a pure term. *)
let fail_effect_mismatch (#a:Type) (g:env) (e:term) (t_e:typ) (e_eff:eff) (target_t:typ) (target_eff:eff)
  : ML (result a)
  = let name (x:eff) : ML string =
      match x with
      | ETot -> "Tot"
      | EGhost -> "GTot"
      | EEff m -> show m
    in
    let t_e =
      match e_eff with
      | ETot -> U.comp_result (VCUtil.maybe_assume_result_eq_pure_term g.tcenv e (S.mk_Total t_e))
      | EGhost -> U.comp_result (VCUtil.maybe_assume_result_eq_pure_term g.tcenv e (S.mk_GTotal t_e))
      | _ -> t_e
    in
    let ppt = N.term_to_doc g.tcenv in
    fail_code Errors.Fatal_ComputedTypeNotMatchAnnotation [
      prefix 2 1 (text "Computed type") (ppt t_e) ^/^
      prefix 2 1 (text "and effect") (text (name e_eff)) ^/^
      prefix 2 1 (text "is not compatible with the annotated type") (ppt target_t) ^/^
      prefix 2 1 (text "and effect") (text (name target_eff))
    ]

(* The least effect both [e0] and [e1] lift to, if any. *)
let join_eff (g:env) (e0 e1:eff)
  : ML (result eff)
  = match e0, e1 with
    | ETot, e
    | e, ETot -> return e
    | EGhost, EGhost -> return EGhost
    | _ ->
      (* As [N.ghost_to_pure2]: composed with an erasable effect, GHOST is
         promoted to PURE, its erasability being accounted for by the other
         effect. *)
      let promote e other =
        match e, other with
        | EGhost, EEff m when Env.is_erasable_effect g.tcenv m -> ETot
        | _ -> e
      in
      let e0, e1 = promote e0 e1, promote e1 e0 in
      if ETot? e0 then return e1 else
      if ETot? e1 then return e0 else
      match Env.join_opt g.tcenv (eff_to_lid e0) (eff_to_lid e1) with
      | Some m -> return (lid_to_eff m)
      | None ->
        fail [
          text "Computations with effects" ^/^ pp (eff_to_lid e0)
          ^/^ text "and" ^/^ pp (eff_to_lid e1) ^/^ text "cannot be composed"
        ]

let rec join_eff_l (g:env) (es:list eff)
  : ML (result eff)
  = match es with
    | [] -> return ETot
    | e::es ->
      let! e' = join_eff_l g es in
      join_eff g e e'

(* [e0] may be used where [e1] is expected. *)
let sub_eff (g:env) (e0 e1:eff) : ML bool =
  match e0, e1 with
  | ETot, _ -> true
  | EGhost, EGhost -> true
  | EGhost, ETot -> false
  | _, ETot -> false
  (* GHOST lifts to an erasable effect via PURE, as in [N.ghost_to_pure2] *)
  | EGhost, EEff m when Env.is_erasable_effect g.tcenv m ->
    Some? (Env.monad_leq g.tcenv PC.primitive_pure_lid m)
  | _ ->
    Some? (Env.monad_leq g.tcenv (eff_to_lid e0) (eff_to_lid e1))
