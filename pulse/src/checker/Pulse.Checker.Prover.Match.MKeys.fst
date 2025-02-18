(*
   Copyright 2023 Microsoft Research

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

module Pulse.Checker.Prover.Match.MKeys

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Show

module T       = FStar.Tactics.V2
module R       = FStar.Reflection.V2
module L       = FStar.List.Tot
module TermEq  = FStar.Reflection.TermEq
module PTU = Pulse.Typing.Util

let rec equational (t:term) : bool =
  match R.inspect_ln t with
  // | R.Tv_Var _ -> true
  | R.Tv_App h _ -> equational h
  | R.Tv_Match _ _ _ -> true
  | R.Tv_AscribedT t _ _ _
  | R.Tv_AscribedC t _ _ _ -> equational t
  | _ -> false

let type_of_fv (g:env) (fv:R.fv)
  : T.Tac (option R.term)
  = let n = R.inspect_fv fv in
    match R.lookup_typ (fstar_env g) n with
    | None -> None
    | Some se ->
      match R.inspect_sigelt se with
      | R.Unk -> None
      | R.Sg_Let _ lbs -> (
        L.tryPick
          (fun lb -> 
            let lbv = R.inspect_lb lb in
            if R.inspect_fv lbv.lb_fv = n
            then Some lbv.lb_typ
            else None)
          lbs
      )
      | R.Sg_Val _ _ t -> Some t
      | R.Sg_Inductive _nm _univs params typ _ -> None

let is_mkey (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Pulse"; "Lib"; "Core"; "mkey"]
  | _ -> false

let binder_is_mkey (b:R.binder) : bool =
  L.existsb is_mkey (R.inspect_binder b).attrs

let binder_is_slprop (b:R.binder) : T.Tac bool =
  let r = TermEq.term_eq tm_slprop (R.inspect_binder b).sort in
  T.print <| "is_slprop " ^ show (R.inspect_binder b).sort ^ " = " ^ show r;
  r

let rec zip3 (l1:list 'a) (l2:list 'b) (l3:list 'c) : T.Tac (list ('a & 'b & 'c)) =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (x, y, z) :: zip3 xs ys zs
  | _, _, _ ->
    T.fail "zip3: length mismatch"

let same_head (t0 t1:term)
  : T.Tac bool
  = match T.hua t0, T.hua t1 with
    | Some (h0, us0, args0), Some (h1, us1, args1) ->
      T.inspect_fv h0 = T.inspect_fv h1 &&
      L.length args0 = L.length args1
    | _ ->
      true // conservative

exception GFalse
exception GTrue

let rec eligible_for_smt_equality (g:env) (t0 t1 : term)
  : T.Tac bool
= try
    (* Never try to SMT-match pure slprops. In fact we never should be called
    on pure slprops anyway. *)
    if Tm_Pure? (inspect_term t0) || Tm_Pure? (inspect_term t1) then
      raise GFalse;
    (* If they are both equational, claim it fair game to try to use SMT.
    Note: this is *before* the ambiguity check and we do not perform a query,
    so if there is one equational resource in the context and two equational
    goals, we will fail claiming ambiguity. *)
    (* FIXME: This is probably quite unexpected, but otherwise
    working with matches/ifs is a real pain. What do we expect the
    user to write...? *)
    (* ALSO FIXME: We should only try to equate matches if there is some possibility
    that their branches match. No point in trying to
      (if p then r|->1 else r|->2)
    with
      inv i p
    or whatever
    *)
    if equational t0 && equational t1 then
      raise GTrue;
    let term_eq = TermEq.term_eq in
    let h0, args0 = R.collect_app_ln t0 in
    let h1, args1 = R.collect_app_ln t1 in
    if not (term_eq h0 h1) || not (length args0 = length args1) then
      raise GFalse;

    (* At this point, we have two applications with the same head. Look at mkeys. *)

    let hfv = match R.inspect_ln h0 with
              | R.Tv_FVar fv
              | R.Tv_UInst fv _ -> fv
              | _ -> raise GFalse
    in
    if Pulse.Reflection.Util.fv_has_attr_string "Pulse.Lib.Core.no_mkeys" hfv then
      raise GTrue;
    let t = match type_of_fv g hfv with | None -> raise GFalse | Some t -> t in
    let bs, _ = R.collect_arr_ln_bs t in
    if L.length bs <> L.length args0 then
      false
    else
    let bs_args0_args1 = zip3 bs args0 args1 in
    let (anykey, eq) = T.fold_right (fun (b, (a0, _), (a1, _)) (anykey, eq)->
      if not eq then (anykey, false) else
      if binder_is_mkey b then
        let eq' =
          if binder_is_slprop b then
            eligible_for_smt_equality g a0 a1
          else
            try
              Some? (fst (PTU.check_equiv_now_nosmt_unfold (elab_env g) a0 a1))
            with | _ -> false
        in
         (true, eq && eq')
      else
        (anykey, eq)
    ) bs_args0_args1 (false, true)
    in
    (* Attempt SMT if all keys matched. If there are no keys,
    we consider that a match. To require at least one key uncomment
    the conjunct below. *)
    // anykey &&
    eq
  with
  | GFalse -> false
  | GTrue -> true
  | e -> raise e
