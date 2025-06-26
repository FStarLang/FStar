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

module Pulse.Checker.Prover.Match.Matchers

open FStar.Tactics.V2
open FStar.List.Tot
open FStar.Ghost

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base
open Pulse.Checker.Prover.Match.Base
open Pulse.PP
open Pulse.Show
open Pulse.Checker.Prover.Base

module T       = FStar.Tactics.V2
module R       = FStar.Reflection.V2
module L       = FStar.List.Tot
module TermEq  = FStar.Reflection.TermEq
module RT      = FStar.Reflection.Typing
module MKeys   = Pulse.Checker.Prover.Match.MKeys

module RU  = Pulse.RuntimeUtils
module PS  = Pulse.Checker.Prover.Substs
module PTU = Pulse.Typing.Util

(* local aliases *)
let (>>>) #g #t0 #t1 #t2 = VE_Trans g t0 t1 t2
let (>>*) #g #t0 #t1 #t2 = slprop_list_equiv_trans g t0 t1 t2
let cong_r #g #t0 #t1 #t2 (d : slprop_equiv g t1 t2) : slprop_equiv g (t0 * t1) (t0 * t2) =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) d
let cong_l #g #t0 #t1 #t2 (d : slprop_equiv g t1 t2) : slprop_equiv g (t1 * t0) (t2 * t0) =
  VE_Ctxt _ _ _ _ _ d (VE_Refl _ _)
let ve_refl_pf (#g:env) (p q : slprop) (s : squash (p == q)) : slprop_equiv g p q = VE_Refl g p

//
// Call into the F* unifier to solve for uvs by unifying p and q
//
let try_solve_uvars (g:env) (uvs:env { disjoint uvs g }) (p q:term)
  : T.Tac (ss:PS.ss_t { PS.dom ss `Set.subset` freevars q }) =

  let uvs = uvs
    |> bindings_with_ppname
    |> L.rev
    |> L.map (fun (({name}, x, t):(ppname & _ & _)) ->
         let nv_view = {
           R.uniq = x;
           R.sort = t;
           R.ppname = name;
         } in
         let nv = R.pack_namedv nv_view in
         nv, t
       ) in

  let l, issues =
    RU.with_context (get_context g) (fun _ ->
      T.with_policy T.Force (fun () ->
        T.try_unify (elab_env g) uvs p q))
  in

  T.log_issues issues;

  // build ss
  let ss = PS.empty in
  assume (PS.dom ss `Set.subset` freevars q);
  match l with
  | None -> ss
  | Some l ->
    let q_names = freevars q in
    L.fold_left (fun (ss:(ss:PS.ss_t { PS.dom ss `Set.subset` freevars q })) (x, t) ->
      let nv_view = R.inspect_namedv x in
      if Set.mem nv_view.uniq q_names &&
         not (Set.mem nv_view.uniq (PS.dom ss))
      then begin
        let ss_new = PS.push ss nv_view.uniq t in
        assert (nv_view.uniq `Set.mem` freevars q);
        assert (PS.dom ss `Set.subset` freevars q);
        assume (PS.dom ss_new `Set.subset` freevars q);
        ss_new
      end
      else ss
    ) ss l

let rec unascribe (g:env) (t:term) : (t':term & erased (RT.equiv (elab_env g) t t')) =
  match R.inspect_ln t with
  | R.Tv_AscribedT t' _ _ _
  | R.Tv_AscribedC t' _ _ _ ->
    let tok : erased (RT.equiv (elab_env g) t t') = magic() in // Rel_ascribed?
    let (| t'', tok' |) = unascribe g t' in
    (| t'', hide <| RT.Rel_trans _ _ _ _ _ tok tok' |)
  | _ -> (| t, hide <| RT.Rel_refl _ _ _ |)

(* Syntactic equality check, but we also unascribe at the top level. Returns
an equality proof. *)
let eq_tm_unascribe (g:env) (p q:term) : option (erased (RT.equiv (elab_env g) p q)) =
  let (| up, ptok |) = unascribe g p in
  let (| uq, qtok |) = unascribe g q in
  if eq_tm up uq
  then (
    let t1 : erased (RT.equiv (elab_env g) p q) =
      let trans #t0 #t1 #t2
          (d1 : (RT.equiv (elab_env g) t0 t1))
          (d2 : (RT.equiv (elab_env g) t1 t2))
          : (RT.equiv (elab_env g) t0 t2)
          = RT.Rel_trans (elab_env g) _ _ _ RT.R_Eq d1 d2
      in
      ptok `trans` RT.Rel_refl _ _ _ `trans` RT.Rel_sym _ _ _ qtok
    in
    Some t1
  )
  else None

(**************** The actual matchers *)

open Pulse.VC

(* The syntactic matcher *)
let match_syntactic_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop)
  : T.Tac (match_res_t pst p q)
= (* term_eq gives us provable equality between p and q, so we can use VE_Refl. *)
  if TermEq.term_eq p q
  then Matched PS.empty Trivial (fun () -> VE_Refl _ _)
  else NoMatch "not term_eq"

(* Fast unification / strict matcher *)
let match_fastunif_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop)
  : T.Tac (match_res_t pst p q)
= match PTU.check_equiv_now_nosmt (elab_env pst.pg) p q with
  | Some tok, _ ->
    Matched PS.empty Trivial (fun () -> VE_Ext _ _ _ (RT.Rel_eq_token _ _ _ ()))
  | None, _ ->
    NoMatch "no unif"

let match_fastunif_inst_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop)
  : T.Tac (match_res_t pst p q)
= let g = pst.pg in
  let q0 = q in

  (* If the heads of p and q differ, skip. This makes sure we don't unfold
  stuff implicitly. *)
  if not <| MKeys.same_head p q then
    raise (ENoMatch "head mismatch");

  (* Try to instantiate q's uvars by matching it to p. We do not trust
  this call so we then typecheck the result (and normalize it too). *)
  let ss' = try_solve_uvars pst.pg pst.uvs p q in
  let q_subst = ss'.(q) in

  match PTU.check_equiv_now_nosmt (elab_env pst.pg) p q_subst with
  | None, issues ->
    if RU.debug_at_level (fstar_env g) "ggg" then
      info_doc_with_subissues g (Some <| range_of_env g) issues [
        text "match_fastunif_inst_11: check_equiv failed, no unif";
      ];
    raise (ENoMatch "no unif")

  | Some token, _ ->
    Matched ss' Trivial (fun _ -> VE_Ext _ _ _ (RT.Rel_eq_token _ _ _ ()))

let match_full_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : slprop)
  : T.Tac (match_res_t pst p q)
= let g = pst.pg in
  let q0 = q in

  (* Similar to fastunif_inst. Instead of unifiying without SMT,
     we check if the mkeys match. If so, we return a guarded result. *)

  if not <| MKeys.same_head p q then
    raise (ENoMatch "head mismatch");

  let ss' = try_solve_uvars pst.pg pst.uvs p q in
  let q_subst = ss'.(q) in

  (* Check now, after normalizing etc, that we are allowed to try an SMT query
  to match them. This is the part that looks at the binder attributes for strictness.
  If this check doesn't pass, skip. *)
  if not (MKeys.eligible_for_smt_equality g p q_subst) then
    raise (ENoMatch "not eligible for SMT");

  (* Return a guarded result *)
  Matched ss' (Equiv g p q_subst) (fun equiv -> VE_Ext _ _ _ equiv)
