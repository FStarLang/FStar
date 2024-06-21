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

module T       = FStar.Tactics.V2
module R       = FStar.Reflection.V2
module L       = FStar.List.Tot
module TermEq  = FStar.Reflection.V2.TermEq
module RT      = FStar.Reflection.Typing

module RU  = Pulse.RuntimeUtils
module P   = Pulse.Syntax.Printer
module PS  = Pulse.Checker.Prover.Substs
module PTU = Pulse.Typing.Util

(* local aliases *)
let (>>>) #g #t0 #t1 #t2 = VE_Trans g t0 t1 t2
let (>>*) #g #t0 #t1 #t2 = vprop_list_equiv_trans g t0 t1 t2
let cong_r #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t0 * t1) (t0 * t2) =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) d
let cong_l #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t1 * t0) (t2 * t0) =
  VE_Ctxt _ _ _ _ _ d (VE_Refl _ _)
let ve_refl_pf (#g:env) (p q : vprop) (s : squash (p == q)) : vprop_equiv g p q = VE_Refl g p

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

type matching_kind =
  | Syntactic
  | Strict
  | Full

let is_equate_by_smt (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Pulse"; "Lib"; "Core"; "equate_by_smt"]
  | _ -> false

let is_equate_strict (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Pulse"; "Lib"; "Core"; "equate_strict"]
  | _ -> false

let is_equate_syntactic (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Pulse"; "Lib"; "Core"; "equate_syntactic"]
  | _ -> false

(* Gets the strictest matching kind from a list of attributes. *)
let matching_kind_from_attr (ats : list term) : matching_kind =
  if L.existsb is_equate_syntactic ats then Syntactic
  else if L.existsb is_equate_strict ats then Strict
  else Full

let rec zip3 (l1:list 'a) (l2:list 'b) (l3:list 'c) : T.Tac (list ('a & 'b & 'c)) =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (x, y, z) :: zip3 xs ys zs
  | _, _, _ ->
    T.fail "zip3: length mismatch"

let same_head (g:env) (t0 t1:term)
  : T.Tac bool
  = match T.hua t0, T.hua t1 with
    | Some (h0, us0, args0), Some (h1, us1, args1) ->
      T.inspect_fv h0 = T.inspect_fv h1 &&
      L.length args0 = L.length args1
    | _ ->
      true // conservative

let eligible_for_smt_equality (g:env) (t0 t1:term) 
  : T.Tac bool
  = let either_equational () = equational t0 || equational t1 in
    let term_eq t0 t1 = TermEq.term_eq t0 t1 in
    if term_eq t0 t1 || either_equational () then true
    else
    match inspect_term t0, inspect_term t1 with
    | Tm_ForallSL _ _ _, Tm_ForallSL _ _ _ -> true
    | _ -> (
      let h0, args0 = R.collect_app_ln t0 in
      let h1, args1 = R.collect_app_ln t1 in
      if term_eq h0 h1 && L.length args0 = L.length args1
      then (
        match R.inspect_ln h0 with
        | R.Tv_FVar fv
        | R.Tv_UInst fv _ -> (
          match type_of_fv g fv with
          | None -> false
          | Some t ->
            let bs, _ = R.collect_arr_ln_bs t in
            if L.length bs <> L.length args0
            then false
            else (
              let bs_args0_args1 = zip3 bs args0 args1 in
              T.fold_right (fun (b, (a0, _), (a1, _)) acc ->
                if not acc then false else
                let ats = (R.inspect_binder b).attrs in
                match matching_kind_from_attr ats with
                | Syntactic -> term_eq a0 a1
                | Strict -> begin
                  try
                    Some? (fst (PTU.check_equiv_now_nosmt (elab_env g) a0 a1))
                  with | _ -> false
                  end

                | Full -> true
              ) bs_args0_args1 true
            )
          )
        | _ -> false
      )
      else false
    )
    | _ -> false

let refl_uvar (t:R.term) (uvs:env) : option var =
  let open R in
  match inspect_ln t with
  | Tv_Var v ->
    let {uniq=n} = inspect_namedv v in
    if contains uvs n then Some n else None
  | _ -> None

let is_uvar (t:term) (uvs:env) : option var = refl_uvar t uvs

let contains_uvar (t:term) (uvs:env) (g:env) : T.Tac bool =
  not (check_disjoint uvs (freevars t))

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
      T.with_policy T.ForceSMT (fun () ->
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

let try_unif_nosmt (g:env) (p q:term) : T.Tac (option (T.equiv_token (elab_env g) p q) & T.issues) =
  let hp, args_p = R.collect_app_ln p in
  let hq, args_q = R.collect_app_ln q in
  if RU.debug_at_level (fstar_env g) "ggg" then
    info_doc g (Some <| range_of_env g) [
      text "try_unify_nosmt";
      text "p: " ^^ pp p;
      text "q: " ^^ pp q;
    ];
  let r =
    (* We only try to unify if the heads syntactically match. *)
    if TermEq.term_eq hp hq then
      PTU.check_equiv_now_nosmt (elab_env g) p q
    else
      None, []
  in
  // if RU.debug_at_level (fstar_env g) "ggg" then
  // info_doc g (Some <| range_of_env g) [
  //   text "Unification result:";
  //   text "p: " ^^ pp p;
  //   text "q: " ^^ pp q;
  //   text "result: " ^^ (arbitrary_string <| Pulse.Show.show (Some? (fst r), List.length (snd r) <: bool & int));
  // ];
  r

let head_is_uvar (uvs:env) (t:term) : T.Tac bool =
  let hd, _ = T.collect_app t in
  match T.inspect hd with
  | T.Tv_Var v ->
    List.existsb (fun (x, _) -> x = v.uniq) (bindings uvs)
  | _ -> false

(**************** The actual matchers *)

(* The syntactic matcher *)
let match_syntactic_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : vprop)
  : T.Tac (match_success_t pst p q)
= (* term_eq gives us provable equality between p and q, so we can use VE_Refl. *)
  if TermEq.term_eq p q
  then (| PS.empty, VE_Refl _ _ |)
  else raise (NoMatch "not term_eq")

(* Fast unification / strict matcher *)
let match_fastunif_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : vprop)
  : T.Tac (match_success_t pst p q)
= match PTU.check_equiv_now_nosmt (elab_env pst.pg) p q with
  | Some tok, _ -> (| PS.empty, VE_Ext _ _ _ tok |)
  | None, _ -> raise (NoMatch "no unif")

let match_fastunif_inst_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : vprop)
  : T.Tac (match_success_t pst p q)
= let g = pst.pg in
  let q0 = q in

  (* If q is just a unification variable, skip this, it is most definitely
  ambiguous to try to solve it. *)
  // if head_is_uvar pst.uvs q then
  //   raise (NoMatch "head of q is uvar");

  (* If the heads of p and q differ, skip. *)
  if not <| same_head pst.pg p q then
    raise (NoMatch "head mismatch");

  (* Try to instantiate q's uvars by matching it to p. We do not trust
  this call so we then typecheck the result (and normalize it too). *)
  // T.dump "GG1";
  let ss' = try_solve_uvars pst.pg pst.uvs p q in
  // T.dump "GG2";
  let q_subst = ss'.(q) in
  let q_norm =
    (* First typecheck q_subst and then normalize it. If it
    fails to typecheck, say due to a bad solution of uvars by try_solve_uvars,
    then we must also fail here. Hence we use ForceSMT to not batch these queries. *)
    match T.with_policy T.ForceSMT (fun () -> T.tc_term (elab_env g) q_subst) with
    | Some (q_subst', _), [] ->
      T.norm_well_typed_term (elab_env g)
        [Pervasives.unascribe; primops; iota]
        q_subst'
    | _ ->
      // bad uvars, just ignore
      raise (NoMatch "uvar solution did not check")
  in

  if RU.debug_at_level (fstar_env g) "ggg" then
    info_doc g (Some <| range_of_env g) [
      text "match_fastunif_inst_11";
      text "p: " ^^ pp p;
      text "q: " ^^ pp q;
      text "q_subst: " ^^ pp q_subst;
      text "q_norm: " ^^ pp q_norm;
    ];

  match PTU.check_equiv_now_nosmt (elab_env pst.pg) p q_norm with
  | Some tok, _ ->
    (| ss', VE_Ext _ _ _ (RU.magic ()) |)
  | None, _ -> raise (NoMatch "no unif")

(* Full unification with SMT. Also can instantiate uvars (strict should maybe
also do this?). *)
let match_full_11
  (#preamble:_) (pst : prover_state preamble)
  (p q : vprop)
  : T.Tac (match_success_t pst p q)
= let g = pst.pg in
  let q0 = q in

  (* If q is just a unification variable, skip this, it is most definitely
  ambiguous to try to solve it. *)
  // if head_is_uvar pst.uvs q then
  //   raise (NoMatch "head of q is uvar");

  (* If the heads of p and q differ, skip. *)
  if not <| same_head pst.pg p q then
    raise (NoMatch "head mismatch");
  
  (* Try to instantiate q's uvars by matching it to p. We do not trust
  this call so we then typecheck the result (and normalize it too). *)
  let ss' = try_solve_uvars pst.pg pst.uvs p q in
  let q_subst = ss'.(q) in
  let q_norm =
    (* First typecheck q_subst and then normalize it. If it
    fails to typecheck, say due to a bad solution of uvars by try_solve_uvars,
    then we must also fail here. Hence we use ForceSMT to not batch these queries. *)
    match T.with_policy T.ForceSMT (fun () -> T.tc_term (elab_env g) q_subst) with
    | Some (q_subst', _), [] ->
      T.norm_well_typed_term (elab_env g)
        [Pervasives.unascribe; primops; iota]
        q_subst'
    | _ ->
      // bad uvars, just ignore
      raise (NoMatch "uvar solution did not check")
  in

  (* FIXME: extend reflection typing to provide the token. The norm_well_typed_term
  calls gives us a squashed one (which is ok) but tc_term does not. *)
  let q_subst_eq_q_norm : erased (equiv_token (elab_env g) q_subst q_norm) = magic () in

  (* Check now, after normalizing etc, that we are allowed to try an SMT query
  to match them. This is the part that looks at the binder attributes for strictness.
  If this check doesn't pass, skip. *)
  if not (eligible_for_smt_equality g p q_norm) then
    raise (NoMatch "not eligible for SMT");

  (* Finally, try to match and construct proof. *)
  match PTU.check_equiv_now (elab_env g) p q_norm with
  | None, _ -> raise (NoMatch "no unif")
  | Some token, _ ->
    let p_eq_q_norm : vprop_equiv g p q_norm  = VE_Ext _ _ _ token in
    let p_eq_q      : vprop_equiv g p q_subst =
      p_eq_q_norm >>> VE_Sym _ _ _ (VE_Ext _ _ _ q_subst_eq_q_norm)
    in
    (| ss', p_eq_q |) 
