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

module Pulse.Checker.Prover.Match

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory
open Pulse.Typing.Util
open Pulse.Checker.VPropEquiv
open Pulse.Checker.Prover.Base
open Pulse.Checker.Prover.Util

module RU = Pulse.RuntimeUtils
module L = FStar.List.Tot
module R = FStar.Reflection.V2
module TermEq = FStar.Reflection.V2.TermEq
module T = FStar.Tactics.V2

module RUtil = Pulse.Reflection.Util
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs
module Metatheory = Pulse.Typing.Metatheory

let rec equational (t:term) : bool =
  match R.inspect_ln t with
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

let is_smt_fallback (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_FVar fv ->
    let name = R.inspect_fv fv in
    name = ["Steel";"Effect";"Common";"smt_fallback"] ||
    name = ["Pulse"; "Lib"; "Core"; "equate_by_smt"]
  | _ -> false

(*
  When comparing t0 =?= t1, if they are not syntactically equal, we
  have to decide whether or not we should fire an SMT query to compare
  them for provable equality.

  The criterion is as follows:

  1. We allow an SMT query if either t0 or t1 is "equational". For now, that means
     that either is a match expression.

  2. Otherwise, if they are both applications of `f v0...vn` and `f u0...un`
     of the same head symbol `f`, a top-level constant, then we check if the
     type of `f` decorates any of its binders with the `smt_fallback` attribute. 

        - If none of them are marked as such,
          then we check if `f v0...` is syntactically equal to `f u0...`
          and allow an SMT query to check if vn = vm. That is, the default behavior
          for predicates is that they *last* argument is eligible for SMT equality.

        - Otherwise, for each binder that is NOT marked as `smt_fallback`, we check
          if the corresponding argument is syntactically equal. If so, we allow 
          t0 and t1 to be compared for SMT equality.

          For example, Steel.ST.Reference.pts_to is defined like so:

            /// For instance, [pts_to r (sum_perm (half_perm p) (half_perm p)) (v + 1)]
            /// is unifiable with [pts_to r p (1 + v)]
            val pts_to (#a:Type0)
                      (r:ref a)
                      ([@@@smt_fallback] p:perm)
                      ([@@@smt_fallback] v:a)
              : vprop
*)
let eligible_for_smt_equality (g:env) (t0 t1:term) 
  : T.Tac bool
  = let either_equational () = equational t0 || equational t1 in
    let head_eq (t0 t1:R.term) =
      match R.inspect_ln t0, R.inspect_ln t1 with
      | R.Tv_App h0 _, R.Tv_App h1 _ ->
        TermEq.term_eq h0 h1
      | _ -> false
    in
    match inspect_term t0, inspect_term t1 with
    | Some (Tm_ForallSL _ _ _), Some (Tm_ForallSL _ _ _) -> true
    | _ -> (
      let h0, args0 = R.collect_app_ln t0 in
      let h1, args1 = R.collect_app_ln t1 in
      if TermEq.term_eq h0 h1 && L.length args0 = L.length args1
      then (
        match R.inspect_ln h0 with
        | R.Tv_FVar fv
        | R.Tv_UInst fv _ -> (
          match type_of_fv g fv with
          | None -> either_equational()
          | Some t ->
            let bs, _ = R.collect_arr_ln_bs t in
            let is_smt_fallback (b:R.binder) = 
                let bview = R.inspect_binder b in
                L.existsb is_smt_fallback bview.attrs
            in
            let some_fallbacks, fallbacks =
              L.fold_right
                (fun b (some_fallbacks, bs) -> 
                  if is_smt_fallback b
                  then true, true::bs
                  else some_fallbacks, false::bs)
                bs (false, [])
            in
            if not some_fallbacks
            then (
                //if none of the binders are marked fallback
                //then, by default, consider only the last argument as
                //fallback
              head_eq t0 t1
            )
            else (
              let rec aux args0 args1 fallbacks =
                match args0, args1, fallbacks with
                | (a0, _)::args0, (a1, _)::args1, b::fallbacks -> 
                  if b
                  then aux args0 args1 fallbacks
                  else if not (TermEq.term_eq a0 a1)
                  then false
                  else aux args0 args1 fallbacks
                | [], [], [] -> true
                | _ -> either_equational() //unequal lengths
              in
              aux args0 args1 fallbacks
            )
        ) 
        | _ -> either_equational ()
      )
      else either_equational ()
    )
    | _ -> either_equational ()


let refl_uvar (t:R.term) (uvs:env) : option var =
  let open R in
  match inspect_ln t with
  | Tv_Var v ->
    let {uniq=n} = inspect_namedv v in
    if contains uvs n then Some n else None
  | _ -> None

let is_uvar (t:term) (uvs:env) : option var =
  refl_uvar t uvs


let contains_uvar (t:term) (uvs:env) (g:env) : T.Tac bool =
  not (check_disjoint uvs (freevars t))

let is_reveal_uvar (t:term) (uvs:env) : option (universe & term & var) =
  match is_pure_app t with
  | Some (hd, None, arg) ->
    (match is_pure_app hd with
     | Some (hd, Some Implicit, ty) ->
       let arg_uvar_index_opt = is_uvar arg uvs in
       (match arg_uvar_index_opt with
        | Some n ->
          (match is_fvar hd with
           | Some (l, [u]) ->
             if l = RUtil.reveal_lid
             then Some (u, ty, n)
             else None
           | _ -> None)
        | _ -> None)
     | _ -> None)
  | _ -> None

let is_reveal (t:term) : bool =
  match leftmost_head t with
  | Some hd ->
    (match is_fvar hd with
     | Some (l, [_]) -> l = RUtil.reveal_lid
     | _ -> false)
  | _ -> false

module RT = FStar.Reflection.Typing

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
           R.sort = elab_term t;
           R.ppname = name;
         } in
         let nv = R.pack_namedv nv_view in
         nv, elab_term t
       ) in

  let l, issues = RU.with_context (get_context g) (fun _ ->
    T.try_unify (elab_env g) uvs (elab_term p) (elab_term q))
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
      // let topt = readback_ty t in
      // match topt with
      // | Some t ->
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
      // | None -> ss
    ) ss l

let rec unascribe (t:term) : term =
  match R.inspect_ln t with
  | R.Tv_AscribedT t _ _ _
  | R.Tv_AscribedC t _ _ _ -> unascribe t
  | _ -> t

let unify (g:env) (uvs:env { disjoint uvs g})
  (p q:term)
  : T.Tac (ss:PS.ss_t { PS.dom ss `Set.subset` freevars q } &
           option (RT.equiv (elab_env g) (elab_term p) (elab_term ss.(q)))) =

  let ss = try_solve_uvars g uvs p q in
  let q_ss = ss.(q) in  // readback_ty (elab_term ss.(q)) in
  let q = q_ss in
  // match q_ss with
  // | None -> (| ss, None |)
  // | Some q -> 
    if eq_tm p q
    then (| ss, Some (RT.Rel_refl _ _ _) |)
    else if eq_tm (unascribe p) (unascribe q)
    then let _ = assume False in (| ss, Some (RT.Rel_refl _ _ _) |)
    else if contains_uvar q uvs g
    then (| ss, None |)
    else if eligible_for_smt_equality g p q
    then let v0 = elab_term p in
        let v1 = elab_term q in
        match check_equiv_now (elab_env g) v0 v1 with
        | Some token, _ -> (| ss, Some (RT.Rel_eq_token _ _ _ (FStar.Squash.return_squash token)) |)
        | None, _ -> (| ss, None |)
    else (| ss, None |)

let try_match_pq (g:env) (uvs:env { disjoint uvs g}) (p q:vprop)
  : T.Tac (ss:PS.ss_t { PS.dom ss `Set.subset` freevars q } &
           option (vprop_equiv g p ss.(q))) =

  let r = unify g uvs p q in
  match r with
  | (| ss, None |) -> (| ss, None |)
  | (| ss, Some _ |) -> (| ss, Some (RU.magic #(vprop_equiv _ _ _) ()) |)

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let match_step (#preamble:preamble) (pst:prover_state preamble)
  (p:vprop) (remaining_ctxt':list vprop)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.remaining_ctxt == p::remaining_ctxt' /\
             pst.unsolved == q::unsolved'))
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
assume (freevars q_ss `Set.disjoint` PS.dom pst.ss);

let (| ss_q, ropt |) = try_match_pq pst.pg pst.uvs p q_ss in

debug_prover pst.pg (fun _ ->
  Printf.sprintf "prover matcher: tried to match p %s and q (partially substituted) %s, result: %s"
    (P.term_to_string p) (P.term_to_string (ss_q.(q_ss))) (if None? ropt then "fail" else "success"));

match ropt with
| None -> None
| Some veq ->
  assert (PS.dom ss_q `Set.disjoint` PS.dom pst.ss);
  
  let ss_new = PS.push_ss pst.ss ss_q in

  let veq : vprop_equiv pst.pg p (ss_q.(pst.ss.(q))) = veq in

  assume (ss_q.(pst.ss.(q)) == ss_new.(q));
  let veq : vprop_equiv pst.pg p ss_new.(q) = coerce_eq veq () in

  let remaining_ctxt_new = remaining_ctxt' in
  let solved_new = q * pst.solved in
  let unsolved_new = unsolved' in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved)) = pst.k in

  assume (pst.ss.(pst.solved) == ss_new.(pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop (p::remaining_ctxt_new) * preamble.frame) * ss_new.(pst.solved)) =
    coerce_eq k () in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop remaining_ctxt_new * preamble.frame) * (ss_new.(q) * ss_new.(pst.solved))) =
    k_elab_equiv k (VE_Refl _ _) (RU.magic ()) in
  
  assume (ss_new.(q) * ss_new.(pst.solved) == ss_new.(q * pst.solved));

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst.pg ((list_as_vprop remaining_ctxt_new * preamble.frame) * (ss_new.(solved_new))) =
    coerce_eq k () in

  assume (freevars ss_new.(solved_new) `Set.subset` dom pst.pg);
  let pst' : prover_state preamble =
    { pst with remaining_ctxt=remaining_ctxt_new;
               remaining_ctxt_frame_typing=RU.magic ();
               ss=ss_new;
               nts=None;
               solved=solved_new;
               unsolved=unsolved_new;
               k;
               goals_inv=RU.magic ();
               solved_inv=() } in

  assume (ss_new `ss_extends` pst.ss);
  Some pst'

let move_hd_end (g:env) (l:list vprop { Cons? l })
  : vprop_equiv g (list_as_vprop l) (list_as_vprop (L.tl l @ [L.hd l])) = RU.magic ()

let remaining_ctxt_equiv_pst (#preamble:_) (pst:prover_state preamble) (remaining_ctxt':list vprop)
  (d:vprop_equiv pst.pg (list_as_vprop pst.remaining_ctxt) (list_as_vprop remaining_ctxt'))
  : prover_state preamble =
  { pst with remaining_ctxt = remaining_ctxt';
             remaining_ctxt_frame_typing = RU.magic ();
             k = k_elab_equiv pst.k (VE_Refl _ _) (RU.magic ()) }

let rec match_q_aux (#preamble:_) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (i:nat)
  : T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

  if L.length pst.remaining_ctxt = 0
  then None
  else if i = L.length pst.remaining_ctxt
  then None
  else
    let p = L.hd pst.remaining_ctxt in
    let pst_opt =
      match_step pst p (L.tl pst.remaining_ctxt) q unsolved' () in
    match pst_opt with
    | Some pst -> Some pst
    | None ->
      let pst =
        remaining_ctxt_equiv_pst pst (L.tl pst.remaining_ctxt @ [L.hd pst.remaining_ctxt])
          (move_hd_end pst.pg pst.remaining_ctxt) in
      match_q_aux pst q unsolved' () (i+1)

//
// THIS SHOULD GO AWAY SOON
//
let ___canon___ (q:vprop) : Dv (r:vprop { r == q }) = q
  // assume False;
  // match Pulse.Readback.readback_ty (elab_term q) with
  // | None -> q
  // | Some q -> q

let has_structure (q:vprop) : bool =
  match inspect_term q with
  | Some (Tm_Star _ _) -> true
  | _ -> false

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 2"
let match_q (#preamble:preamble) (pst:prover_state preamble)
  (q:vprop) (unsolved':list vprop)
  (_:squash (pst.unsolved == q::unsolved'))
  (prover:prover_t)
: T.Tac (option (pst':prover_state preamble { pst' `pst_extends` pst })) =

let q_ss = pst.ss.(q) in
let q_ss = ___canon___ q_ss in

if has_structure q_ss
then begin
  let preamble_sub = {
    g0 = pst.pg;
    ctxt = list_as_vprop pst.remaining_ctxt;
    frame = preamble.frame * pst.ss.(pst.solved);
    ctxt_frame_typing = RU.magic ();
    goals = q_ss * (list_as_vprop unsolved');
  } in
  let k_sub:
    continuation_elaborator
      preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
      pst.pg ((list_as_vprop (vprop_as_list preamble_sub.ctxt) * preamble_sub.frame) * pst.ss.(tm_emp)) =
    let k = k_elab_unit preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame) in
    let k = k_elab_equiv k
      (VE_Refl _ _)
      (RU.magic () <:
         vprop_equiv
           preamble_sub.g0
           (preamble_sub.ctxt * preamble_sub.frame)
           ((list_as_vprop (vprop_as_list preamble_sub.ctxt) * preamble_sub.frame) * pst.ss.(tm_emp))) in
    coerce_eq k ()
  in
  assume (pst.ss.(tm_emp) == tm_emp);
  let pst_sub : prover_state preamble_sub = {
    pg = pst.pg;
    remaining_ctxt = vprop_as_list preamble_sub.ctxt;
    remaining_ctxt_frame_typing = RU.magic ();
    uvs = pst.uvs;
    ss = pst.ss;
    nts = None;
    solved = tm_emp;
    unsolved = vprop_as_list q_ss;
    k = k_sub;
    goals_inv = RU.magic ();
    solved_inv = ();
  } in

  let pst_sub = prover pst_sub in
  assert (pst_sub.unsolved == []);
  assert (pst_sub.ss `ss_extends` pst.ss);

  let k_sub : continuation_elaborator 
    pst.pg (list_as_vprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved))) * pst_sub.ss.(pst_sub.solved)) =
    pst_sub.k in

  // AC
  let k_pre_eq : vprop_equiv pst.pg
    (list_as_vprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
    ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved)) = RU.magic () in
  
  // AC
  let k_post_equiv : vprop_equiv pst_sub.pg
    ((list_as_vprop pst_sub.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved))) * pst_sub.ss.(pst_sub.solved))
    ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(pst_sub.solved) * pst.ss.(pst.solved))) = RU.magic () in

  let k_sub : continuation_elaborator
    pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(pst_sub.solved) * pst.ss.(pst.solved))) =
    k_elab_equiv k_sub k_pre_eq k_post_equiv in

  let pst_sub_goals_inv : vprop_equiv (push_env pst_sub.pg pst_sub.uvs)
    (q_ss * (list_as_vprop unsolved'))
    (list_as_vprop [] * pst_sub.solved) = pst_sub.goals_inv in

  let (| nt, effect_labels |)
    : nts:PS.nt_substs &
      effect_labels:list T.tot_or_ghost {
        PS.well_typed_nt_substs pst_sub.pg pst_sub.uvs nts effect_labels /\
        PS.is_permutation nts pst_sub.ss
  } =
    match pst_sub.nts with
    | Some r -> r
    | None ->
      let r = PS.ss_to_nt_substs pst_sub.pg pst_sub.uvs pst_sub.ss in
      match r with
      | Inr msg ->
        fail pst_sub.pg None
          (Printf.sprintf
             "resulted substitution after match protocol is not well-typed: %s"
             msg)
      | Inl nt -> nt in
  assert (PS.well_typed_nt_substs pst_sub.pg pst_sub.uvs nt effect_labels);

  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(q_ss * (list_as_vprop unsolved'))
                  pst_sub.ss.(list_as_vprop [] * pst_sub.solved) =
    PS.vprop_equiv_nt_substs_derived pst_sub.pg pst_sub.uvs pst_sub_goals_inv nt effect_labels in

  let emp_equiv : vprop_equiv pst_sub.pg
    pst_sub.ss.(list_as_vprop [] * pst_sub.solved)
    pst_sub.ss.(pst_sub.solved) = RU.magic () in

  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(q_ss * (list_as_vprop unsolved'))
                  pst_sub.ss.(pst_sub.solved) = VE_Trans _ _ _ _ pst_sub_goals_inv emp_equiv in

  // This assume is saying pst_sub.ss.(q) == pst_sub.ss.(ss.(q)),
  //   since pst_sub.ss extends ss
  assert (pst_sub.ss `ss_extends` pst.ss);
  assume (pst_sub.ss.(pst.ss.(q) * (list_as_vprop unsolved')) == pst_sub.ss.(q * list_as_vprop unsolved'));

  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(q * (list_as_vprop unsolved'))
                  pst_sub.ss.(pst_sub.solved) = coerce_eq pst_sub_goals_inv () in

  // In the relation above, play with q * (list_as_vprop unsolved') ~
  //                                  list_as_vprop (q::unsolved')
  assert (q::unsolved' == pst.unsolved);
  let pst_sub_goals_inv
    : vprop_equiv pst_sub.pg
                  pst_sub.ss.(list_as_vprop pst.unsolved)
                  pst_sub.ss.(pst_sub.solved) = RU.magic () in
  
  // The two sides are same, except for pst_sub.solved and list_as_vprop pst.unsolved part,
  //   which comes from the relation above  
  let k_sub_q_equiv : vprop_equiv pst_sub.pg
      ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(pst_sub.solved) * pst.ss.(pst.solved)))
      ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(list_as_vprop pst.unsolved) * pst.ss.(pst.solved))) =
      RU.magic () in

  let k_sub : continuation_elaborator
    pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(list_as_vprop pst.unsolved) * pst.ss.(pst.solved))) =
    k_elab_equiv k_sub (VE_Refl _ _) k_sub_q_equiv in

  // pst.ss.(pst.solved) has no uvs
  assume (pst.ss.(pst.solved) == pst_sub.ss.(pst.solved));

  // ss. commutes
  assume (pst_sub.ss.(list_as_vprop pst.unsolved) * pst_sub.ss.(pst.solved) ==
          pst_sub.ss.(list_as_vprop pst.unsolved * pst.solved));

  let k_sub : continuation_elaborator
    pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(list_as_vprop pst.unsolved * pst.solved))) =
    coerce_eq k_sub () in

  let goals_inv
    : vprop_equiv (push_env pst.pg pst.uvs)
                  preamble.goals
                  (list_as_vprop pst.unsolved * pst.solved) =
    pst.goals_inv in

  // weakening
  let goals_inv
    : vprop_equiv (push_env pst_sub.pg pst_sub.uvs)
                  preamble.goals
                  (list_as_vprop pst.unsolved * pst.solved) =
    let d = Metatheory.veq_weakening pst.pg pst.uvs goals_inv pst_sub.pg in
    Metatheory.veq_weakening_end pst_sub.pg pst.uvs d pst_sub.uvs in

  let goals_inv
    : vprop_equiv pst_sub.pg
                  (pst_sub.ss.(preamble.goals))
                  (pst_sub.ss.(list_as_vprop pst.unsolved * pst.solved)) =
    PS.vprop_equiv_nt_substs_derived pst_sub.pg pst_sub.uvs goals_inv nt effect_labels in
 
  // replace list_as_vprop pst.unsolved * pst.solved with preamble.goals using goals_inv
  let k_sub_q_equiv : vprop_equiv pst_sub.pg
    ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(list_as_vprop pst.unsolved * pst.solved)))
    ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(preamble.goals))) =
    RU.magic () in

  let k_sub : continuation_elaborator
    pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * (pst_sub.ss.(preamble.goals))) =
    k_elab_equiv k_sub (VE_Refl _ _) k_sub_q_equiv in

  let k : continuation_elaborator
    preamble.g0 (preamble.ctxt * preamble.frame)
    pst_sub.pg ((list_as_vprop pst_sub.remaining_ctxt * preamble.frame) * pst_sub.ss.(preamble.goals)) =
    k_elab_trans pst.k k_sub in

  let pst' : prover_state preamble = {
    pg = pst_sub.pg;
    remaining_ctxt = pst_sub.remaining_ctxt;
    remaining_ctxt_frame_typing = RU.magic ();
    uvs = pst_sub.uvs;
    ss = pst_sub.ss;
    nts = Some (| nt, effect_labels |);
    solved = preamble.goals;
    unsolved = [];
    k;
    goals_inv = RU.magic ();
    solved_inv = RU.magic ();
  } in

  Some pst'
end
else match_q_aux pst q unsolved' () 0
