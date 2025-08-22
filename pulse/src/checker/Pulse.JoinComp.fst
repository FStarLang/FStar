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

module Pulse.JoinComp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover
open FStar.List.Tot
open Pulse.Show
module T = FStar.Tactics.V2
module MKeys = Pulse.Checker.Prover.Match.MKeys
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module RU = Pulse.RuntimeUtils

let mk_imp lhs rhs =
  let open R in
  let implies_lid = ["Prims"; "l_imp"] in
  let hd = R.pack_ln (Tv_FVar (R.pack_fv implies_lid)) in
  R.mk_app hd [(lhs, Q_Explicit); (rhs, Q_Explicit)]

let rec guard_pures then_ b (ps:list slprop) 
: list slprop & list slprop
= let guard_pure pp =
    let def () = 
      let payload =
        if then_ then mk_imp (RT.eq2 u0 tm_bool b tm_true) pp
        else mk_imp (RT.eq2 u0 tm_bool b tm_false) pp
      in
      pack_term_view (Tm_Pure payload) (T.range_of_term pp)
    in    
    let hd, args = T.collect_app_ln pp in
    match R.inspect_ln hd, args with
    | R.Tv_UInst _ _, [(ty, _); _; _] -> //no need to retain unit equalities
      if FStar.Reflection.TermEq.term_eq hd (`(Prims.eq2 u#0))
      && FStar.Reflection.TermEq.term_eq ty (`Prims.unit)
      then tm_emp
      else def()
    | _ -> def ()
  in
  let guard_pures = guard_pures then_ in
  match ps with
  | [] -> [], []
  | p::ps -> (
    match inspect_term p with
    | Tm_Pure pp -> (
      let pure = guard_pure pp in
      let pures, ps = guard_pures b ps in
      pure::pures, ps
    )
  
    | _ ->
      let pures, ps = guard_pures b ps in
      pures, p::ps
  )

let may_match g (p:slprop) (q:slprop) = MKeys.eligible_for_smt_equality g p q

let find_match g (p:slprop) (qs:list slprop)
: T.Tac (list (slprop & slprop) & list slprop & list slprop)
= let rec aux qs rest 
  : T.Tac (list (slprop & slprop) & list slprop & list slprop)
  = match qs with
    | [] -> [], [p], rest

    | q::qs ->
      if may_match g p q 
      then [p,q], [], qs@rest
      else (
        match inspect_term p, inspect_term q with
        | Tm_Pure _, Tm_Pure _ -> [p,q], [], qs@rest
        | _ -> aux qs (q::rest)
      )
  in
  aux qs []

let partition_matches g (ps qs:list slprop)
: T.Tac (list (slprop & slprop) & list slprop & list slprop)
= T.fold_right 
    (fun p (matches, remaining_ps, remaining_qs) ->
      let matches', remaining_ps', remaining_qs = find_match g p remaining_qs in
      matches'@matches, remaining_ps'@remaining_ps, remaining_qs)
    ps ([], [], qs)

let rec combine_terms top g b pq : T.Tac term =
  let p, q = pq in
  Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Combine terms %s and %s\n" (show p) (show q)
  );
  let pack t = pack_term_view t (T.range_of_term p) in
  let combine_terms p q = combine_terms true g b (p, q) in
  let def () = if T.term_eq p q then p else RT.mk_if b p q in
  match inspect_term p, inspect_term q with
  | Tm_Emp, Tm_Emp
  | Tm_SLProp, Tm_SLProp
  | Tm_EmpInames, Tm_EmpInames
  | Tm_Inames, Tm_Inames -> p
  | Tm_Pure f1, Tm_Pure f2 ->
    let f = RT.mk_if b f1 f2 in
    pack <| Tm_Pure f
  | Tm_Inv i1 p1, Tm_Inv i2 p2 ->
    pack <| Tm_Inv (combine_terms i1 i2) (combine_terms p1 p2)
  | Tm_FStar f1, Tm_FStar f2 -> (
    if not top then def () else
    let hd1, args1 = T.collect_app_ln f1 in
    let hd2, args2 = T.collect_app_ln f2 in //not proving termination because collect_app_ln's type is not strong enough
    Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
      Printf.sprintf "Destructed\nlhs as %s [%s]\nrhs as %s [%s]"
        (show hd1) (show args1)
        (show hd2) (show args2)
    );
    if T.term_eq hd1 hd2
    then T.mk_app hd1 (combine_args g b args1 args2)
    else def ()
  )
  | _ -> def ()

and combine_args g b (args1 args2:list R.argv) : T.Tac (list R.argv) =
  //combinine args, when heads are equal, 
  //the quals must be equal and the lengths must be equal
  match args1, args2 with
  | (a1, v1)::args1, (a2, v2)::args2 ->
    (combine_terms true g b (a1, a2), v1)::combine_args g b args1 args2
  | _ -> []

let join_slprop g b (ex1 ex2:list (universe & binder)) (p1 p2:slprop)
: T.Tac slprop
= match inspect_term p1, inspect_term p2 with
  | Tm_ExistsSL .., _
  | Tm_ForallSL .., _
  | _, Tm_ExistsSL ..
  | _, Tm_ForallSL .. ->
    //Not doing anything interesting to share binders
    RT.mk_if b p1 p2

  | _ ->
    let open Pulse.Show in
    let p1s, p2s = slprop_as_list p1, slprop_as_list p2 in
    let matches, p1s, p2s = partition_matches g p1s p2s in
    Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
      Printf.sprintf
        "Matches: %s\nRemaining ps=%s\nRemaining qs=%s\n"
          (show matches)
          (show p1s)
          (show p2s)
    );
    let matched = T.map (fun x -> combine_terms true g b x) matches in
    let pures1, p1s = guard_pures true b p1s in
    let pures2, p2s = guard_pures false b p2s in
    match p1s, p2s with
    | [], [] -> list_as_slprop (pures1@pures2@matched)
    | _ ->
      let remaining = RT.mk_if b (list_as_slprop p1s) (list_as_slprop p2s) in
      list_as_slprop (remaining::pures1@pures2@matched)

let rec join_effect_annot g (e1 e2:effect_annot)
: T.Tac (e:effect_annot & effect_annot_typing g e)
= match e1, e2 with
  | _, EffectAnnotSTT
  | EffectAnnotSTT, _ -> (| EffectAnnotSTT, () |)
  
  | EffectAnnotGhost { opens=o1 }, EffectAnnotGhost { opens=o2 } ->
    let o = tm_join_inames o1 o2 in
    let ty = Pulse.Checker.Pure.core_check_term g o RT.E_Total tm_inames in
    let e = EffectAnnotGhost { opens = o } in
    (| e, ty |)
  | EffectAnnotAtomic { opens=o1 }, EffectAnnotAtomic { opens=o2 } ->
    let o = tm_join_inames o1 o2 in
    let ty = Pulse.Checker.Pure.core_check_term g o RT.E_Total tm_inames in
    let e = EffectAnnotAtomic { opens = o } in
    (| e, ty |)
  | EffectAnnotAtomicOrGhost { opens=o1 }, EffectAnnotAtomicOrGhost { opens=o2 } ->
    let o = tm_join_inames o1 o2 in
    let ty = Pulse.Checker.Pure.core_check_term g o RT.E_Total tm_inames in
    let e = EffectAnnotAtomicOrGhost { opens = o } in
    (| e, ty |)

  | EffectAnnotAtomicOrGhost { opens=o1 }, EffectAnnotGhost _ ->
    join_effect_annot g (EffectAnnotGhost {opens=o1}) e2

  | EffectAnnotAtomicOrGhost { opens=o1 }, EffectAnnotAtomic _ ->
    join_effect_annot g (EffectAnnotAtomic {opens=o1}) e2

  | EffectAnnotAtomic _, EffectAnnotAtomicOrGhost { opens=o2 } ->
    join_effect_annot g e1 (EffectAnnotAtomicOrGhost {opens=o2})

  | EffectAnnotGhost _, EffectAnnotAtomicOrGhost { opens=o2 } ->
    join_effect_annot g e1 (EffectAnnotGhost {opens=o2})

  | _ -> 
    let open Pulse.PP in
    let open Pulse.Show in
    fail_doc g (Some <| range_of_env g)
      [text "Could not combine effect annotations";
       text (Printf.sprintf "Effect of then-branch is %s" (show e1));
       text (Printf.sprintf "Effect of else-branch is %s" (show e2))]

let join_post #g #hyp #b
    (p1:post_hint_for_env (g_with_eq g hyp b tm_true))
    (p2:post_hint_for_env (g_with_eq g hyp b tm_false))
: T.Tac (post_hint_for_env g)
= Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Joining postconditions:\n%s\nand\n%s\n"
      (T.term_to_string p1.post)
      (T.term_to_string p2.post)
  );
  if not (T.term_eq p1.ret_ty p2.ret_ty)
  then (
    fail_doc g (Some (T.range_of_term p1.ret_ty))
      Pulse.PP.(
        [text "The branches of a conditional must return the same type";
         text (Printf.sprintf "The types %s and %s are not equal" (T.term_to_string p1.ret_ty) (T.term_to_string p2.ret_ty))]
      )
  );
  let x = fresh g in
  let p1_post = open_term_nv p1.post (ppname_default, x) in
  let (| p1_post, _ |) = 
    Pulse.Checker.Prover.normalize_slprop 
      (push_binding_def g x p1.ret_ty) 
      p1_post true 
  in
  let p2_post = open_term_nv p2.post (ppname_default, x) in
  let (| p2_post, _ |) =
    Pulse.Checker.Prover.normalize_slprop 
      (push_binding_def g x p1.ret_ty) 
      p2_post true 
  in
  let joined_post = join_slprop g b [] [] p1_post p2_post in
  let joined_post = close_term joined_post x in
  Pulse.Checker.Util.debug g "pulse.join_comp" (fun _ ->
    Printf.sprintf "Inferred joint postcondition:\n%s\n"
      (T.term_to_string joined_post)
  );
  assume (fresh_wrt x g (freevars joined_post));
  let (| u, ty_typing |) = Pulse.Checker.Pure.check_universe g p1.ret_ty in
  let joined_post' = open_term_nv joined_post (ppname_default, x) in 
  let g' = push_binding g x ppname_default p1.ret_ty in
  let post_typing_src = Pulse.Checker.Pure.check_slprop_with_core g' joined_post' in
  let (| eff, eff_ty |) = join_effect_annot g p1.effect_annot p2.effect_annot in
  let res : post_hint_for_env g =
    {g; effect_annot=eff; effect_annot_typing=eff_ty;
     ret_ty=p1.ret_ty; u=u; ty_typing; x;
     post=joined_post; post_typing_src; post_typing=RU.magic()}
  in
  res


let st_ghost_as_atomic_matches_post_hint
  (c:comp { C_STGhost? c })
  (post:post_hint_t { EffectAnnotAtomicOrGhost? post.effect_annot })
  : Lemma (requires comp_post_matches_hint c (PostHint post))
          (ensures comp_post_matches_hint (st_ghost_as_atomic c) (PostHint post)) = ()

(* This matches the effects of the two branches, without
necessarily matching inames. *)
#push-options "--z3rlimit_factor 8"
#restart-solver
open Pulse.Checker.Base
(* NB: g_then and g_else are equal except for containing one extra
hypothesis according to which branch was taken. *)
let rec join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  (post:post_hint_t)
  : TacS (c:comp_st &
          st_typing g_then e_then c &
          st_typing g_else e_else c)
         (requires
            comp_post_matches_hint c_then (PostHint post) /\
            comp_post_matches_hint c_else (PostHint post) /\
            comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) ->
           st_comp_of_comp c == st_comp_of_comp c_then /\
           comp_post_matches_hint c (PostHint post))
= let g = g_then in
  assert (st_comp_of_comp c_then == st_comp_of_comp c_else);
  match c_then, c_else with
  | C_STAtomic _ obs1 _, C_STAtomic _ obs2 _ ->
    let obs = join_obs obs1 obs2 in
    let e_then_typing = T_Lift _ _ _ _ e_then_typing (Lift_Observability g_then c_then obs) in
    let e_else_typing = T_Lift _ _ _ _ e_else_typing (Lift_Observability g_else c_else obs) in
    (| _, e_then_typing, e_else_typing |)
  | C_STGhost _ _, C_STGhost _ _
  | C_ST _, C_ST _ -> (| _, e_then_typing, e_else_typing |)

  | _ ->
    assert (EffectAnnotAtomicOrGhost? post.effect_annot);
    match c_then, c_else with
    | C_STGhost _ _, C_STAtomic _ _ _ ->
      let d : st_typing g_then e_then (st_ghost_as_atomic c_then) =
        lift_ghost_atomic e_then_typing in
      st_ghost_as_atomic_matches_post_hint c_then post;
      join_comps _ _ _ d _ _ _ e_else_typing post

    | C_STAtomic _ _ _, C_STGhost _ _ ->
      let d = lift_ghost_atomic e_else_typing in
      st_ghost_as_atomic_matches_post_hint c_else post;
      join_comps _ _ _ e_then_typing _ _ _ d post
#pop-options
