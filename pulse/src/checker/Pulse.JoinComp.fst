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
  T.print (
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
    T.print (
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
  | _, Tm_ForallSL .. -> RT.mk_if b p1 p2
    // let x1 = fresh g in
    // let p1 = open_term_nv p1 (b1.binder_ppname, x1) in
    // join_slprop g b ((u1, b1, p1)::ex1) ex2 p1 p2

  // | _, Tm_ExistsSL u2 b2 p2 ->
  //   let x2 = fresh g in
  //   let p2 = open_term_nv p2 (b2.binder_ppname, x2) in
  //   join_slprop g b ex1 ((u2, b2, p2)::ex2) p1 p2

  | _ ->
    let open Pulse.Show in
    let p1s, p2s = slprop_as_list p1, slprop_as_list p2 in
    let matches, p1s, p2s = partition_matches g p1s p2s in
    T.print (
      Printf.sprintf
        "Matches: %s\nRemaining ps=%s\nRemaining qs=%s\n"
          (show matches)
          (show p1s)
          (show p2s)
    );
    let matched = T.map (fun x -> combine_terms true g b x) matches in
    match p1s, p2s with
    | [], [] -> list_as_slprop matched
    | _ ->
      let remaining = RT.mk_if b (list_as_slprop p1s) (list_as_slprop p2s) in
      list_as_slprop (remaining::matched)

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
= T.print (
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
  let joined_post = join_slprop g b [] [] p1.post p2.post in
  T.print (
    Printf.sprintf "Inferred joint postcondition:\n%s\n"
      (T.term_to_string joined_post)
  );
  let x = fresh g in
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
  : Lemma (requires comp_post_matches_hint c (Some post))
          (ensures comp_post_matches_hint (st_ghost_as_atomic c) (Some post)) = ()

(* This matches the effects of the two branches, without
necessarily matching inames. *)
#push-options "--z3rlimit_factor 4"
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
            comp_post_matches_hint c_then (Some post) /\
            comp_post_matches_hint c_else (Some post) /\
            comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) ->
           st_comp_of_comp c == st_comp_of_comp c_then /\
           comp_post_matches_hint c (Some post))
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
