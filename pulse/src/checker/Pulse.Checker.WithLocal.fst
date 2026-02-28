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

module Pulse.Checker.WithLocal

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module RU = Pulse.RuntimeUtils

let extend_env (g: env) (x: var { freshv g x }) (n: ppname) (init_t: term) =
  push_post (push_binding g x n (mk_ref init_t)) (withlocal_post init_t (term_of_nvar (n, x)))

let extend_post_hint_for_local (g:env) (p:post_hint_for_env g)
                               (init_t:term) (x:var { ~ (Set.mem x (dom g)) }) (n: ppname)
  : T.Tac (q:post_hint_for_env (extend_env g x n init_t) { 
      q.post == comp_withlocal_body_post p.post init_t (term_of_nvar (n, x)) /\
      q.ret_ty == p.ret_ty /\
      q.u == p.u /\
      q.effect_annot == p.effect_annot
      })
  = let conjunct = withlocal_post init_t (term_of_nvar (n, x)) in
    let g' = extend_env g x n init_t in
    let c_typing = Pulse.Checker.Pure.core_check_term (push_binding g x n (mk_ref init_t)) conjunct T.E_Total tm_slprop in
    let res = Pulse.Checker.Base.extend_post_hint g p x (mk_ref init_t) conjunct c_typing in
    res

let with_local_pre_typing (#g:env) (#pre:term) (_pre_typing:unit)
                          (init_t:term) (x:var { ~ (Set.mem x (dom g)) }) n (i:option term)
  : unit
  = admit()

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 0"

let rec unrefine t : T.Tac term =
  match t with
  | T.Tv_Refine b t -> unrefine b.sort
  | T.Tv_AscribedT e _ _ _ -> unrefine e
  | T.Tv_AscribedC e _ _ _ -> unrefine e
  | _ -> t

let head_range (t:st_term {Tm_WithLocal? t.term}) : range =
  match t.term with
  | Tm_WithLocal { initializer = Some i } -> RU.range_of_term i
  | Tm_WithLocal { binder = { binder_ppname = { range } } } -> range
#restart-solver
let check
  (g:env)
  (pre:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_WithLocal? t.term })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= allow_invert post_hint;
  match post_hint with
  | NoHint | TypeHint _ ->
    fail g (Some <| head_range t)
      "Allocating a mutable local variable expects an annotated post-condition"

  | PostHint { effect_annot = EffectAnnotGhost _ }
  | PostHint { effect_annot = EffectAnnotAtomic _ }
  | PostHint { effect_annot = EffectAnnotAtomicOrGhost _ } ->
    fail g (Some <| head_range t)
      "Allocating a mutable local variable is only allowed in non-ghost and non-atomic code"

  | PostHint post ->
    let g = push_context "check_withlocal" t.range g in
    let Tm_WithLocal {binder; initializer=init; body} = t.term in
    let (| init, init_u, init_t |) :
          (init: option term & u:universe & ty:term)
    =
      (* Check against annotation if any *)
      let ty = binder.binder_ty in
      match inspect_term ty, init with
      | Tm_Unknown, Some init ->
        let (| init, init_u, init_t |) =
          compute_tot_term_type_and_u g init
        in
        // Remove any refinements from this inferred type. The Core typechecker
        // will turn postconditions into refinements, and we don't want these
        // going into the type of the local variable. See issue #512.
        let init_t = unrefine init_t in
        (| Some init, init_u, init_t |)

      | _, Some init ->
        let ty, _ = tc_type_phase1 g ty in
        let u = check_universe g ty in
        let init = check_term g init T.E_Total ty in
        (| Some init, u, ty |)

      | Tm_Unknown, None ->
        fail g (Some <| head_range t)
          "allocating a local variable: type must be specified when there is no initializer"

      | _, None ->
        let ty, _ = tc_type_phase1 g ty in
        let u = check_universe g ty in
        (| None, u, ty |)
    in
    if not (eq_univ init_u u0)
    then (
      fail g (Some <| head_range t)
          (Printf.sprintf "check_withlocal: allocating a local variable: type %s is not universe zero (computed %s)"
              (Pulse.Show.show init)
              (P.univ_to_string init_u))
    )
    else
      let x = fresh g in
      let px = binder.binder_ppname, x in
      assume not (x `Set.mem` freevars_st body);
        let x_tm = term_of_nvar px in
        let g_extended = extend_env g x binder.binder_ppname init_t in
        let body_pre = comp_withlocal_body_pre pre init_t x_tm init in
        let body_pre_typing = () in
        // elaborating this post here,
        //   so that later we can check the computed post to be equal to this one
        let post : post_hint_for_env g = post in
        assume not (x `Set.mem` freevars post.post);
          let open Pulse.Typing.Combinators in
          let body_post : post_hint_for_env g_extended = extend_post_hint_for_local g post init_t x binder.binder_ppname in
          let r = check g_extended body_pre body_pre_typing (PostHint body_post) binder.binder_ppname (open_st_term_nv body px) in
          let r: checker_result_t g_extended body_pre (PostHint body_post) = r in
          let (| opened_body, c_body |) = apply_checker_result_k #g_extended #body_pre #body_post r binder.binder_ppname in
          let body = close_st_term opened_body x in
          assume (open_st_term (close_st_term opened_body x) x == opened_body);
          let c = C_ST {u=comp_u c_body;res=comp_res c_body;pre;post=post.post} in
          let c_typing =
            intro_comp_typing g c () 
              ()
              ()
              x ()
          in
          assert (freshv g x);
          assert (~(Set.mem x (freevars_st body)));
          let st = wrst c (Tm_WithLocal { binder = mk_binder_ppname (mk_ref init_t) binder.binder_ppname; initializer=init; body }) in
          checker_result_for_st_typing (| st, c |) res_ppname
#pop-options
