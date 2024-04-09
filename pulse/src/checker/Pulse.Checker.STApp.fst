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

module Pulse.Checker.STApp

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Prover = Pulse.Checker.Prover
open Pulse.Show

let debug_log (g:env) (f:unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level (fstar_env g) "st_app" then f () else ()

let canon_comp (c:comp_st) : comp_st = 
  match readback_comp (elab_comp c) with
  | None -> c
  | Some (C_Tot _) -> c //should be impossible
  | Some c' -> c'

#push-options "--admit_smt_queries true"
let canon_comp_eq_res (g:env) (c:comp_st)
  : RT.equiv (elab_env g) (elab_term (comp_res c)) (elab_term (comp_res (canon_comp c)))
  = RT.Rel_refl _ _ _ 
#pop-options

let canonicalize_st_typing (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (canon_comp c)
  = let c' = canon_comp c in
    let x = fresh g in
    assume ( ~(x `Set.mem` freevars (comp_post c)) /\
            ~(x `Set.mem` freevars (comp_post c')) );
    assume (st_equiv_pre c c');
    let st_eq 
      : st_equiv g c c'
      = ST_VPropEquiv g c c' x (RU.magic ()) (RU.magic()) (RU.magic()) (canon_comp_eq_res g c) (RU.magic()) (RU.magic())
    in
    T_Equiv _ _ _ _ d st_eq

let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b { y == x } = x

let rec intro_uvars_for_logical_implicits (g:env) (uvs:env { disjoint g uvs }) (t:term) (ty:term)
  : T.Tac (uvs':env &
           g':env { extends_with g' g uvs' } &
           t':st_term { Tm_STApp? t'.term }) =
  
  let ropt = is_arrow ty in
  match ropt with
  | Some (b, Some Implicit, c_rest) ->
    let x = fresh (push_env g uvs) in
    let uvs' = push_binding uvs x b.binder_ppname b.binder_ty in
    let c_rest = open_comp_with c_rest (tm_var {nm_index = x; nm_ppname = b.binder_ppname}) in
    begin
      match c_rest with
       | C_ST _
       | C_STAtomic _ _ _
       | C_STGhost _ _ ->
         (| uvs', push_env g uvs', {term=Tm_STApp {head=t;arg_qual=Some Implicit;arg=null_var x};
                                    range=Pulse.RuntimeUtils.range_of_term t;
                                    effect_tag=as_effect_hint (ctag_of_comp_st c_rest) } |)
       | C_Tot ty ->
         intro_uvars_for_logical_implicits g uvs' (tm_pureapp t (Some Implicit) (null_var x)) ty
    end
  | _ ->
    fail g None
      (Printf.sprintf "check_stapp.intro_uvars_for_logical_implicits: expected an arrow type,\
                       with an implicit parameter, found: %s"
         (P.term_to_string ty))

let instantiate_implicits (g:env) (t:st_term { Tm_STApp? t.term })
  : T.Tac (uvs : env &
           g' : env { extends_with g' g uvs } &
           t' : st_term { Tm_STApp? t'.term }) =

  let range = t.range in
  let Tm_STApp { head; arg_qual=qual; arg } = t.term in
  let pure_app = tm_pureapp head qual arg in
  let (| uvs, t, ty |) = instantiate_term_implicits_uvs g pure_app in
  match is_arrow ty with
  | Some (_, Some Implicit, _) ->
    //Some implicits to follow
    intro_uvars_for_logical_implicits g uvs t ty
  | _ ->
    match is_pure_app t with
    | Some (head, q, arg) ->
      (| uvs, push_env g uvs, {term=Tm_STApp {head;arg_qual=q;arg}; range=Pulse.RuntimeUtils.range_of_term t; effect_tag=default_effect_hint } |)
    | _ ->
      fail g (Some (Pulse.RuntimeUtils.range_of_term t))
        (Printf.sprintf "check_stapp.instantiate_implicits: expected an application term, found: %s"
           (show t))

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let apply_impure_function 
      (range:range)
      (g0:env)
      (uvs:_)
      (g:env { extends_with g g0 uvs })
      (ctxt:vprop)
      (ctxt_typing:tot_typing g0 ctxt tm_vprop)
      (post_hint:post_hint_opt g0)
      (res_ppname:ppname)
      (head:term)
      (qual:option qualifier)
      (arg:term)
      (ty_head:term)
      (eff_head:_)
      (dhead:typing g head eff_head ty_head)
      (b:binder & option qualifier & comp { Some b == is_arrow ty_head })
  : T.Tac (checker_result_t g0 ctxt post_hint)
  = let {binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ = b in
    assert (g `env_extends` g0);
    let post_hint : post_hint_opt g = post_hint in
    is_arrow_tm_arrow ty_head;
    debug_log g (fun _ ->
      T.print (Printf.sprintf "st_app, head=%s, arg=%s, readback comp as %s\n"
                 (P.term_to_string head)
                 (P.term_to_string arg)
                 (P.comp_to_string comp_typ)));
    
    let allow_ghost = C_STGhost? comp_typ in
    if (not allow_ghost) &&
       eff_head = T.E_Ghost
    then fail g (Some range)
           (Printf.sprintf "head term %s is ghost, but the arrow comp is not STGhost"
              (P.term_to_string head));

    if qual <> bqual
    then (
     fail g (Some range) (Printf.sprintf "Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
                (P.term_to_string ty_head)
                (P.term_to_string head)
                (P.term_to_string arg))

    )
    else (
      let eff_arg = if allow_ghost then T.E_Ghost else T.E_Total in
      let (| arg, darg |) = check_term g arg eff_arg formal in
      let (| t, c, d |) : (t:st_term & c:comp_st & st_typing g t c) =
        match comp_typ with
        | C_ST res
        | C_STAtomic _ _ res ->
          // ST application
          let d : st_typing _ _ (open_comp_with comp_typ arg) =
            T_STApp g head formal qual comp_typ arg dhead darg in
          let d = canonicalize_st_typing d in
          let t = { term = Tm_STApp {head; arg_qual=qual; arg}; range; effect_tag=as_effect_hint (ctag_of_comp_st comp_typ) } in
          let c = (canon_comp (open_comp_with comp_typ arg)) in
          (| t, c, d |)
        | C_STGhost _ res ->
          // get the non-informative witness
          let x = fresh g in
          if x `Set.mem` freevars_comp (comp_typ)
          then fail g (Some range)
                 ("Unexpected clash of variable names, please file a bug-report");

          //
          // This will always succeed, is there a way to avoid this?
          //
          let d_non_info =
            let token =
              is_non_informative (push_binding g x ppname_default formal)
                                 (open_comp_with comp_typ (null_var x)) in
            match token with
            | None ->
              fail g (Some range)
                (Printf.sprintf "Unexpected non-informative result for %s" (P.comp_to_string comp_typ))
            | Some token ->
              RT.Non_informative_token _ _
                (FStar.Squash.return_squash token) in

          let d : st_typing _ _ (open_comp_with comp_typ arg) =
            T_STGhostApp g head formal qual comp_typ arg x
              (lift_typing_to_ghost_typing dhead)
              (E d_non_info)
              (lift_typing_to_ghost_typing darg) in
          let d = canonicalize_st_typing d in
          let t = { term = Tm_STApp {head; arg_qual=qual; arg}; range; effect_tag=as_effect_hint STT_Ghost } in
          let c = (canon_comp (open_comp_with comp_typ arg)) in
          (| t, c, d |)
        | _ ->
          fail g (Some range)
            "Expected an effectful application; got a pure term (could it be partially applied by mistake?)"
      in
      let (| st', c', st_typing' |) = match_comp_res_with_post_hint d post_hint in
      debug_log g (fun _ -> T.print (Printf.sprintf "st_app: c' = %s\n"
                                       (show #comp c')));
      let framed = Prover.try_frame_pre_uvs ctxt_typing uvs (| st', c', st_typing' |)  res_ppname in
      Prover.prove_post_hint framed post_hint range
    )
  

let check
  (g0:env)
  (ctxt:vprop)
  (ctxt_typing:tot_typing g0 ctxt tm_vprop)
  (post_hint:post_hint_opt g0)
  (res_ppname:ppname)
  (t:st_term { Tm_STApp? t.term })
  : T.Tac (checker_result_t g0 ctxt post_hint) =

  let g0 = push_context "st_app" t.range g0 in
  let range = t.range in

  let (| uvs, g, t |) = instantiate_implicits g0 t in
  assert (g `env_extends` g0);
  let post_hint : post_hint_opt g = post_hint in

  let Tm_STApp { head; arg_qual=qual; arg } = t.term in

  let (| head, eff_head, ty_head, dhead |) = compute_term_type g head in

  debug_log g (fun _ ->
    T.print (Printf.sprintf "st_app: head = %s, eff_head: %s, ty_head = %s\n"
               (P.term_to_string head)
               (P.tot_or_ghost_to_string eff_head)
               (P.term_to_string ty_head)));
    
  match is_arrow ty_head with
  | Some b ->
    apply_impure_function t.range g0 uvs g ctxt ctxt_typing post_hint res_ppname head qual arg ty_head eff_head dhead b

  | _ ->
    let (| ty', typing |) = norm_typing g head eff_head ty_head dhead [weak;hnf;delta] in
    
    match is_arrow ty' with
    | None ->
      fail g (Some t.range)
        (Printf.sprintf "Expected an arrow type; but head %s has type %s" 
            (P.term_to_string head)
            (P.term_to_string ty_head))
    | Some b ->
     apply_impure_function t.range g0 uvs g ctxt ctxt_typing post_hint res_ppname head qual arg ty' eff_head typing b
#pop-options
