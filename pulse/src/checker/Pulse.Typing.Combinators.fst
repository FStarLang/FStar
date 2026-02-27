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

module Pulse.Typing.Combinators

module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module CU = Pulse.Checker.Util
module RU = Pulse.RuntimeUtils

module Metatheory = Pulse.Typing.Metatheory.Base

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure

assume
val invert_forall_typing
        (#g #u #b #body:_)
        (d:tot_typing g (tm_forall_sl u b body) tm_slprop)
        (x:var { freshv g x /\ ~ (x `Set.mem` freevars body) })
  : GTot (
    tot_typing g b.binder_ty (tm_type u) &
    tot_typing (push_binding g x ppname_default b.binder_ty) (open_term body x) tm_slprop
  )

assume
val construct_forall_typing
        (#g #u #b #body:_)
        (x:var { freshv g x /\ ~ (x `Set.mem` freevars body) })
        (dt:tot_typing g b.binder_ty (tm_type u))
        (db:tot_typing (push_binding g x ppname_default b.binder_ty) (open_term body x) tm_slprop)
  : GTot (tot_typing g (tm_forall_sl u b body) tm_slprop)

let st_equiv_trans (#g:env) (#c0 #c1 #c2:comp) (d01:st_equiv g c0 c1) (d12:st_equiv g c1 c2)
  : st_equiv g c0 c2
  = ()

let t_equiv (g:env) (st:st_term) (c:comp) (d:st_typing g st c) (c':comp) (eq:st_equiv g c c')
  : st_typing g st c'
  = ()

let slprop_equiv_typing (g:env) (t0 t1:term) (v:slprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_slprop -> tot_typing g t1 tm_slprop) &
          (tot_typing g t1 tm_slprop -> tot_typing g t0 tm_slprop))
  = (fun _ -> ()), (fun _ -> ())
        
let bind_t (case_c1 case_c2:comp_st -> bool) =
      (g:env) ->
      (pre:term) ->
      (e1:st_term) ->
      (e2:st_term) ->
      (c1:comp_st{ case_c1 c1 }) ->
      (c2:comp_st{ case_c2 c2 }) ->
      (px:nvar { ~ (Set.mem (snd px) (dom g)) }) ->
      (d_e1:st_typing g e1 c1) ->
      (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1))) ->
      (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2) ->
      (res_typing:universe_of g (comp_res c2) (comp_u c2)) ->
      (post_typing:tot_typing (push_binding g (snd px) (fst px) (comp_res c2))
                              (open_term_nv (comp_post c2) px)
                                      tm_slprop) ->
      (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint }) ->
    T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre  /\
                        comp_post_matches_hint c post_hint })
           (requires
              (let _, x = px in
              comp_pre c1 == pre /\
              freshv g x /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2)))))
           (ensures fun _ -> True)
#push-options "--fuel 0 --ifuel 0"
let mk_bind_st_st
  : bind_t C_ST? C_ST?
  = fun g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing _ ->
      let _, x = px in
      let b = nvar_as_binder px (comp_res c1) in
      let c : comp_st = C_ST (st_comp_with_pre (st_comp_of_comp c2) pre) in
      let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
      (| t, c |)
#pop-options
let inames_of (c:comp_st) : term =
  match c with
  | C_ST _ -> tm_emp_inames
  | C_STGhost inames _
  | C_STAtomic inames _ _ -> inames

let with_inames (c:comp_st) (i:term) =
  match c with
  | C_ST _ -> c
  | C_STGhost _ sc -> C_STGhost i sc
  | C_STAtomic _ obs sc -> C_STAtomic i obs sc

let weaken_comp_inames (#g:env) (#e:st_term) (#c:comp_st) (d_e:st_typing g e c) (new_inames:term)
  : T.Tac (c':comp_st { with_inames c new_inames == c' } &
           st_typing g e c')
  = match c with
    | C_ST _ -> (| c, d_e |)
    | C_STGhost inames sc ->
      let _ = check_prop_validity g _ (tm_inames_subset_typing g inames new_inames) in
      (| with_inames c new_inames, () |)

    | C_STAtomic inames obs sc ->
      let _ = check_prop_validity g _ (tm_inames_subset_typing g inames new_inames) in
      (| with_inames c new_inames, () |)

let try_lift_ghost_atomic (g:env) (e:st_term) (c:comp_st { C_STGhost? c }) (d:st_typing g e c)
: T.Tac (option (st_typing g e (st_ghost_as_atomic c)))
= let comp_res_typing : universe_of g (comp_res c) (comp_u c) = () in
  let w = try_get_non_informative_witness g (comp_u c) (comp_res c) comp_res_typing in
  match w with
  | None -> None
  | Some w -> Some ()

let lift_ghost_atomic (g:env) (e:st_term) (c:comp_st { C_STGhost? c }) (d:st_typing g e c)
: T.Tac (st_typing g e (st_ghost_as_atomic c))
= let w = try_lift_ghost_atomic g e c d in
  match w with
  | None -> 
    let open Pulse.PP in
    let t = comp_res c in
    fail_doc g (Some (RU.range_of_term t)) [
        text "Expected a term with a non-informative (e.g., erased) type.";
        prefix 2 1 (text "Got:")
          (pp t);
    ]
  | Some d ->
    d

#push-options "--z3rlimit_factor 2 --ifuel 0 --fuel 0 --split_queries no"
#restart-solver
let mk_bind_ghost_ghost : bind_t C_STGhost? C_STGhost? =
  fun g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint ->
  let _, x = px in
  let b = nvar_as_binder px (comp_res c1) in
  let C_STGhost inames1 sc1 = c1 in
  let C_STGhost inames2 sc2 = c2 in
  if eq_tm inames1 inames2
  then begin
    let c : comp_st = C_STGhost inames1 (st_comp_with_pre sc2 pre) in
    let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
    (| t, c |)
  end
  else if (PostHint? post_hint)
  then (
    let _ = check_prop_validity g _ (tm_inames_subset_typing g inames1 inames2) in
    let c : comp_st = C_STGhost inames2 (st_comp_with_pre sc2 pre) in
    let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
    (| t, c |)
  )
  else begin
    let new_inames = tm_join_inames inames1 inames2 in
    let _ = check_prop_validity g _ (tm_inames_subset_typing g inames1 new_inames) in
    let _ = check_prop_validity g _ (tm_inames_subset_typing g inames2 new_inames) in
    let c : comp_st = C_STGhost new_inames (st_comp_with_pre sc2 pre) in
    let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
    (| t, c |)
  end 

let mk_bind_atomic_atomic
  : bind_t C_STAtomic? C_STAtomic?
  = fun g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint ->
      let _, x = px in
      let b = nvar_as_binder px (comp_res c1) in
      let C_STAtomic inames1 obs1 sc1 = c1 in
      let C_STAtomic inames2 obs2 sc2 = c2 in
      if at_most_one_observable obs1 obs2
      then (
        if eq_tm inames1 inames2
        then begin
          let c : comp_st = C_STAtomic inames1 (join_obs obs1 obs2) (st_comp_with_pre sc2 pre) in
          let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
          (| t, c |)
        end
        else if (PostHint? post_hint)
        then (
          let _ = check_prop_validity g _ (tm_inames_subset_typing g inames1 inames2) in
          let c : comp_st = C_STAtomic inames2 (join_obs obs1 obs2) (st_comp_with_pre sc2 pre) in
          let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
          (| t, c |)
        )
        else begin
          let new_inames = tm_join_inames inames1 inames2 in
          let _ = check_prop_validity g _ (tm_inames_subset_typing g inames1 new_inames) in
          let _ = check_prop_validity g _ (tm_inames_subset_typing g inames2 new_inames) in
          let c : comp_st = C_STAtomic new_inames (join_obs obs1 obs2) (st_comp_with_pre sc2 pre) in
          let t = wrst c (Tm_Bind {binder=b; head=e1; body=e2}) in
          (| t, c |)
        end 
      )
      else (
        T.fail "Should have been handled separately"
      )
#pop-options

#push-options "--z3rlimit_factor 20 --fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"
#restart-solver
let rec mk_bind (g:env) 
                (pre:term)
                (e1:st_term)
                (e2:st_term)
                (c1:comp_st)
                (c2:comp_st)
                (px:nvar { ~ (Set.mem (snd px) (dom g)) })
                (d_e1:st_typing g e1 c1)
                (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
                (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2)
                (res_typing:universe_of g (comp_res c2) (comp_u c2))
                (post_typing:tot_typing (push_binding g (snd px) (fst px) (comp_res c2))
                                        (open_term_nv (comp_post c2) px)
                                        tm_slprop)
                (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint })
  : T.TacH (t:st_term &
            c:comp_st {
              st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre /\
              comp_post_matches_hint c post_hint })
           (requires
              (let _, x = px in
              comp_pre c1 == pre /\
              freshv g x /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2)))))
           (ensures fun _ -> True) =
  let _, x = px in
  let b = nvar_as_binder px (comp_res c1) in
  let fail_bias tag
  : T.TacH _ (requires True) (ensures fun _ -> False)
  = let open Pulse.PP in
    fail_doc g (Some e1.range)
      [text "Cannot compose computations in this " ^/^ text tag ^/^ text " block:";
       prefix 4 1 (text "This computation has effect: ") (pp (effect_annot_of_comp c1));
       prefix 4 1 (text "The continuation has effect: ") (pp (effect_annot_of_comp c2))]
  in
  match c1, c2 with
  | C_ST _, C_ST _ ->
    mk_bind_st_st g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint

  | C_STGhost _ _, C_STGhost _ _ ->
    mk_bind_ghost_ghost g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint

  | C_STAtomic inames1 obs1 sc1, C_STAtomic inames2 obs2 sc2 ->
    if at_most_one_observable obs1 obs2
    then (
      mk_bind_atomic_atomic g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint
    ) 
    else if (PostHint? post_hint)
    then fail_bias "atomic"
    else (
      mk_bind g pre e1 e2 (C_ST (st_comp_of_comp c1)) c2 px () d_c1res d_e2 res_typing post_typing post_hint
    )

  | C_STAtomic inames _ _, C_ST _ ->
    mk_bind g pre e1 e2 (C_ST (st_comp_of_comp c1)) c2 px () d_c1res d_e2 res_typing post_typing post_hint

  | C_ST _, C_STAtomic inames _ _ ->
    if (PostHint? post_hint)
    then fail_bias "atomic"
    else (
      let c2_lifted = C_ST (st_comp_of_comp c2) in
      let (| t, c |) = mk_bind g pre e1 e2 c1 c2_lifted px () d_c1res () res_typing post_typing post_hint in
      (| t, c |)
    )

  | C_STGhost _ _, C_STAtomic _ Neutral _ -> (
    match try_lift_ghost_atomic g e1 c1 d_e1 with
    | Some _ ->
      mk_bind g pre e1 e2 (st_ghost_as_atomic c1) c2 px () d_c1res d_e2 res_typing post_typing post_hint
    | None ->
      match post_hint with
      | TypeHint _
      | NoHint
      | PostHint { effect_annot = EffectAnnotAtomicOrGhost _ } ->
        let c2_lifted = C_STGhost (comp_inames c2) (st_comp_of_comp c2) in
        let (| t, c |) = mk_bind g pre e1 e2 c1 c2_lifted px () d_c1res () res_typing post_typing post_hint in
        (| t, c |)
      | _ -> fail_bias "atomic"
  )

  | C_STAtomic _ Neutral _, C_STGhost _ _ -> (
    match post_hint with
    | TypeHint _
    | NoHint
    | PostHint { effect_annot = EffectAnnotGhost _ } ->
      let c1_lifted = C_STGhost (comp_inames c1) (st_comp_of_comp c1) in
      mk_bind g pre e1 e2 c1_lifted c2 px () d_c1res d_e2 res_typing post_typing post_hint

    | _ ->
      match try_lift_ghost_atomic (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2 d_e2 with
      | Some _ ->
        let c2_lifted = st_ghost_as_atomic c2 in
        let (| t, c |) = mk_bind g pre e1 e2 c1 c2_lifted px () d_c1res () res_typing post_typing post_hint in
        (| t, c |)
      | None ->
        let c1_lifted = C_STGhost (comp_inames c1) (st_comp_of_comp c1) in
        mk_bind g pre e1 e2 c1_lifted c2 px () d_c1res d_e2 res_typing post_typing post_hint
  )

  | C_STGhost _ _, C_ST _
  | C_STGhost _ _, C_STAtomic _ _ _ ->
    let _ = lift_ghost_atomic g e1 c1 d_e1 in
    mk_bind g pre e1 e2 (st_ghost_as_atomic c1) c2 px () d_c1res d_e2 res_typing post_typing post_hint

  | C_ST _, C_STGhost _ _
  | C_STAtomic _ _ _, C_STGhost _ _ ->
    if (PostHint? post_hint)
    then fail_bias "ghost"
    else (
      let _ = lift_ghost_atomic (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2 d_e2 in
      let c2_lifted = st_ghost_as_atomic c2 in
      let (| t, c |) = mk_bind g pre e1 e2 c1 c2_lifted px () d_c1res () res_typing post_typing post_hint in
      (| t, c |)
    )
  | _ -> T.fail "Impossible: unexpected combination of effects"
#pop-options

let bind_res_and_post_typing g c2 x post_hint 
  = let s2 = st_comp_of_comp c2 in
    match post_hint with
    | NoHint | TypeHint _ -> 
      (* We're inferring a post, so these checks are unavoidable *)
      (* since we need to type the result in a smaller env g *)          
      let u = check_universe g s2.res in 
      if not (eq_univ u s2.u)
      then fail g None "Unexpected universe for result type"
      else if x `Set.mem` freevars (RU.deep_compress_safe s2.post)
      then fail g None (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
      else (
        let y = x in //fresh g in
        let s2_post_opened = open_term_nv s2.post (v_as_nv y) in
        let post_typing =
          check_slprop_with_core (push_binding g y ppname_default s2.res) s2_post_opened in
        ()
      )
    | PostHint post -> 
      CU.debug g "pulse.main" (fun _ -> "bind_res_and_post_typing (with post_hint)\n");
      let pr = post_hint_typing g post x in
      ()
     
let add_frame (g:env) (t:st_term) (c:comp_st) (t_typing:st_typing g t c)
  (frame:slprop)
  (frame_typing:tot_typing g frame tm_slprop)
  : t':st_term &
    c':comp_st { c' == add_frame c frame } =

  (| t, add_frame c frame |)

#push-options "--fuel 0 --ifuel 0"
let apply_frame (g:env)
                (t:st_term)
                (ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_slprop)
                (c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Dv  (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) })
  = let s = st_comp_of_comp c in
    let frame = frame_t in
    let c' = Pulse.Typing.add_frame c frame in
    let s' = st_comp_of_comp c' in
    let s'' = { s' with pre = ctxt } in
    let c'' = c' `with_st_comp` s'' in
    assert (comp_post c' == comp_post c'');
    c''
#pop-options

#push-options "--z3rlimit_factor 2"
let comp_for_post_hint (g:env) (pre:slprop) (pre_typing:tot_typing g pre tm_slprop)
  (post:post_hint_t { g `env_extends` post.g })
  (x:var { freshv g x })
  : T.Tac (c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint post) }) =

  if x `Set.mem` freevars post.post
  then fail g None "Impossible: unexpected freevar clash in comp_for_post_hint, please file a bug-report";

  let s : st_comp = {u=post.u;res=post.ret_ty;pre;post=post.post} in
  match post.effect_annot with
  | EffectAnnotSTT -> C_ST s
  | EffectAnnotGhost { opens } ->
    C_STGhost opens s
  | EffectAnnotAtomic { opens }
  | EffectAnnotAtomicOrGhost { opens } ->
    C_STAtomic opens Neutral s
  | _ -> T.fail "Impossible"
#pop-options