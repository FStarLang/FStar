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
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer

module RU = Pulse.RuntimeUtils

module Metatheory = Pulse.Typing.Metatheory.Base

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure

assume
val invert_forall_typing
        (#g #u #b #body:_)
        (d:tot_typing g (tm_forall_sl u b body) tm_vprop)
        (x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars body) })
  : GTot (
    tot_typing g b.binder_ty (tm_type u) &
    tot_typing (push_binding g x ppname_default b.binder_ty) (open_term body x) tm_vprop
  )

assume
val construct_forall_typing
        (#g #u #b #body:_)
        (x:var { None? (lookup g x) /\ ~ (x `Set.mem` freevars body) })
        (dt:tot_typing g b.binder_ty (tm_type u))
        (db:tot_typing (push_binding g x ppname_default b.binder_ty) (open_term body x) tm_vprop)
  : GTot (tot_typing g (tm_forall_sl u b body) tm_vprop)
   

let rec vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_vprop -> tot_typing g t1 tm_vprop) &
          (tot_typing g t1 tm_vprop -> tot_typing g t0 tm_vprop))
        (decreases v)
  = match v with
    | VE_Refl _ _ -> (fun x -> x), (fun x -> x)

    | VE_Sym _ _ _ v' -> 
      let f, g = vprop_equiv_typing v' in
      g, f

    | VE_Trans g t0 t2 t1 v02 v21 ->
      let f02, f20 = vprop_equiv_typing v02 in
      let f21, f12 = vprop_equiv_typing v21 in
      (fun x -> f21 (f02 x)), 
      (fun x -> f20 (f12 x))

    | VE_Ctxt g s0 s1 s0' s1' v0 v1 ->
      let f0, f0' = vprop_equiv_typing v0 in
      let f1, f1' = vprop_equiv_typing v1 in      
      let ff (x:tot_typing g (tm_star s0 s1) tm_vprop)
        : tot_typing g (tm_star s0' s1') tm_vprop
        = let s0_typing = star_typing_inversion_l x in
          let s1_typing = star_typing_inversion_r x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing g (tm_star s0' s1') tm_vprop)
        : tot_typing g (tm_star s0 s1) tm_vprop
        = let s0'_typing = star_typing_inversion_l x in
          let s1'_typing = star_typing_inversion_r x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing g (tm_star tm_emp t) tm_vprop)
        : tot_typing g t tm_vprop
        = let r = star_typing_inversion_r x in
          r
      in
      let bk (x:tot_typing g t tm_vprop)
        : tot_typing g (tm_star tm_emp t) tm_vprop
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing g (tm_star t0 t1) tm_vprop)
        : tot_typing g (tm_star t1 t0) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt1 = star_typing_inversion_r x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop)
        : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop
        = let tt0 = star_typing_inversion_l x in
          let tt12 = star_typing_inversion_r x in
          let tt1 = star_typing_inversion_l tt12 in
          let tt2 = star_typing_inversion_r tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing g (tm_star (tm_star t0 t1) t2) tm_vprop)
        : tot_typing g (tm_star t0 (tm_star t1 t2)) tm_vprop
        = let tt01 = star_typing_inversion_l x in
          let tt2 = star_typing_inversion_r x in
          let tt0 = star_typing_inversion_l tt01 in
          let tt1 = star_typing_inversion_r tt01 in
          star_typing tt0 (star_typing tt1 tt2)
      in
      fwd, bk
   
    | VE_Ext g t0 t1 token ->
      let d1, d2 = vprop_eq_typing_inversion g t0 t1 token in
      (fun _ -> d2),
      (fun _ -> d1)
    
    | VE_Fa g x u b t0 t1 d ->
      let d0, d1 = vprop_equiv_typing d in
      (fun fa0_typing ->
        let b_typing, t0_typing = invert_forall_typing fa0_typing x in
        let t1_typing = d0 t0_typing in
        construct_forall_typing #g #u x b_typing t1_typing),
      (fun fa1_typing ->
        let b_typing, t1_typing = invert_forall_typing fa1_typing x in
        let t0_typing = d1 t1_typing in
        construct_forall_typing #g #u #b #t0 x b_typing t0_typing)
        
#push-options "--z3rlimit_factor 8 --ifuel 1 --fuel 2"

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
                                      tm_vprop) ->
      (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint }) ->
    T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre  /\
                        comp_post_matches_hint c post_hint } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True)

let mk_bind_st_st
  : bind_t C_ST? C_ST?
  = fun g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing _ ->
      let _, x = px in
      let b = nvar_as_binder px (comp_res c1) in
      let bc = Bind_comp g x c1 c2 res_typing x post_typing in
      (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)

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
      let d_e = T_Sub _ _ _ _ d_e (STS_GhostInvs _ sc inames new_inames (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
      (| with_inames c new_inames, d_e |)

    | C_STAtomic inames obs sc ->
      let d_e = T_Sub _ _ _ _ d_e (STS_AtomicInvs _ sc inames new_inames obs obs (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
      (| with_inames c new_inames, d_e |)

let try_lift_ghost_atomic (#g:env) (#e:st_term) (#c:comp_st { C_STGhost? c }) (d:st_typing g e c)
: T.Tac (option (st_typing g e (st_ghost_as_atomic c)))
= let comp_res_typing : universe_of g (comp_res c) (comp_u c) =
    let open Metatheory in
    let d = st_typing_correctness d in
    let d, _ = comp_typing_inversion d in
    let (| d, _, _, _ |) = st_comp_typing_inversion d in
    d
  in
  let w = try_get_non_informative_witness g (comp_u c) (comp_res c) comp_res_typing in
  match w with
  | None -> None
  | Some w ->
    let d = T_Lift _ _ _ _ d (Lift_Ghost_Neutral _ c w) in
    Some d

let lift_ghost_atomic (#g:env) (#e:st_term) (#c:comp_st { C_STGhost? c }) (d:st_typing g e c)
: T.Tac (st_typing g e (st_ghost_as_atomic c))
= let w = try_lift_ghost_atomic d in
  match w with
  | None -> 
    let open Pulse.PP in
    let t = comp_res c in
    fail_doc g (Some (RU.range_of_term t)) [
        text "Expected a term with a non-informative (e.g., erased) type; got"
          ^/^ pp t
    ]
  | Some d ->
    d

let mk_bind_ghost_ghost : bind_t C_STGhost? C_STGhost? =
  fun g pre e1 e2 c1 c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint ->
  let _, x = px in
  let b = nvar_as_binder px (comp_res c1) in
  let C_STGhost inames1 sc1 = c1 in
  let C_STGhost inames2 sc2 = c2 in
  if eq_tm inames1 inames2
  then begin
    let bc = Bind_comp g x c1 c2 res_typing x post_typing in
    (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
  end
  else if (Some? post_hint)
  then (
    let d_e1 = T_Sub _ _ _ _ d_e1 (STS_GhostInvs _ sc1 inames1 inames2 (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
    let c1 = C_STGhost inames2 sc1 in
    let bc = Bind_comp g x c1 c2 res_typing x post_typing in
    (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
  )
  else begin
    let new_inames = tm_join_inames inames1 inames2 in
    let d_e1 = T_Sub _ _ _ _ d_e1 (STS_GhostInvs _ sc1 inames1 new_inames (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
    let d_e2 = T_Sub _ _ _ _ d_e2 (STS_GhostInvs _ sc2 inames2 new_inames (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
    let c1 = C_STGhost new_inames sc1 in
    let c2 = C_STGhost new_inames sc2 in
    let bc = Bind_comp g x c1 c2 res_typing x post_typing in
    (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
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
          let bc = Bind_comp g x c1 c2 res_typing x post_typing in
          (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
        end
        else if (Some? post_hint)
        then (
          let d_e1 = T_Sub _ _ _ _ d_e1 (STS_AtomicInvs _ sc1 inames1 inames2 obs1 obs1 (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
          let c1 = C_STAtomic inames2 obs1 sc1 in
          let bc = Bind_comp g x c1 c2 res_typing x post_typing in
          (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
        )
        else begin
          let new_inames = tm_join_inames inames1 inames2 in
          let d_e1 = T_Sub _ _ _ _ d_e1 (STS_AtomicInvs _ sc1 inames1 new_inames obs1 obs1 (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
          let d_e2 = T_Sub _ _ _ _ d_e2 (STS_AtomicInvs _ sc2 inames2 new_inames obs2 obs2 (check_prop_validity _ _ (tm_inames_subset_typing _ _ _))) in
          let c1 = C_STAtomic new_inames obs1 sc1 in
          let c2 = C_STAtomic new_inames obs2 sc2 in
          let bc = Bind_comp g x c1 c2 res_typing x post_typing in
          (| _, _, T_Bind _ e1 e2 _ _ b _ _ d_e1 d_c1res d_e2 bc |)
        end 
      )
      else (
        T.fail "Should have been handled separately"
      )

#push-options "--z3rlimit_factor 10 --fuel 0 --ifuel 1"
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
                                        tm_vprop)
                (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint })
  : T.TacH (t:st_term &
            c:comp_st {
              st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre /\
              comp_post_matches_hint c post_hint } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True) =
  let _, x = px in
  let b = nvar_as_binder px (comp_res c1) in
  let fail_bias (#a:Type) tag
  : T.TacH a (requires fun _ -> True) (ensures fun _ r -> FStar.Tactics.Result.Failed? r)
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
    else if (Some? post_hint)
    then fail_bias "atomic"
    else (
      let d_e1 = T_Lift _ _ _ _ d_e1 (Lift_STAtomic_ST _ c1) in
      mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint
    )

  | C_STAtomic inames _ _, C_ST _ ->
    let d_e1 = T_Lift _ _ _ _ d_e1 (Lift_STAtomic_ST _ c1) in
    mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint

  | C_ST _, C_STAtomic inames _ _ ->
    if (Some? post_hint)
    then fail_bias "atomic"
    else (
      let d_e2  = T_Lift _ _ _ _ d_e2 (Lift_STAtomic_ST _ c2) in
      let (| t, c, d |) = mk_bind g pre e1 e2 _ _ px d_e1 d_c1res d_e2 res_typing post_typing post_hint in
      (| t, c, d |)
    )

  | C_STGhost _ _, C_STAtomic _ Neutral _ -> (
    match try_lift_ghost_atomic d_e1 with
    | Some d_e1 ->
      mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint
    | None ->
      match post_hint with
      | None
      | Some { effect_annot = EffectAnnotAtomicOrGhost _ } ->
        let d_e2 = T_Lift _ _ _ _ d_e2 (Lift_Neutral_Ghost _ c2) in
        let (| t, c, d |) = mk_bind g pre e1 e2 _ _ px d_e1 d_c1res d_e2 res_typing post_typing post_hint in
        (| t, c, d |)
      | _ -> fail_bias "atomic"
  )

  | C_STAtomic _ Neutral _, C_STGhost _ _ -> (
    match post_hint with
    | Some { effect_annot = EffectAnnotGhost _ } ->
      let d_e1 = T_Lift _ _ _ _ d_e1 (Lift_Neutral_Ghost _ c1) in
      mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint

    | _ ->
      match try_lift_ghost_atomic d_e2 with
      | Some d_e2 ->
        let (| t, c, d |) = mk_bind g pre e1 e2 _ _ px d_e1 d_c1res d_e2 res_typing post_typing post_hint in
        (| t, c, d |)
      | None ->
        let d_e1 = T_Lift _ _ _ _ d_e1 (Lift_Neutral_Ghost _ c1) in
        mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint
  )

  | C_STGhost _ _, C_ST _
  | C_STGhost _ _, C_STAtomic _ _ _ ->
    let d_e1 = lift_ghost_atomic d_e1 in
    mk_bind g pre e1 e2 _ c2 px d_e1 d_c1res d_e2 res_typing post_typing post_hint

  | C_ST _, C_STGhost _ _
  | C_STAtomic _ _ _, C_STGhost _ _ ->
    if (Some? post_hint)
    then fail_bias "ghost"
    else (
      let d_e2 = lift_ghost_atomic d_e2 in
      let (| t, c, d |) = mk_bind g pre e1 e2 _ _ px d_e1 d_c1res d_e2 res_typing post_typing post_hint in
      (| t, c, d |)
    )
#pop-options

let bind_res_and_post_typing g c2 x post_hint 
  = let s2 = st_comp_of_comp c2 in
    match post_hint with
    | None -> 
      (* We're inferring a post, so these checks are unavoidable *)
      (* since we need to type the result in a smaller env g *)          
      let (| u, res_typing |) = check_universe g s2.res in 
      if not (eq_univ u s2.u)
      then fail g None "Unexpected universe for result type"
      else if x `Set.mem` freevars s2.post
      then fail g None (Printf.sprintf "Bound variable %d escapes scope in postcondition %s" x (P.term_to_string s2.post))
      else (
        let y = x in //fresh g in
        let s2_post_opened = open_term_nv s2.post (v_as_nv y) in
        let post_typing =
          check_vprop_with_core (push_binding g y ppname_default s2.res) s2_post_opened in
        res_typing, post_typing
      )
    | Some post -> 
      if x `Set.mem` freevars s2.post
      then fail g None "Unexpected mismatched postcondition in bind" //exclude with a stronger type on check'
      else (
         let pr = post_hint_typing g post x in
         pr.ty_typing, pr.post_typing
      )

let add_frame (#g:env) (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
  (#frame:vprop)
  (frame_typing:tot_typing g frame tm_vprop)
  : t':st_term &
    c':comp_st { c' == add_frame c frame } &
    st_typing g t' c' =

  (| t, add_frame c frame, T_Frame _ _ _ _ frame_typing t_typing |)

let apply_frame (#g:env)
                (#t:st_term)
                (#ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_vprop)
                (#c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Tot (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) } &
           st_typing g t c')
  = let s = st_comp_of_comp c in
    let (| frame, frame_typing, ve |) = frame_t in
    let t_typing
      : st_typing g t (Pulse.Typing.add_frame c frame)
      = T_Frame g t c frame frame_typing t_typing in
    let c' = Pulse.Typing.add_frame c frame in
    let c'_typing = Metatheory.st_typing_correctness t_typing in
    let s' = st_comp_of_comp c' in
    let ve: vprop_equiv g s'.pre ctxt = ve in
    let s'' = { s' with pre = ctxt } in
    let c'' = c' `with_st_comp` s'' in
    assert (comp_post c' == comp_post c'');
    let ve: vprop_equiv g (comp_pre c') (comp_pre c'') = ve in    
    let st_typing = fst <| Metatheory.comp_typing_inversion c'_typing in
    let (| res_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_typing in
    let st_equiv = ST_VPropEquiv g c' c'' x pre_typing res_typing post_typing (RT.Rel_refl _ _ _) ve (VE_Refl _ _) in
    let t_typing = T_Equiv _ _ _ _ t_typing st_equiv in
    (| c'', t_typing |)

let comp_for_post_hint #g (#pre:vprop) (pre_typing:tot_typing g pre tm_vprop)
  (post:post_hint_t { g `env_extends` post.g })
  (x:var { lookup g x == None })
  : T.Tac (c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (Some post) } &
           comp_typing g c (universe_of_comp c)) =

  if x `Set.mem` freevars post.post
  then fail g None "Impossible: unexpected freevar clash in comp_for_post_hint, please file a bug-report";

  let px = v_as_nv x in
  let post_typing_rec = post_hint_typing g post x in
  let post_opened = open_term_nv post.post px in              
  assume (close_term post_opened x == post.post);
  let s : st_comp = {u=post.u;res=post.ret_ty;pre;post=post.post} in
  let d_s : st_comp_typing _ s =
  STC _ s x post_typing_rec.ty_typing pre_typing post_typing_rec.post_typing in
          
  match post.effect_annot with
  | EffectAnnotSTT -> (| _,  CT_ST _ _ d_s |)
  | EffectAnnotGhost { opens } ->
    let d_opens : tot_typing post.g opens tm_inames = post.effect_annot_typing in
    assert (g `env_extends` post.g);
    let d_opens : tot_typing g opens tm_inames = magic () in  // weakening
    (| _, CT_STGhost _ opens _ d_opens d_s |)
  | EffectAnnotAtomic { opens }
  | EffectAnnotAtomicOrGhost { opens } ->
    let d_opens : tot_typing post.g opens tm_inames = post.effect_annot_typing in
    assert (g `env_extends` post.g);
    let d_opens : tot_typing g opens tm_inames = magic () in  // weakening
    (| _, CT_STAtomic _ opens Neutral _ d_opens d_s |)
