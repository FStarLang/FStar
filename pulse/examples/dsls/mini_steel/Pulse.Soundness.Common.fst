module Pulse.Soundness.Common
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate

let rec extend_env_l_lookup_fvar (g:R.env) (sg:env) (fv:R.fv) (us:R.universes)
  : Lemma 
    (ensures
      RT.lookup_fvar_uinst (extend_env_l g sg) fv us ==
      RT.lookup_fvar_uinst g fv us)
    [SMTPat (RT.lookup_fvar_uinst (extend_env_l g sg) fv us)]
  = match sg with
    | [] -> ()
    | hd::tl -> extend_env_l_lookup_fvar g tl fv us


let rec extend_env_l_lookup_bvar (g:R.env) (sg:env) (x:var)
  : Lemma 
    (requires (forall x. RT.lookup_bvar g x == None))
    (ensures (
      match lookup sg x with
      | Some b -> RT.lookup_bvar (extend_env_l g sg) x == Some (elab_binding b)
      | None -> RT.lookup_bvar (extend_env_l g sg) x == None))
    (decreases sg)
    [SMTPat (RT.lookup_bvar (extend_env_l g sg) x)]
  = match sg with
    | [] -> ()
    | hd :: tl -> extend_env_l_lookup_bvar g tl x

let tot_typing_soundness (#f:RT.fstar_top_env)
                         (#g:env)
                         (#e:pure_term)
                         (#t:pure_term)
                         (d:tot_typing f g e t)
  : GTot (RT.typing (extend_env_l f g) (elab_pure e) (elab_pure t))
         (decreases d)
  = let E d = d in
    match d with
    | T_Tot _ _ _ d -> d
    // | T_If _ _ _ _ _ _ _ _ _ -> admit() //make T_If stateful

let mk_t_abs_tot (f:RT.fstar_top_env) (g:env)
                 (#u:universe)
                 (#ty:pure_term)
                 (ppname:string)
                 (t_typing:tot_typing f g ty (Tm_Type u))
                 (#x:var { None? (lookup g x) })
                 (#body:pure_term)
                 (#body_ty:pure_term)
                 (body_typing:tot_typing f ((x, Inl ty)::g) (open_term body x) body_ty)
  : GTot (RT.typing (extend_env_l f g)
                    (mk_abs_with_name ppname (elab_pure ty) (elab_pure body))
                    (elab_pure (Tm_Arrow {binder_ty=ty; binder_ppname=ppname} (close_pure_comp (C_Tot body_ty) x))))
  = let c = C_Tot body_ty in
    let r_ty = elab_pure ty in
    let r_body = elab_pure (open_term body x) in
    let r_c = elab_pure_comp c in
    let r_t_typing = tot_typing_soundness t_typing in
    let r_body_typing = tot_typing_soundness body_typing in
    RT.well_typed_terms_are_ln _ _ _ r_body_typing;
    RT.open_close_inverse r_body x;
    elab_comp_close_commute c x;      
    let d : RT.typing (extend_env_l f g)
                      (mk_abs_with_name ppname (elab_pure ty)
                              (RT.close_term (elab_pure (open_term body x)) x))
                      (elab_pure (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} (close_pure_comp (C_Tot body_ty) x)))
          = 
    RT.T_Abs (extend_env_l f g)
             x
             r_ty
             (RT.close_term r_body x)
             r_c
             (elab_universe u) ppname _
             r_t_typing
             r_body_typing
    in
    elab_open_commute' body (Tm_Var {nm_index=x;nm_ppname="_"}) 0;
    RT.open_term_spec (elab_pure body) x;
    assert (elab_pure (open_term body x) ==
            RT.open_term (elab_pure body) x);
    let d : RT.typing _
                      (mk_abs_with_name ppname (elab_pure ty)
                              (RT.close_term (RT.open_term (elab_pure body) x) x))
                      _
          = d 
    in
    assume (~ (x `Set.mem` RT.freevars (elab_pure body)));
    RT.close_open_inverse (elab_pure body) x;
    d

let mk_t_abs (f:RT.fstar_top_env) (g:env)
             (#u:universe)
             (#ty:pure_term)
             (#t_typing:src_typing f g ty (C_Tot (Tm_Type u)))
             (ppname:string)
             (r_t_typing:RT.typing (extend_env_l f g)
                                   (elab_src_typing t_typing)
                                   (elab_pure_comp (C_Tot (Tm_Type u))))
             (#body:term)
             (#x:var { None? (lookup g x) })
             (#c:pure_comp)
             (#body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c)
             (r_body_typing:RT.typing (extend_env_l f ((x, Inl ty)::g))
                                     (elab_src_typing body_typing)
                                     (elab_pure_comp c))
  : GTot (RT.typing (extend_env_l f g)
                    (mk_abs_with_name ppname (elab_pure ty) (RT.close_term (elab_src_typing body_typing) x))
                    (elab_pure (Tm_Arrow {binder_ty=ty;binder_ppname=ppname} (close_pure_comp c x))))
  = let r_ty = elab_pure ty in
    let r_body = elab_src_typing body_typing in
    let r_c = elab_pure_comp c in
    Pulse.Elaborate.elab_pure_equiv t_typing;
    RT.well_typed_terms_are_ln _ _ _ r_body_typing;
    RT.open_close_inverse r_body x;
    elab_comp_close_commute c x;      
        RT.T_Abs (extend_env_l f g)
                   x
                   r_ty
                   (RT.close_term r_body x)
                   r_c
                   (elab_universe u) ppname _
                   r_t_typing
                   r_body_typing

(*** Typing of combinators used
     in the elaboration **)


(** Type of bind **)

let bind_res (u2:R.universe) (t2 pre post2:R.term) =
  mk_stt_app u2 [t2; pre; post2]

let g_type_bind (u2:R.universe) (t1 t2 post1 post2:R.term) =
    mk_tot_arrow1 (t1, R.Q_Explicit)
                  (bind_res u2 t2 (R.mk_app post1 [bound_var 0 (* x *), R.Q_Explicit]) post2)

let bind_type_t1_t2_pre_post1_post2_f (u1 u2:R.universe) (t1 t2 pre post1 post2:R.term) =
  mk_tot_arrow1 (g_type_bind u2 t1 t2 post1 post2, R.Q_Explicit)
                (bind_res u2 t2 pre post2)

let bind_type_t1_t2_pre_post1_post2 (u1 u2:R.universe) (t1 t2 pre post1 post2:R.term) =
  let f_type = mk_stt_app u1 [t1; pre; post1] in
  mk_tot_arrow1 (f_type, R.Q_Explicit)
                (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)

let post2_type_bind t2 = mk_tot_arrow1 (t2, R.Q_Explicit) vprop_tm
let bind_type_t1_t2_pre_post1 (u1 u2:R.universe) (t1 t2 pre post1:R.term) =
  let var = 0 in
  let post2 = mk_name var in
  mk_tot_arrow1 (post2_type_bind t2, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2) (RT.CloseVar var) 0)

let post1_type_bind t1 = mk_tot_arrow1 (t1, R.Q_Explicit) vprop_tm
let bind_type_t1_t2_pre (u1 u2:R.universe) (t1 t2 pre:R.term) =
  let var = 1 in
  let post1 = mk_name var in
  mk_tot_arrow1 (post1_type_bind t1, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1) (RT.CloseVar var) 0)

let bind_type_t1_t2 (u1 u2:R.universe) (t1 t2:R.term) =
  let var = 2 in
  let pre = mk_name var in
  let pre_type = vprop_tm in
  mk_tot_arrow1 (pre_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2_pre u1 u2 t1 t2 pre) (RT.CloseVar var) 0)

let bind_type_t1 (u1 u2:R.universe) (t1:R.term) =
  let var = 3 in
  let t2 = mk_name var in
  let t2_type = RT.tm_type u2 in
  mk_tot_arrow1 (t2_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1_t2 u1 u2 t1 t2) (RT.CloseVar var) 0)

let bind_type (u1 u2:R.universe) =
  let var = 4 in
  let t1 = mk_name var in
  let t1_type = RT.tm_type u1 in
  mk_tot_arrow1 (t1_type, R.Q_Implicit)
                (RT.open_or_close_term' (bind_type_t1 u1 u2 t1) (RT.CloseVar var) 0)

(** Type of frame **)

let mk_star (l r:R.term) =
  let open R in
  let head = pack_ln (Tv_FVar (pack_fv star_lid)) in      
  R.mk_app head [(l, Q_Explicit); (r, Q_Explicit)]

let frame_res (u:R.universe) (t pre post frame:R.term) =
    mk_stt_app u [t; 
                  mk_star pre frame;
                  mk_abs t (mk_star (R.mk_app post [bound_var 0, R.Q_Explicit]) frame)]

let frame_type_t_pre_post_frame (u:R.universe) (t pre post frame:R.term) =
  let open R in
  let f_type = mk_stt_app u [t; pre; post] in
  mk_tot_arrow1 (f_type, Q_Explicit)
                (frame_res u t pre post frame)

let frame_type_t_pre_post (u:R.universe) (t pre post:R.term) =
  let var = 0 in
  let frame = mk_name var in
  mk_tot_arrow1 (vprop_tm, R.Q_Explicit)
                (RT.close_term (frame_res u t pre post frame) var)

let frame_type_t_pre (u:R.universe) (t pre:R.term) =
  let var = 1 in
  let post = mk_name var in
  let post_type = mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm in
  mk_tot_arrow1 (post_type, R.Q_Implicit)
                (RT.close_term (frame_type_t_pre_post u t pre post) var)

let frame_type_t (u:R.universe) (t:R.term) =
  let var = 2 in
  let pre = mk_name var in
  let pre_type = vprop_tm in
  mk_tot_arrow1 (pre_type, R.Q_Implicit)
                (RT.close_term (frame_type_t_pre u t pre) var)

let frame_type (u:R.universe) =
  let var = 3 in
  let t = mk_name var in
  let t_type = RT.tm_type u in
  mk_tot_arrow1 (t_type, R.Q_Implicit)
                (RT.close_term (frame_type_t u t) var)


(** Type of sub_stt **)

let stt_vprop_equiv_fv = R.pack_fv (mk_steel_wrapper_lid "vprop_equiv")
let stt_vprop_equiv_tm = R.pack_ln (R.Tv_FVar stt_vprop_equiv_fv)
let stt_vprop_equiv (t1 t2:R.term) = R.mk_app stt_vprop_equiv_tm [(t1, R.Q_Explicit); (t2, R.Q_Explicit)]

let stt_vprop_post_equiv_fv = R.pack_fv (mk_steel_wrapper_lid "vprop_post_equiv")
let stt_vprop_post_equiv_univ_inst u = R.pack_ln (R.Tv_UInst stt_vprop_post_equiv_fv [u])
let stt_vprop_post_equiv (u:R.universe) (t t1 t2:R.term) = 
  R.mk_app (stt_vprop_post_equiv_univ_inst u) 
           [(t, R.Q_Implicit); (t1, R.Q_Explicit); (t2, R.Q_Explicit)]

let sub_stt_res u t pre post = mk_stt_app u [t; pre; post]

let sub_stt_equiv_post u t pre1 post1 pre2 post2 = 
  mk_tot_arrow1 (stt_vprop_post_equiv u t post1 post2, R.Q_Explicit)
                (sub_stt_res u t pre2 post2)

let sub_stt_equiv_pre u t pre1 post1 pre2 post2 = 
  mk_tot_arrow1 (stt_vprop_equiv pre1 pre2, R.Q_Explicit)
                (sub_stt_equiv_post u t pre1 pre2 post1 post2)

let sub_stt_post2 u t pre1 post1 pre2 = 
  let var = 0 in
  let post2 = mk_name var in
  let post2_type = mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm in
  mk_tot_arrow1 (post2_type, R.Q_Explicit)
                (RT.close_term (sub_stt_equiv_pre u t pre1 pre2 post1 post2) var)

let sub_stt_pre2 u t pre1 post1 = 
  let var = 1 in
  let pre2 = mk_name var in
  let pre2_type = vprop_tm in
  mk_tot_arrow1 (pre2_type, R.Q_Explicit)
                (RT.close_term (sub_stt_post2 u t pre1 post1 pre2) var)

let sub_stt_post1 u t pre1 = 
  let var = 2 in
  let post1 = mk_name var in
  let post1_type = mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm in
  mk_tot_arrow1 (post1_type, R.Q_Explicit)
                (RT.close_term (sub_stt_pre2 u t pre1 post1) var)

let sub_stt_pre1 u t = 
  let var = 3 in
  let pre1 = mk_name var in
  let pre1_type = vprop_tm in
  mk_tot_arrow1 (pre1_type, R.Q_Explicit)
                (RT.close_term (sub_stt_post1 u t pre1) var)

let sub_stt_type u = 
  let var = 4 in
  let t = mk_name var in
  let ty_typ = RT.tm_type u in
  mk_tot_arrow1 (ty_typ, R.Q_Explicit)
                (RT.close_term (sub_stt_pre1 u t) var)

(** Properties of environments suitable for elaboration **)

let stt_env = 
  f:RT.fstar_top_env {
    RT.lookup_fvar f RT.bool_fv == Some (RT.tm_type RT.u_zero) /\
    RT.lookup_fvar f vprop_fv == Some (RT.tm_type (elab_universe (U_succ (U_succ U_zero)))) /\
    (forall (u1 u2:R.universe). RT.lookup_fvar_uinst f bind_fv [u1; u2] == Some (bind_type u1 u2)) /\
    (forall (u:R.universe). RT.lookup_fvar_uinst f frame_fv [u] == Some (frame_type u)) /\
    (forall (u:R.universe). RT.lookup_fvar_uinst f subsumption_fv [u] == Some (sub_stt_type u))        
  }

let check_top_level_environment (f:RT.fstar_top_env)
  : option stt_env
  = admit(); Some f //we should implement this as a runtime check

let elab_comp_post (c:pure_comp_st) : R.term =
  let t = elab_pure (comp_res c) in
  let post = elab_pure (comp_post c) in
  mk_abs t post

let comp_post_type (c:pure_comp_st) : R.term = 
  let t = elab_pure (comp_res c) in
  mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm

assume
val inversion_of_stt_typing (f:RT.fstar_top_env) (g:env) (c:pure_comp_st)
                            (u:R.universe)
                            // _ |- stt u#u t pre (fun (x:t) -> post) : Type _ 
                            (_:RT.typing (extend_env_l f g) (elab_pure_comp c) (RT.tm_type u))
  : GTot ( // _ |- t : Type u#u
          RT.typing (extend_env_l f g) (elab_pure (comp_res c)) (RT.tm_type (elab_universe (comp_u c))) &
          // _ |- pre : vprop
          RT.typing (extend_env_l f g) (elab_pure (comp_pre c)) (elab_pure (Tm_VProp)) &
          // _ |- (fun (x:t) -> post) : t -> vprop
          RT.typing (extend_env_l f g) (elab_comp_post c)
                                       (elab_pure (Tm_Arrow {binder_ty=comp_res c;binder_ppname="_"} (C_Tot Tm_VProp))))
