module Pulse.Elaborate
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

let return_lid = mk_steel_wrapper_lid "return_stt"
let return_noeq_lid = mk_steel_wrapper_lid "return_stt_noeq"

let bind_lid = mk_steel_wrapper_lid "bind_stt"
let bind_fv = R.pack_fv bind_lid
let bind_univ_inst u1 u2 = R.pack_ln (R.Tv_UInst bind_fv [u1;u2])

let frame_lid = mk_steel_wrapper_lid "frame_stt"
let frame_fv = R.pack_fv frame_lid
let frame_univ_inst u = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid) [u])

let subsumption_lid = mk_steel_wrapper_lid "sub_stt"
let subsumption_fv = R.pack_fv subsumption_lid
let subsumption_univ_inst u = R.pack_ln (R.Tv_UInst subsumption_fv [u])

let mk_return (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_return_noeq (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_noeq_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_bind (u1 u2:universe)
            (ty1 ty2:R.term)
            (pre1 post1: R.term)
            (post2: R.term)
            (t1 t2:R.term) 
  : R.term
  = let head = bind_univ_inst (elab_universe u1) (elab_universe u2) in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app 
            (R.mk_app 
              (R.mk_app 
                (R.mk_app head
                          [(ty1, R.Q_Implicit)])
                [(ty2, R.Q_Implicit)])
              [(pre1, R.Q_Implicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Implicit)])
        [(t1, R.Q_Explicit)])
      [(t2, R.Q_Explicit)]

let mk_frame (u:universe)
             (ty:R.term)
             (pre: R.term)
             (post: R.term)
             (frame: R.term)
             (t:R.term) 
  : R.term
  = let head = frame_univ_inst (elab_universe u) in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app head [(ty, R.Q_Implicit)])
            [(pre, R.Q_Implicit)])
          [(post, R.Q_Implicit)])
        [(frame, R.Q_Explicit)])
      [(t, R.Q_Explicit)]

let mk_sub (u:R.universe)
           (ty:R.term)
           (pre1 pre2: R.term)
           (post1 post2: R.term)
           (t:R.term) 
  : R.term
  = let head = subsumption_univ_inst u in
    R.mk_app
     (R.mk_app 
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app
              (R.mk_app 
                 (R.mk_app head [(ty, R.Q_Implicit)])
                 [(pre1, R.Q_Implicit)])
              [(pre2, R.Q_Explicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Explicit)])
        [(t, R.Q_Explicit)])
      [(`(), R.Q_Explicit)])
     [(`(), R.Q_Explicit)]      

let elab_bind (c1 c2:pure_comp_st) (e1 e2:R.term) =
  let C_ST c1 = c1 in
  let C_ST c2 = c2 in
  let ty1 = elab_pure c1.res in
  let ty2 = elab_pure c2.res in
  mk_bind c1.u c2.u
          ty1 ty2
          (elab_pure c1.pre)
          (mk_abs ty1 (elab_pure c1.post))
          (mk_abs ty2 (elab_pure c2.post))
          e1 e2

let rec elab_src_typing (#f:RT.fstar_top_env)
                        (#g:env)
                        (#t:term)
                        (#c:pure_comp)
                        (d:src_typing f g t c)
  : Tot R.term (decreases d)
  = match d with
    | T_Tot _ _ _ _ -> elab_pure t

    | T_Abs _ x ty _u body _ _ ty_typing body_typing ->
      let ty = elab_pure ty in
      let body = elab_src_typing body_typing in
      mk_abs ty (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x
    
    | T_STApp _ head _formal _res arg head_typing arg_typing ->
      let head = elab_src_typing head_typing in
      let arg = elab_pure arg in
      R.mk_app head [(arg, R.Q_Explicit)]

    | T_Return _ _ ty u _ _ ->
      mk_return u (elab_pure ty) (elab_pure t)

    | T_ReturnNoEq _ _ ty u t_typing _ ->
      mk_return_noeq u (elab_pure ty) (elab_src_typing t_typing)

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing _bc ->
      let e1 = elab_src_typing e1_typing in
      let e2 = elab_src_typing e2_typing in
      let ty1 = elab_pure (comp_res c1) in
      elab_bind c1 c2 e1 (mk_abs ty1 (RT.close_term e2 x))
      
    | T_Frame _ _ c frame _frame_typing e_typing ->
      let e = elab_src_typing e_typing in
      let C_ST c = c in
      let ty = elab_pure c.res in
      let pre = elab_pure c.pre in
      let post = elab_pure c.post in
      mk_frame c.u ty pre (mk_abs ty post) (elab_pure frame) e
      
    | T_If _ b e1 e2 _c hyp _ e1_typing e2_typing ->
      let b = elab_pure b in
      let e1 = elab_src_typing e1_typing in
      let e2 = elab_src_typing e2_typing in
      let open R in
      pack_ln (Tv_Match b None 
                  [(Pat_Constant C_True, e1);
                   (Pat_Constant C_False, e2)])

    | T_Equiv _ _ c1 c2 e_typing _ ->
      let e = elab_src_typing e_typing in
      let C_ST c1 = c1 in
      let C_ST c2 = c2 in
      let ty = elab_pure c1.res in
      mk_sub (elab_universe c1.u)
             ty
             (elab_pure c1.pre)
             (elab_pure c2.pre)
             (mk_abs ty (elab_pure c1.post))
             (mk_abs ty (elab_pure c2.post))
             e

#push-options "--ifuel 2"
let rec elab_pure_equiv (#f:RT.fstar_top_env)
                        (#g:env)
                        (#t:pure_term)
                        (#c:pure_comp { C_Tot? c })
                        (d:src_typing f g t c)
  : Lemma (ensures elab_src_typing d == elab_pure t)
          (decreases d)
  = match d with
    | T_Tot _ _ _ d -> ()
    | T_If _ _ _ _ _ _ _ d1 d2 -> 
      elab_pure_equiv d1; 
      elab_pure_equiv d2      
#pop-options


let rec elab_open_commute' (e:pure_term)
                           (v:pure_term)
                           (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure e) (RT.OpenWith (elab_pure v)) n ==
              elab_pure (open_term' e v n))
          (decreases e)
  = admit()
and elab_comp_open_commute' (c:pure_comp) (v:pure_term) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.OpenWith (elab_pure v)) n ==
              elab_pure_comp (open_comp' c v n))
          (decreases c)
  = admit()

let elab_open_commute (t:pure_term) (x:var)
  : Lemma (elab_pure (open_term t x) == RT.open_term (elab_pure t) x)
  = RT.open_term_spec (elab_pure t) x;
    elab_open_commute' t (Tm_Var x) 0

#push-options "--fuel 8 --ifuel 4 --z3rlimit_factor 10"
let rec elab_close_commute' (e:pure_term)
                            (v:var)
                            (n:index)
  : Lemma (ensures (
              closing_pure_term e v n;
              RT.open_or_close_term' (elab_pure e) (RT.CloseVar v) n ==
              elab_pure (close_term' e v n)))
          (decreases e)
  = closing_pure_term e v n;
    match e with
    | Tm_BVar _ 
    | Tm_Var _ 
    | Tm_FVar _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _ 
    | Tm_VProp -> ()
    | Tm_PureApp e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_Let t e1 e2 ->
      elab_close_commute' t v n;    
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v (n + 1)
    | Tm_Pure p ->
      elab_close_commute' p v n
    | Tm_Star e1 e2 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n
    | Tm_ExistsSL t body
    | Tm_ForallSL t body ->
      elab_close_commute' t v n;
      elab_close_commute' body v (n + 1)    
    | Tm_Arrow t body ->
      elab_close_commute' t v n;
      elab_comp_close_commute' body v (n + 1)
    | Tm_If e1 e2 e3 ->
      elab_close_commute' e1 v n;
      elab_close_commute' e2 v n;
      elab_close_commute' e3 v n

and elab_comp_close_commute' (c:pure_comp) (v:var) (n:index)
  : Lemma (ensures
              RT.open_or_close_term' (elab_pure_comp c) (RT.CloseVar v) n ==
              elab_pure_comp (close_comp' c v n))
          (decreases c)
  = match c with
    | C_Tot t -> elab_close_commute' t v n
    | C_ST s -> 
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)           
#pop-options


let elab_comp_close_commute (c:pure_comp) (x:var)
  : Lemma (elab_pure_comp (close_pure_comp c x) == RT.close_term (elab_pure_comp c) x)
  = RT.close_term_spec (elab_pure_comp c) x;
    elab_comp_close_commute' c x 0

let elab_comp_open_commute (c:pure_comp) (x:pure_term)
  : Lemma (elab_pure_comp (open_comp_with c x) == RT.open_with (elab_pure_comp c) (elab_pure x))
  = RT.open_with_spec (elab_pure_comp c) (elab_pure x);
    elab_comp_open_commute' c x 0
