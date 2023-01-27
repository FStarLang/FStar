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
let mk_return (u:R.universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_lid) [u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_return_noeq (u:R.universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_noeq_lid) [u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

// Wrapper.lift_stt_atomic<u> #a #pre #post e
let mk_lift_atomic_stt (u:R.universe) (a pre post e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "lift_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.lift_stt_ghost<u> #a #opened #pre #post e reveal_a
let mk_lift_ghost_atomic (u:R.universe) (a opened pre post e reveal_a:R.term) =
  let open R in
  let lid = mk_steel_wrapper_lid "lift_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_a, Q_Explicit))

// Wrapper.bind_stt<u1, u2> #a #b #pre1 #post1 #post2 e1 e2
let mk_bind_stt
  (u1 u2:R.universe)
  (ty1 ty2:R.term)
  (pre1 post1: R.term)
  (post2: R.term)
  (t1 t2:R.term) 
  : R.term
  = let bind_lid = mk_steel_wrapper_lid "bind_stt" in
    let head = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
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

// Wrapper.bind_sttg<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2
let mk_bind_ghost
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_sttg" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  pack_ln (R.Tv_App t (e2, Q_Explicit))

// Wrapper.bind_stt_ghost_atomic<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_a
let mk_bind_ghost_atomic
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2 reveal_a:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_stt_ghost_atomic" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (e2, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_a, Q_Explicit))

// Wrapper.bind_stt_atomic_ghost<u1, u2> #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_b
let mk_bind_atomic_ghost
  (u1 u2:R.universe)
  (a b opened pre1 post1 post2 e1 e2 reveal_b:R.term) =
  let open R in
  let bind_lid = mk_steel_wrapper_lid "bind_stt_atomic_ghost" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (e2, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_b, Q_Explicit))

// Wrapper.frame_stt<u> #ty #pre #post frame t
let mk_frame_stt
  (u:R.universe)
  (ty:R.term)
  (pre: R.term)
  (post: R.term)
  (frame: R.term)
  (t:R.term) 
  : R.term
  = let frame_lid = mk_steel_wrapper_lid "frame_stt" in
    let frame_fv = R.pack_fv frame_lid in
    let frame_univ_inst u = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid) [u]) in
    let head = frame_univ_inst u in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app head [(ty, R.Q_Implicit)])
            [(pre, R.Q_Implicit)])
          [(post, R.Q_Implicit)])
        [(frame, R.Q_Explicit)])
      [(t, R.Q_Explicit)]

// Wrapper.frame_stt_atomic<u> #a #opened #pre #post frame e
let mk_frame_stt_atomic (u:R.universe) (a opened pre post frame e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "frame_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.frame_stt_ghost<u> #a #opened #pre #post frame e
let mk_frame_stt_ghost (u:R.universe) (a opened pre post frame e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "frame_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.sub_stt<u> #ty #pre1 pre2 #post1 post2 () () e
let mk_sub_stt
  (u:R.universe)
  (ty:R.term)
  (pre1 pre2: R.term)
  (post1 post2: R.term)
  (t:R.term) 
  : R.term
  = let subsumption_lid = mk_steel_wrapper_lid "sub_stt" in
    let subsumption_fv = R.pack_fv subsumption_lid in
    let subsumption_univ_inst u = R.pack_ln (R.Tv_UInst subsumption_fv [u]) in
    let head = subsumption_univ_inst u in
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
        [(`(), R.Q_Explicit)])
      [(`(), R.Q_Explicit)])
     [(t, R.Q_Explicit)]

// Wrapper.sub_stt_atomic<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_atomic (u:R.universe) (a opened pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "sub_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.sub_stt_ghost<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_ghost (u:R.universe) (a opened pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_steel_wrapper_lid "sub_stt_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

let elab_frame (c:pure_comp_st) (frame:pure_term) (e:R.term) =
  let u = elab_universe (comp_u c) in
  let ty = elab_pure (comp_res c) in
  let pre = elab_pure (comp_pre c) in
  let post = elab_pure (comp_post c) in
  if C_ST? c
  then mk_frame_stt u ty pre (mk_abs ty R.Q_Explicit post) (elab_pure frame) e
  else let opened = elab_pure (comp_inames c) in      
       if C_STAtomic? c
       then mk_frame_stt_atomic u ty opened pre (mk_abs ty R.Q_Explicit post) (elab_pure frame) e
       else let _ = assert (C_STGhost? c) in
            mk_frame_stt_ghost u ty opened pre (mk_abs ty R.Q_Explicit post) (elab_pure frame) e

let elab_sub (c1 c2:pure_comp_st) (e:R.term) =
  let ty = elab_pure (comp_res c1) in
  let u = elab_universe (comp_u c1) in
  let pre1 = elab_pure (comp_pre c1) in
  let pre2 = elab_pure (comp_pre c2) in
  let post1 = mk_abs ty R.Q_Explicit (elab_pure (comp_post c1)) in
  let post2 = mk_abs ty R.Q_Explicit (elab_pure (comp_post c2)) in
  if C_ST? c1
  then mk_sub_stt u ty pre1 pre2 post1 post2 e
  else let opened = elab_pure (comp_inames c1) in
       if C_STAtomic? c1
       then mk_sub_stt_atomic u ty opened pre1 pre2 post1 post2 e
       else let _ = assert (C_STGhost? c1) in
            mk_sub_stt_ghost u ty opened pre1 pre2 post1 post2 e

#push-options "--z3rlimit_factor 4"
let rec elab_bind #f #g #x #c1 #c2 #c
  (bc:bind_comp f g x c1 c2 c)
  (e1 e2:R.term)
  : Tot R.term (decreases bc) =

  let t1 = elab_pure (comp_res c1) in
  let t2 = elab_pure (comp_res c2) in

  match bc with
  | Bind_comp _ _ _ _ _ _ _ ->
    if C_ST? c1
    then
      mk_bind_stt
        (elab_universe (comp_u c1))
        (elab_universe (comp_u c2))
        t1 t2
        (elab_pure (comp_pre c1))
        (mk_abs t1 R.Q_Explicit (elab_pure (comp_post c1)))
        (mk_abs t2 R.Q_Explicit (elab_pure (comp_post c2)))
        e1 e2
    else 
      mk_bind_ghost
        (elab_universe (comp_u c1))
        (elab_universe (comp_u c2))
        t1 t2
        (elab_pure (comp_inames c1))
        (elab_pure (comp_pre c1))
        (mk_abs t1 R.Q_Explicit (elab_pure (comp_post c1)))
        (mk_abs t2 R.Q_Explicit (elab_pure (comp_post c2)))
        e1 e2

  | Bind_comp_ghost_l _ _ _ _ (| reveal_a, reveal_a_typing |) _ _ _ ->
    mk_bind_ghost_atomic
      (elab_universe (comp_u c1))
      (elab_universe (comp_u c2))
      t1 t2
      (elab_pure (comp_inames c1))
      (elab_pure (comp_pre c1))
      (mk_abs t1 R.Q_Explicit (elab_pure (comp_post c1)))
      (mk_abs t2 R.Q_Explicit (elab_pure (comp_post c2)))
      e1 e2
      (elab_src_typing reveal_a_typing)

  | Bind_comp_ghost_r _ _ _ _ (| reveal_b, reveal_b_typing |) _ _ _ ->
    mk_bind_atomic_ghost
      (elab_universe (comp_u c1))
      (elab_universe (comp_u c2))
      t1 t2
      (elab_pure (comp_inames c1))
      (elab_pure (comp_pre c1))
      (mk_abs t1 R.Q_Explicit (elab_pure (comp_post c1)))
      (mk_abs t2 R.Q_Explicit (elab_pure (comp_post c2)))
      e1 e2
      (elab_src_typing reveal_b_typing)

and elab_lift #f #g #c1 #c2 (d:lift_comp f g c1 c2) (e:R.term)
  : Tot R.term (decreases d) =

  match d with
  | Lift_STAtomic_ST _ _ ->
    let t = elab_pure (comp_res c1) in
    mk_lift_atomic_stt
      (elab_universe (comp_u c1))
      (elab_pure (comp_res c1))
      t
      (mk_abs t R.Q_Explicit (elab_pure (comp_post c1)))
      e
      
  | Lift_STGhost_STAtomic _ _ (| reveal_a, reveal_a_typing |) ->
    let t = elab_pure (comp_res c1) in
    mk_lift_ghost_atomic
      (elab_universe (comp_u c1))
      t
      (elab_pure (comp_inames c1))
      (elab_pure (comp_pre c1))
      (mk_abs t R.Q_Explicit (elab_pure (comp_post c1)))
      e
      (elab_src_typing reveal_a_typing)

and elab_src_typing
  (#f:RT.fstar_top_env)
  (#g:env)
  (#t:term)
  (#c:pure_comp)
  (d:src_typing f g t c)
  : Tot R.term (decreases d)

  = match d with
    | T_Tot _ _ _ _ -> elab_pure t

    | T_Abs _ _ x qual ty _u body _ _ _ ty_typing body_typing ->
      let ty = elab_pure ty in
      let body = elab_src_typing body_typing in
      mk_abs ty (elab_qual qual) (RT.close_term body x) //this closure should be provably redundant by strengthening the conditions on x
    
    | T_STApp _ head _ppname _formal qual _res arg head_typing arg_typing ->
      let head = elab_src_typing head_typing in
      let arg = elab_pure arg in
      R.mk_app head [(arg, elab_qual qual)]

    | T_Return _ _ ty u _ _ ->
      mk_return (elab_universe u) (elab_pure ty) (elab_pure t)

    | T_ReturnNoEq _ _ ty u t_typing _ ->
      mk_return_noeq (elab_universe u) (elab_pure ty) (elab_src_typing t_typing)

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc ->
      let e1 = elab_src_typing e1_typing in
      let e2 = elab_src_typing e2_typing in
      let ty1 = elab_pure (comp_res c1) in
      elab_bind bc e1 (mk_abs ty1 R.Q_Explicit (RT.close_term e2 x))
      
    | T_Frame _ _ c frame _frame_typing e_typing ->
      let e = elab_src_typing e_typing in
      elab_frame c frame e
      
    // | T_If _ b e1 e2 _c hyp _ e1_typing e2_typing ->
    //   let b = elab_pure b in
    //   let e1 = elab_src_typing e1_typing in
    //   let e2 = elab_src_typing e2_typing in
    //   let open R in
    //   pack_ln (Tv_Match b None 
    //               [(Pat_Constant C_True, e1);
    //                (Pat_Constant C_False, e2)])

    | T_Equiv _ _ c1 c2 e_typing _ ->
      let e = elab_src_typing e_typing in
      elab_sub c1 c2 e

    | T_Lift _ _ c1 c2 e_typing lc ->
      let e = elab_src_typing e_typing in
      elab_lift lc e
#pop-options

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
    // | T_If _ _ _ _ _ _ _ d1 d2 -> 
    //   elab_pure_equiv d1; 
    //   elab_pure_equiv d2      
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
    elab_open_commute' t (null_var x) 0

#push-options "--fuel 10 --ifuel 6 --z3rlimit_factor 25"
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
    | Tm_Var _
    | Tm_BVar _
    | Tm_FVar _
    | Tm_UInst _ _
    | Tm_Constant _
    | Tm_Emp 
    | Tm_Type _
    | Tm_Inames
    | Tm_EmpInames
    | Tm_VProp -> ()
    | Tm_Refine b phi ->
      elab_close_commute' b.binder_ty v n;
      elab_close_commute' phi v (n + 1)
    | Tm_PureApp e1 _ e2 ->
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
    | Tm_Arrow b _ body ->
      elab_close_commute' b.binder_ty v n;
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
   | C_STAtomic inames s
   | C_STGhost inames s ->
      admit ();
      elab_close_commute' inames v n;
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
