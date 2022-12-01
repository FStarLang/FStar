module Pulse.Elaborate
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

let return_lid = ["Steel"; "ST"; "Util"; "return_stt"]
let return_noeq_lid = ["Steel"; "ST"; "Util"; "return_stt_noeq"]

(* 
  inline_for_extraction
  let bind_stt : stt t1 p1 q1 -> (x:t1 -> stt t2 (q1 x) q2) -> stt t2 p1 q2
*)
let bind_lid = ["Steel"; "ST"; "Util"; "bind_stt"]

let bind_fv = R.pack_fv bind_lid
let bind_univ_inst u1 u2 = R.pack_ln (R.Tv_UInst bind_fv [u1;u2])


(* 
  inline_for_extraction
  let frame_stt : stt t1 p1 q1 -> (stt t1 (pre * f) (fun x -> q1 x * f)
*)
let frame_lid = ["Steel"; "ST"; "Util"; "frame_stt"]


(* 
  inline_for_extraction
  let sub_stt : stt t1 p1 q1 { p1 `equiv` p2 /\ forall x. q1 x `equiv` q2 x } -> stt t1 p2 q2
*)
let subsumption_lid = ["Steel"; "ST"; "Util"; "sub_stt"]

let mk_return (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_return_noeq (u:universe) (ty:R.term) (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv return_noeq_lid) [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit); (t, R.Q_Explicit)]

let mk_frame (u:universe)
             (ty:R.term)
             (pre: R.term)
             (post: R.term)
             (frame: R.term)
             (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid)
                         [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit);
                   (pre, R.Q_Implicit);
                   (post, R.Q_Implicit);
                   (frame, R.Q_Explicit);
                   (t, R.Q_Explicit)]

let mk_sub (u:universe)
           (ty:R.term)
           (pre1 pre2: R.term)
           (post1 post2: R.term)
           (t:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv subsumption_lid)
                         [elab_universe u]) in
    R.mk_app head [(ty, R.Q_Implicit);
                   (pre1, R.Q_Implicit);
                   (pre2, R.Q_Explicit);                   
                   (post1, R.Q_Implicit);
                   (post2, R.Q_Explicit);                   
                   (t, R.Q_Explicit)]


let mk_bind (u1 u2:universe)
            (ty1 ty2:R.term)
            (pre1 post1: R.term)
            (post2: R.term)
            (t1 t2:R.term) 
  : R.term
  = let head = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid)
                         [elab_universe u1; elab_universe u2]) in
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

let rec elab_src_typing (#f:fstar_top_env)
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
      mk_return u (elab_pure ty) (elab_src_typing t_typing)

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
      mk_frame c.u ty pre post (elab_pure frame) e
      
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
      mk_sub c1.u ty
             (elab_pure c1.pre)
             (elab_pure c2.pre)
             (mk_abs ty (elab_pure c1.post))
             (mk_abs ty (elab_pure c2.post))
             e

      

