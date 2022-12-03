module Pulse.Soundness
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate


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
    | T_If _ _ _ _ _ _ _ _ _ -> admit() //make T_If stateful

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

////////////////////////////////////////////////////////////////////////////////

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
                                       (elab_pure (Tm_Arrow (comp_res c) (C_Tot Tm_VProp))))


(* x:t1 -> stt t2 pre post   ~    x:t1 -> stt t2 ((fun x -> pre) x) post *)
let equiv_arrow (g:R.env) (t1:R.term) (u2:R.universe) (t2:R.term) (pre:R.term) (post:R.term) //need some ln preconditions
  : GTot (RT.equiv g (mk_tot_arrow1 (t1, R.Q_Explicit)
                                    (mk_stt_app u2 [t2; pre; post]))
                     (mk_tot_arrow1 (t1, R.Q_Explicit)
                                    (mk_stt_app u2 [t2; R.mk_app (mk_abs t1 pre) [bound_var 0, R.Q_Explicit]; post])))
  = admit()

#push-options "--z3rlimit_factor 5"
(*** Soundness of bind elaboration *)


#push-options "--fuel 2 --ifuel 1 --query_stats"
let inst_bind_t1 #u1 #u2 #g #head
                   (head_typing: RT.typing g head (bind_type u1 u2))
                   (#t1:_)
                   (t1_typing: RT.typing g t1 (RT.tm_type u1))
  : GTot (RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) (bind_type_t1 u1 u2 t1))
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(t1, R.Q_Implicit)]) _ =
      RT.T_App _ _ _ _ _ _ head_typing t1_typing
    in
    assume (bind_type_t1 u1 u2 t1 ==
            RT.open_with (RT.open_or_close_term' (bind_type_t1 u1 u2 (mk_name 4))
                                                 (RT.CloseVar 4) 0)
                         t1);

    d
#pop-options    



let inst_bind_t2 #u1 #u2 #g #head #t1
                   (head_typing: RT.typing g head (bind_type_t1 u1 u2 t1))
                   (#t2:_)
                   (t2_typing: RT.typing g t2 (RT.tm_type u2))
  : RT.typing g (R.mk_app head [(t2, R.Q_Implicit)]) (bind_type_t1_t2 u1 u2 t1 t2)
  = admit()


let inst_bind_pre #u1 #u2 #g #head #t1 #t2
                  (head_typing: RT.typing g head (bind_type_t1_t2 u1 u2 t1 t2))
                  (#pre:_)
                  (pre_typing: RT.typing g pre vprop_tm)
  : RT.typing g (R.mk_app head [(pre, R.Q_Implicit)]) (bind_type_t1_t2_pre u1 u2 t1 t2 pre)
  = admit()

let inst_bind_post1 #u1 #u2 #g #head #t1 #t2 #pre
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre u1 u2 t1 t2 pre))
                  (#post1:_)
                  (post1_typing: RT.typing g post1 (post1_type_bind t1))
  : RT.typing g (R.mk_app head [(post1, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1)
  = admit()

let inst_bind_post2 #u1 #u2 #g #head #t1 #t2 #pre #post1
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1 u1 u2 t1 t2 pre post1))
                  (#post2:_)
                  (post2_typing: RT.typing g post2 (post2_type_bind t2))
  : RT.typing g (R.mk_app head [(post2, R.Q_Implicit)]) (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_f #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2 u1 u2 t1 t2 pre post1 post2))
                  (#f:_)
                  (f_typing: RT.typing g f (mk_stt_app u1 [t1; pre; post1]))
  : RT.typing g (R.mk_app head [(f, R.Q_Explicit)]) (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2)
  = admit()

let inst_bind_g #u1 #u2 #g #head #t1 #t2 #pre #post1 #post2
                  (head_typing: RT.typing g head (bind_type_t1_t2_pre_post1_post2_f u1 u2 t1 t2 pre post1 post2))
                  (#gg:_)
                  (g_typing: RT.typing g gg (g_type_bind u2 t1 t2 post1 post2))
  : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) (bind_res u2 t2 pre post2)
  = let open_with_spec (t v:R.term)
      : Lemma (RT.open_with t v == RT.open_or_close_term' t (RT.OpenWith v) 0)
              [SMTPat (RT.open_with t v)]
      = RT.open_with_spec t v
    in
    let d : RT.typing g (R.mk_app head [(gg, R.Q_Explicit)]) _ =
      RT.T_App _ _ _ _ _ _ head_typing g_typing
    in
    admit();
    d


let elab_bind_typing (f:stt_env)
                     (g:env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.typing (extend_env_l f g) r1 (elab_pure_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.typing (extend_env_l f g) r2 
                                           (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x))))
                     (bc:bind_comp f g x c1 c2 c)
                     (t2_typing : RT.typing (extend_env_l f g) (elab_pure (comp_res c2)) (RT.tm_type (elab_universe (comp_u c2))))
                     (post2_typing: RT.typing (extend_env_l f g) (elab_comp_post c2) (post2_type_bind (elab_pure (comp_res c2)))) 
  : GTot (RT.typing (extend_env_l f g) (elab_bind c1 c2 r1 r2) (elab_pure_comp c))
  = let rg = extend_env_l f g in
    let u1 = elab_universe (comp_u c1) in
    let u2 = elab_universe (comp_u c2) in
    let head = bind_univ_inst u1 u2 in
    assert (RT.lookup_fvar_uinst rg bind_fv [u1; u2] == Some (bind_type u1 u2));
    let head_typing : RT.typing _ _ (bind_type u1 u2) = RT.T_UInst rg bind_fv [u1;u2] in
    let (| _, c1_typing |) = RT.type_correctness _ _ _ r1_typing in
    let t1_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ _ _ c1_typing in
    let t1 = (elab_pure (comp_res c1)) in
    let t2 = (elab_pure (comp_res c2)) in
    let t1_typing : RT.typing rg t1 (RT.tm_type u1) = t1_typing in
    let post1 = elab_comp_post c1 in
    let c2_x = close_pure_comp c2 x in
    assume (comp_res c2_x == comp_res c2);
    assume (comp_post c2_x == comp_post c2);    
    assert (open_term (comp_post c1) x == comp_pre c2);
    assert (~ (x `Set.mem` freevars (comp_post c1)));
    close_open_inverse (comp_post c1) x;
    assert (comp_post c1 == close_term (comp_pre c2) x);
    assert (post1 == mk_abs t1 (elab_pure (comp_post c1)));
    assert (elab_pure (comp_post c1) == elab_pure (comp_pre (close_pure_comp c2 x)));
    //ln (comp_post c1) 0
    let g_typing
      : RT.typing _ _ 
                  (mk_tot_arrow1 (t1, R.Q_Explicit)
                                 (mk_stt_app u2 [t2; elab_pure (comp_post c1); elab_comp_post c2]))
      = r2_typing in
    let g_typing 
      : RT.typing _ _ 
                  (mk_tot_arrow1 (t1, R.Q_Explicit)
                                 (mk_stt_app u2 [t2; R.mk_app (mk_abs t1 (elab_pure (comp_post c1))) [bound_var 0, R.Q_Explicit]; elab_comp_post c2]))
      = RT.(T_Sub _ _ _ _ r2_typing (ST_Equiv _ _ _ (equiv_arrow _ _ _ _ _ _))) in
    let d : RT.typing _ (elab_bind c1 c2 r1 r2) _ = 
       inst_bind_g 
        (inst_bind_f
          (inst_bind_post2
            (inst_bind_post1
              (inst_bind_pre 
                (inst_bind_t2 
                  (inst_bind_t1 head_typing t1_typing)
                  t2_typing)
                pre_typing)
              post_typing)
            post2_typing)
          r1_typing)
        g_typing
    in
    d

(*** Soundness of frame elaboration *)


#push-options "--fuel 2 --ifuel 1 --query_stats"
let inst_frame_t #u #g #head
                 (head_typing: RT.typing g head (frame_type u))
                 (#t:_)
                 (t_typing: RT.typing g t (RT.tm_type u))
  : GTot (RT.typing g (R.mk_app head [(t, R.Q_Implicit)]) (frame_type_t u t))
  = admit()

let inst_frame_pre #u #g #head #t
                 (head_typing: RT.typing g head (frame_type_t u t))
                 (#pre:_)
                 (pre_typing: RT.typing g pre vprop_tm)
  : GTot (RT.typing g (R.mk_app head [(pre, R.Q_Implicit)]) (frame_type_t_pre u t pre))
  = admit()

let inst_frame_post #u #g #head #t #pre
                    (head_typing: RT.typing g head (frame_type_t_pre u t pre))
                    (#post:_)
                    (post_typing: RT.typing g post (mk_tot_arrow1 (t, R.Q_Explicit) vprop_tm))
  : GTot (RT.typing g (R.mk_app head [(post, R.Q_Implicit)]) (frame_type_t_pre_post u t pre post))
  = admit()

let inst_frame_frame #u #g #head #t #pre #post
                     (head_typing: RT.typing g head (frame_type_t_pre_post u t pre post))
                     (#frame:_)
                     (frame_typing: RT.typing g frame vprop_tm)
  : GTot (RT.typing g (R.mk_app head [(frame, R.Q_Explicit)]) (frame_type_t_pre_post_frame u t pre post frame))
  = admit()

let inst_frame_comp #u #g #head #t #pre #post #frame
                    (head_typing: RT.typing g head (frame_type_t_pre_post_frame u t pre post frame))
                    (#f:_)
                    (f_typing:RT.typing g f (mk_stt_app u [t; pre; post]))
  : GTot (RT.typing g (R.mk_app head [(f, R.Q_Explicit)]) (frame_res u t pre post frame))
  = admit()

let elab_frame (c:pure_comp { C_ST? c }) (frame:pure_term) (e:R.term) =
  let C_ST s = c in
  Elaborate.mk_frame s.u (elab_pure s.res) (elab_pure s.pre) (elab_comp_post c) (elab_pure frame) e

(* stt t pre (fun x -> (fun x -> post) x * frame)   ~ 
   stt t pre (fun x -> post * frame) *)
let equiv_frame_post (g:R.env) 
                     (u:R.universe)
                     (t:R.term)
                     (pre:R.term) 
                     (post:pure_term) // ln 1
                     (frame:R.term) //ln 0
  : GTot (RT.equiv g (mk_stt_app u [t; pre; mk_abs t (mk_star (R.mk_app (mk_abs t (elab_pure post))
                                                                        [bound_var 0, R.Q_Explicit]) frame)])
                     (mk_stt_app u [t; pre; mk_abs t (mk_star (elab_pure post) frame)]))
  = admit()

let elab_frame_typing (f:stt_env)
                      (g:env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:pure_term)
                      (frame_typing: RT.typing (extend_env_l f g) (elab_pure frame) (elab_pure Tm_VProp))
                      (e_typing: RT.typing (extend_env_l f g) e (elab_pure_comp c))
  : GTot (RT.typing (extend_env_l f g) (elab_frame c frame e) (elab_pure_comp (add_frame c frame)))
  = let rg = extend_env_l f g in
    let u = elab_universe (comp_u c) in
    let head = frame_univ_inst u in
    assert (RT.lookup_fvar_uinst rg frame_fv [u] == Some (frame_type u));
    let head_typing : RT.typing _ _ (frame_type u) = RT.T_UInst rg frame_fv [u] in
    let (| _, c_typing |) = RT.type_correctness _ _ _ e_typing in
    let t_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ _ _ c_typing in
    let t = elab_pure (comp_res c) in
    let t_typing : RT.typing rg t (RT.tm_type u) = t_typing in
    let d : RT.typing (extend_env_l f g)
                      (elab_frame c frame e)
                      (frame_res u t (elab_pure (comp_pre c))
                                     (elab_comp_post c)
                                     (elab_pure frame)) =
        inst_frame_comp
          (inst_frame_frame
            (inst_frame_post
                (inst_frame_pre 
                  (inst_frame_t head_typing t_typing)
                 pre_typing)
             post_typing)
           frame_typing)
          e_typing
    in
    RT.T_Sub _ _ _ _ d RT.(ST_Equiv _ _ _ (equiv_frame_post rg u t 
                                                         (elab_pure (Tm_Star (comp_pre c) frame))
                                                         (comp_post c)
                                                         (elab_pure frame)))
#pop-options    

(*** Soundness of vprop equivalence **)

let vprop_equiv_refl_type = 
  let var = 0 in
  let v = mk_name var in
  let v_typ = elab_pure Tm_VProp in
  mk_tot_arrow1 (v_typ, R.Q_Explicit)
                (RT.close_term (stt_vprop_equiv v v) var)

let inst_vprop_equiv_refl #g #v
                          (d:RT.typing g v (elab_pure Tm_VProp))
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv v v))
  = admit()

let vprop_equiv_sym_type = 
  let var0 = 0 in
  let v0 = mk_name var0 in
  let var1 = 1 in
  let v1 = mk_name var1 in
  let v_typ = elab_pure Tm_VProp in
  mk_tot_arrow1 
    (v_typ, R.Q_Implicit)
    (RT.close_term
      (mk_tot_arrow1 
        (v_typ, R.Q_Implicit)
        (RT.close_term 
          (mk_tot_arrow1 
             (stt_vprop_equiv v0 v1, R.Q_Explicit)
             (stt_vprop_equiv v0 v1)) var1))
        var0)
            
let inst_vprop_equiv_sym #g #v0 #v1
                         (d0:RT.typing g v0 (elab_pure Tm_VProp))
                         (d1:RT.typing g v1 (elab_pure Tm_VProp))
                         (#pf:_)
                         (deq:RT.typing g pf (stt_vprop_equiv v0 v1))
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv v1 v0))
  = admit()

let inst_vprop_equiv_trans #g #v0 #v1 #v2
                         (d0:RT.typing g v0 (elab_pure Tm_VProp))
                         (d1:RT.typing g v1 (elab_pure Tm_VProp))
                         (d2:RT.typing g v2 (elab_pure Tm_VProp))
                         (#pf01:_)
                         (d01:RT.typing g pf01 (stt_vprop_equiv v0 v1))
                         (#pf12:_)                         
                         (d12:RT.typing g pf12 (stt_vprop_equiv v1 v2))
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv v0 v2))
  = admit()

let rec vprop_equiv_soundness (f:stt_env) (g:env) (v0 v1:pure_term) 
                              (d:tot_typing f g v0 Tm_VProp)
                              (eq:vprop_equiv f g v0 v1)
  : GTot (pf:R.term &
          RT.typing (extend_env_l f g) pf (stt_vprop_equiv (elab_pure v0) (elab_pure v1)))
         (decreases eq)
  = match eq with
    | VE_Refl _ _ ->
      let d = tot_typing_soundness d in
      inst_vprop_equiv_refl d

    | VE_Sym g _v1 _v0 eq' ->
      let fwd, _ = vprop_equiv_typing _ _ _ _ eq in
      let d' = fwd d in
      let (| pf, dd |) = vprop_equiv_soundness _ _ _ _ d' eq' in
      inst_vprop_equiv_sym (tot_typing_soundness d')
                           (tot_typing_soundness d)
                           dd

    | VE_Trans _ _ v _ eq_0v eq_v1 ->
      let dv = fst (vprop_equiv_typing _ _ _ _ eq_0v) d in
      let d1 = fst (vprop_equiv_typing _ _ _ _ eq_v1) dv in
      let (| pf_0v, eq_0v |) = vprop_equiv_soundness _ _ _ _ d eq_0v in
      let (| pf_v1, eq_v1 |) = vprop_equiv_soundness _ _ _ _ dv eq_v1 in
      inst_vprop_equiv_trans 
        (tot_typing_soundness d)
        (tot_typing_soundness dv)        
        (tot_typing_soundness d1)
        eq_0v
        eq_v1
                             
    | _ -> admit()

(*** Soundness of st equivalence **)
let st_equiv_soundness (f:stt_env) (g:env) (c0 c1:ln_comp)
  : GTot (RT.typing (extend_env_l f g) (`()) (stt_vprop_equiv (elab_pure (comp_pre c0)) (elab_pure (comp_pre c1))) &
          RT.typing (extend_env_l f g) (`()) (stt_vprop_post_equiv (elab_universe (comp_u c0))
                                                                   (elab_pure (comp_res c0))
                                                                   (elab_comp_post c0)
                                                                   (elab_comp_post c1)))
  = admit()

let mk_t_abs (f:stt_env) (g:env)
             (#u:universe)
             (#ty:pure_term)
             (#t_typing:src_typing f g ty (C_Tot (Tm_Type u)))
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
                    (mk_abs (elab_pure ty) (RT.close_term (elab_src_typing body_typing) x))
                    (elab_pure (Tm_Arrow ty (close_pure_comp c x))))
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
                   (elab_universe u) _ _
                   r_t_typing
                   r_body_typing
    
#push-options "--query_stats --fuel 2 --ifuel 2 --z3rlimit_factor 8 --print_implicits --print_full_names"
let rec soundness (f:stt_env)
                  (g:env)
                  (t:term)
                  (c:pure_comp)
                  (d:src_typing f g t c)
  : GTot (RT.typing (extend_env_l f g) (elab_src_typing d) (elab_pure_comp c))
         (decreases d)
  = let mk_t_abs (#u:universe)
                 (#ty:pure_term)
                 (t_typing:tot_typing f g ty (Tm_Type u) { t_typing << d })
                 (#body:term)
                 (#x:var { None? (lookup g x) })
                 (#c:pure_comp)
                 (body_typing:src_typing f ((x, Inl ty)::g) (open_term body x) c { body_typing << d })
      : GTot (RT.typing (extend_env_l f g)
                        (mk_abs (elab_pure ty) (RT.close_term (elab_src_typing body_typing) x))
                        (elab_pure (Tm_Arrow ty (close_pure_comp c x))))
      = let E t_typing = t_typing in
        let r_t_typing = soundness _ _ _ _ t_typing in
        let r_body_typing = soundness _ _ _ _ body_typing in
        mk_t_abs f g r_t_typing r_body_typing
    in
    match d with
    | T_Tot _ _ _ d -> d

    | T_Abs _ x ty u body c hint t_typing body_typing ->
      mk_t_abs t_typing body_typing    

    | T_STApp _ head formal res arg head_typing arg_typing ->
      let E arg_typing = arg_typing in
      let r_head = elab_src_typing head_typing in
      let r_arg = elab_pure arg in
      elab_pure_equiv arg_typing;
      let r_head_typing
        : RT.typing _ r_head (elab_pure (Tm_Arrow formal res))
        = soundness _ _ _ _ head_typing
      in
      let r_arg_typing = soundness _ _ _ _ arg_typing in
      elab_comp_open_commute res arg;
      RT.T_App _ _ _ (binder_of_t_q (elab_pure formal) R.Q_Explicit)
                     (elab_pure_comp res)
                     ((R.pack_universe R.Uv_Unk))
                     r_head_typing
                     r_arg_typing

    | T_Bind _ e1 e2 c1 c2 x c e1_typing t_typing e2_typing bc ->
      let r1_typing
        : RT.typing _ _ (elab_pure_comp c1)
        = soundness _ _ _ _ e1_typing
      in
      let r2_typing
        : RT.typing _ _ (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x)))
        = mk_t_abs t_typing e2_typing
      in
      let e = elab_src_typing d in
      let Bind_comp _ _ _ _ (E t2_typing) y (E post2_typing) = bc in
      elab_pure_equiv t2_typing;
      elab_pure_equiv post2_typing;      
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (RT.close_term (elab_src_typing post2_typing) y))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = mk_t_abs (E t2_typing) post2_typing in
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (RT.close_term (elab_pure (open_term (comp_post c2) y)) y))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      elab_close_commute' (open_term (comp_post c2) y) y 0;
      RT.close_term_spec (elab_pure (open_term (comp_post c2) y)) y;
      assert (RT.close_term (elab_pure (open_term (comp_post c2) y)) y ==
              elab_pure (close_term (open_term (comp_post c2) y) y));
      let post2_typing 
        : RT.typing _ (mk_abs (elab_pure (comp_res c2)) 
                              (elab_pure (close_term (open_term (comp_post c2) y) y)))
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      assume (~ (y `Set.mem` freevars_comp c2));
      close_open_inverse (comp_post c2) y;
      let post2_typing 
        : RT.typing _ (elab_comp_post c2)
                      (post2_type_bind (elab_pure (comp_res c2)))                              
        = post2_typing in
      let t2_typing = soundness _ _ _ _ t2_typing in
      assume (~ (x `Set.mem` freevars_comp c1));
      assume (ln_c c1 /\ ln_c c2 /\ ln_c c);
      elab_bind_typing f g _ _ _ x _ r1_typing _ r2_typing bc t2_typing post2_typing

    | T_Frame _ e c frame (E frame_typing) e_typing ->
      let r_e_typing = soundness _ _ _ _ e_typing in
      elab_pure_equiv frame_typing;
      let r_frame_typing = soundness _ _ _ _ frame_typing in
      assume (ln_c c);
      elab_frame_typing f g _ _ frame r_frame_typing r_e_typing

    | T_Equiv _ e c c' e_typing equiv ->
      admit()
      
    | _ -> admit()

let soundness_lemma
  (f:stt_env)
  (g:env)
  (t:term)
  (c:pure_comp)
  (d:src_typing f g t c)
  : Lemma (ensures RT.typing (extend_env_l f g)
                             (elab_src_typing d)
                             (elab_pure_comp c))
  = FStar.Squash.bind_squash
      #(src_typing f g t c)
      ()
      (fun dd -> FStar.Squash.return_squash (soundness f g t c d))
