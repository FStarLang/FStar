module Pulse.Soundness.Frame
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common
(*** Soundness of frame elaboration *)

#push-options "--fuel 2 --ifuel 1"
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
                    (post_typing: RT.typing g post (mk_arrow (t, R.Q_Explicit) vprop_tm))
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
                    (f_typing:RT.typing g f (mk_stt_comp u t pre post))
  : GTot (RT.typing g (R.mk_app head [(f, R.Q_Explicit)]) (frame_res u t pre post frame))
  = admit()

(* stt t pre (fun x -> (fun x -> post) x * frame)   ~ 
   stt t pre (fun x -> post * frame) *)
let equiv_frame_post (g:R.env) 
                     (u:R.universe)
                     (t:R.term)
                     (pre:R.term) 
                     (post:term) // ln 1
                     (frame:R.term) //ln 0
  : GTot (RT.equiv g (mk_stt_comp u t pre (mk_abs t R.Q_Explicit (mk_star (R.mk_app (mk_abs t R.Q_Explicit (elab_term post))
                                                                           [bound_var 0, R.Q_Explicit]) frame)))
                     (mk_stt_comp u t pre (mk_abs t R.Q_Explicit (mk_star (elab_term post) frame))))
  = admit()

#push-options "--z3rlimit_factor 4 --ifuel 1 --fuel 4"
let elab_frame_typing (f:stt_env)
                      (g:env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:term)
                      (frame_typing: tot_typing f g frame Tm_VProp)
                      (e_typing: RT.typing (extend_env_l f g) e (elab_comp c))
  : GTot (RT.typing (extend_env_l f g) (elab_frame c frame e) (elab_comp (add_frame c frame)))
  = if C_ST? c then
    let frame_typing = tot_typing_soundness frame_typing in
    let rg = extend_env_l f g in
    let u = elab_universe (comp_u c) in
    let frame_fv = R.pack_fv (mk_steel_wrapper_lid "frame_stt") in
    let head = R.pack_ln (R.Tv_UInst frame_fv [u]) in
    assume (RT.lookup_fvar_uinst rg frame_fv [u] == Some (frame_type u));
    let head_typing : RT.typing _ _ (frame_type u) = RT.T_UInst rg frame_fv [u] in
    let (| _, c_typing |) = RT.type_correctness _ _ _ e_typing in
    let t_typing, pre_typing, post_typing = inversion_of_stt_typing _ _ _ _ c_typing in
    let t = elab_term (comp_res c) in
    let t_typing : RT.typing rg t (RT.tm_type u) = t_typing in
    let d : RT.typing (extend_env_l f g)
                      (elab_frame c frame e)
                      (frame_res u t (elab_term (comp_pre c))
                                     (elab_comp_post c)
                                     (elab_term frame)) =
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
                                                         (elab_term (Tm_Star (comp_pre c) frame))
                                                         (comp_post c)
                                                         (elab_term frame)))
    else admit ()
#pop-options

#pop-options
