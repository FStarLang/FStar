module Pulse.Soundness.VPropEquiv
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


let inst_vprop_equiv_cong #g #v0 #v1 #v0' #v1'
                         (d0:RT.typing g v0 (elab_pure Tm_VProp))
                         (d1:RT.typing g v1 (elab_pure Tm_VProp))
                         (d0':RT.typing g v0' (elab_pure Tm_VProp))
                         (d1':RT.typing g v1' (elab_pure Tm_VProp))                         
                         (#pf0:_)
                         (eq0:RT.typing g pf0 (stt_vprop_equiv v0 v0'))
                         (#pf1:_)                         
                         (eq1:RT.typing g pf1 (stt_vprop_equiv v1 v1'))
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv (mk_star v0 v1) (mk_star v0' v1')))
  = admit()


let inst_vprop_equiv_unit #g #v
                         (d:RT.typing g v (elab_pure Tm_VProp))
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv (mk_star (elab_pure Tm_Emp) v) v))
  = admit()


let inst_vprop_equiv_comm #g #v0 #v1
                         (d0:RT.typing g v0 (elab_pure Tm_VProp))
                         (d1:RT.typing g v1 (elab_pure Tm_VProp))                         
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv (mk_star v0 v1) (mk_star v1 v0)))
  = admit()


let inst_vprop_equiv_assoc #g #v0 #v1 #v2
                         (d0:RT.typing g v0 (elab_pure Tm_VProp))
                         (d1:RT.typing g v1 (elab_pure Tm_VProp))                         
                         (d2:RT.typing g v2 (elab_pure Tm_VProp))                                                  
  : GTot (pf:R.term &
          RT.typing g pf (stt_vprop_equiv (mk_star v0 (mk_star v1 v2)) (mk_star (mk_star v0 v1) v2)))
  = admit()


let rec vprop_equiv_soundness (#f:stt_env) (#g:env) (#v0 #v1:pure_term) 
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
      let (| pf, dd |) = vprop_equiv_soundness d' eq' in
      inst_vprop_equiv_sym (tot_typing_soundness d')
                           (tot_typing_soundness d)
                           dd

    | VE_Trans _ _ v _ eq_0v eq_v1 ->
      let dv = fst (vprop_equiv_typing _ _ _ _ eq_0v) d in
      let d1 = fst (vprop_equiv_typing _ _ _ _ eq_v1) dv in
      let (| pf_0v, eq_0v |) = vprop_equiv_soundness d eq_0v in
      let (| pf_v1, eq_v1 |) = vprop_equiv_soundness dv eq_v1 in
      inst_vprop_equiv_trans 
        (tot_typing_soundness d)
        (tot_typing_soundness dv)        
        (tot_typing_soundness d1)
        eq_0v
        eq_v1

    | VE_Ctxt _ t0 t1 t0' t1' eq0 eq1 ->
      let t0_typing, t1_typing = star_typing_inversion _ _ t0 t1 d  in
      let t0'_typing = fst (vprop_equiv_typing _ _ _ _ eq0) t0_typing in
      let t1'_typing = fst (vprop_equiv_typing _ _ _ _ eq1) t1_typing in      
      let (| pf0, dd0 |) = vprop_equiv_soundness t0_typing eq0 in
      let (| pf1, dd1 |) = vprop_equiv_soundness t1_typing eq1 in      
      inst_vprop_equiv_cong (tot_typing_soundness t0_typing)
                            (tot_typing_soundness t1_typing)
                            (tot_typing_soundness t0'_typing)
                            (tot_typing_soundness t1'_typing)
                            dd0 dd1

    | VE_Unit _ _v1 ->
      let v1_typing = fst (vprop_equiv_typing _ _ _ _ eq) d in
      inst_vprop_equiv_unit (tot_typing_soundness v1_typing)

    | VE_Comm _ t0 t1 ->
      let t0_typing, t1_typing = star_typing_inversion _ _ t0 t1 d  in
      inst_vprop_equiv_comm (tot_typing_soundness t0_typing)
                            (tot_typing_soundness t1_typing)

    | VE_Assoc _ t0 t1 t2 ->
      let t0_typing, t12_typing = star_typing_inversion _ _ t0 (Tm_Star t1 t2) d  in
      let t1_typing, t2_typing =  star_typing_inversion _ _ t1 t2 t12_typing in
      inst_vprop_equiv_assoc (tot_typing_soundness t0_typing)
                             (tot_typing_soundness t1_typing)
                             (tot_typing_soundness t2_typing)                             

let stt_vprop_equiv_is_prop (#g:R.env) (#v0 #v1:R.term)
                            (d0: RT.typing g v0 (elab_pure Tm_VProp))
                            (d1: RT.typing g v1 (elab_pure Tm_VProp))
   : GTot (RT.typing g (stt_vprop_equiv v0 v1) RT.tm_prop)
   = admit()
   
let vprop_equiv_unit_soundness (#f:stt_env) (#g:env) (#v0 #v1:pure_term) 
                               (d0:tot_typing f g v0 Tm_VProp)
                               (eq:vprop_equiv f g v0 v1)
  : GTot (RT.typing (extend_env_l f g) (`()) (stt_vprop_equiv (elab_pure v0) (elab_pure v1)))
  = let (| pf, s |) = vprop_equiv_soundness d0 eq in
    let d1 = fst (vprop_equiv_typing _ _ _ _ eq) d0 in
    let s_prop = stt_vprop_equiv_is_prop (tot_typing_soundness d0) (tot_typing_soundness d1) in
    RT.T_PropIrrelevance _ _ _ s s_prop
