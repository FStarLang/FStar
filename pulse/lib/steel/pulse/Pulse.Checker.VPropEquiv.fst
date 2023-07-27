module Pulse.Checker.VPropEquiv
open Pulse.Syntax
open Pulse.Typing
open FStar.List.Tot

let ve_unit_r g (p:term) : vprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)
      
let rec list_as_vprop_append g (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (tm_star (list_as_vprop vp0) 
                                 (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv g (list_as_vprop vp1)
                            (tm_star tm_emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append g tl vp1 in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (tm_star hd (tm_star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) tl_vp1
      in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (tm_star (tm_star hd (list_as_vprop tl)) (list_as_vprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d


let list_as_vprop_comm g (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (list_as_vprop (vp1 @ vp0)))
  = let d1 : _ = list_as_vprop_append g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_vprop_append g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_vprop_assoc g (vp0 vp1 vp2:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                        (list_as_vprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _
    
let list_as_vprop_ctx g (vp0 vp0' vp1 vp1':list term)
                        (d0:vprop_equiv g (list_as_vprop vp0) (list_as_vprop vp0'))
                        (d1:vprop_equiv g (list_as_vprop vp1) (list_as_vprop vp1'))
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1)) (list_as_vprop (vp0' @ vp1')))

  = let split_app = list_as_vprop_append _ vp0 vp1 in
    let split_app' = list_as_vprop_append _ vp0' vp1' in
    let ctxt = VE_Ctxt _ _ _ _ _ d0 d1 in
    VE_Trans _ _ _ _ split_app (VE_Trans _ _ _ _ ctxt (VE_Sym _ _ _ split_app'))
  
let list_as_vprop_singleton g
  (p q:term)
  (d:vprop_equiv g p q)
  : GTot (vprop_equiv g (list_as_vprop [p]) (list_as_vprop [q]))
  = VE_Ctxt _ p tm_emp q tm_emp d (VE_Refl _ tm_emp)

let rec vprop_list_equiv (g:env)
                         (vp:term)
  : GTot (vprop_equiv g vp (canon_vprop vp))
         (decreases vp)
  = match vp.t with
    | Tm_Emp -> VE_Refl _ _
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv g vp0 in
      let eq1 = vprop_list_equiv g vp1 in      
      let app_eq
        : vprop_equiv _ (canon_vprop vp) (tm_star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ vp (tm_star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp tm_emp) (VE_Unit _ vp))

let vprop_equiv_swap_equiv (g:_)
                          (l0 l2:list term)
                           (p q:term) (d_p_q:vprop_equiv g p q)
  : vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                  (list_as_vprop ([p] @ (l0 @ l2)))
  = let d : vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                          (list_as_vprop (([q] @ l0) @ l2))
        = list_as_vprop_ctx g (l0 @ [q]) ([q] @ l0) l2 l2
                            (list_as_vprop_comm g l0 [q])
                            (VE_Refl _ _) in
    let d' : vprop_equiv g (list_as_vprop (([q] @ l0) @ l2))
                            (list_as_vprop ([q] @ (l0 @ l2)))
        = List.Tot.append_assoc [q] l0 l2;
        VE_Refl _ _ in
    let d : vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                            (list_as_vprop ([q] @ (l0 @ l2)))
        = VE_Trans _ _ _ _ d d' in
    let d_q_p = VE_Sym _ _ _ d_p_q in
    let d' : vprop_equiv g (list_as_vprop [q]) (list_as_vprop [p]) =
        list_as_vprop_singleton _ _ _ d_q_p in
    let d' : vprop_equiv g (list_as_vprop ([q] @ (l0 @ l2)))
                            (list_as_vprop ([p] @ (l0 @ l2)))
        = list_as_vprop_ctx g [q] [p] (l0 @ l2) _ d' (VE_Refl _ _) in
    VE_Trans _ _ _ _ d d'


let vprop_equiv_split_frame (g:_) (ctxt req:term) (frame:list term)
                            (veq:vprop_equiv g (list_as_vprop (vprop_as_list req @ frame))
                                               (list_as_vprop (vprop_as_list ctxt)))                                             
  : vprop_equiv g (tm_star req (list_as_vprop frame)) ctxt
  = let ctxt_l = vprop_as_list ctxt in
    let req_l = vprop_as_list req in
    let veq : vprop_equiv g (list_as_vprop (req_l @ frame))
                            (list_as_vprop ctxt_l) = veq in
    let d1 
        : vprop_equiv _ (tm_star (canon_vprop req) (list_as_vprop frame))
                        (list_as_vprop (req_l @ frame))
        = VE_Sym _ _ _ (list_as_vprop_append g req_l frame)
    in
    let d1 
        : vprop_equiv _ (tm_star req (list_as_vprop frame))
                        (list_as_vprop (req_l @ frame))
        = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv g req) (VE_Refl _ _)) d1
    in
    let d : vprop_equiv  _ (tm_star req (list_as_vprop frame))
                            (canon_vprop ctxt) =
        VE_Trans _ _ _ _ d1 veq
    in
    let d : vprop_equiv _ (tm_star req (list_as_vprop frame))
                            ctxt =
        VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv g ctxt))
    in
    d