module Pulse.Checker.VPropEquiv
open Pulse.Syntax
open Pulse.Typing
open FStar.List.Tot


let rec vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 Tm_VProp -> tot_typing g t1 Tm_VProp) &
          (tot_typing g t1 Tm_VProp -> tot_typing g t0 Tm_VProp))
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
      let ff (x:tot_typing g (Tm_Star s0 s1) Tm_VProp)
        : tot_typing g (Tm_Star s0' s1') Tm_VProp
        = let s0_typing = star_typing_inversion_l x in
          let s1_typing = star_typing_inversion_r x in
          let s0'_typing, s1'_typing = f0 s0_typing, f1 s1_typing in
          star_typing s0'_typing s1'_typing
      in
      let gg (x:tot_typing g (Tm_Star s0' s1') Tm_VProp)
        : tot_typing g (Tm_Star s0 s1) Tm_VProp
        = let s0'_typing = star_typing_inversion_l x in
          let s1'_typing = star_typing_inversion_r x in
          star_typing (f0' s0'_typing) (f1' s1'_typing)        
      in
      ff, gg

    | VE_Unit g t ->
      let fwd (x:tot_typing g (Tm_Star Tm_Emp t) Tm_VProp)
        : tot_typing g t Tm_VProp
        = let r = star_typing_inversion_r x in
          r
      in
      let bk (x:tot_typing g t Tm_VProp)
        : tot_typing g (Tm_Star Tm_Emp t) Tm_VProp
        = star_typing emp_typing x
      in
      fwd, bk

    | VE_Comm g t0 t1 ->
      let f t0 t1 (x:tot_typing g (Tm_Star t0 t1) Tm_VProp)
        : tot_typing g (Tm_Star t1 t0) Tm_VProp
        = let tt0 = star_typing_inversion_l x in
          let tt1 = star_typing_inversion_r x in
          star_typing tt1 tt0
      in
      f t0 t1, f t1 t0

    | VE_Assoc g t0 t1 t2 ->
      let fwd (x:tot_typing g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp)
        : tot_typing g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp
        = let tt0 = star_typing_inversion_l x in
          let tt12 = star_typing_inversion_r x in
          let tt1 = star_typing_inversion_l tt12 in
          let tt2 = star_typing_inversion_r tt12 in
          star_typing (star_typing tt0 tt1) tt2
      in
      let bk (x : tot_typing g (Tm_Star (Tm_Star t0 t1) t2) Tm_VProp)
        : tot_typing g (Tm_Star t0 (Tm_Star t1 t2)) Tm_VProp
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


let rec vprop_as_list (vp:term)
  : list term
  = match vp with
    | Tm_Emp -> []
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list term)
  : term
  = match vps with
    | [] -> Tm_Emp
    | hd::tl -> Tm_Star hd (list_as_vprop tl)


let ve_unit_r g (p:term) : vprop_equiv g (Tm_Star p Tm_Emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)
      
let rec list_as_vprop_append g (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (Tm_Star (list_as_vprop vp0) 
                                 (list_as_vprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : vprop_equiv g (list_as_vprop vp1)
                            (Tm_Star Tm_Emp (list_as_vprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | hd::tl ->
      let tl_vp1 = list_as_vprop_append g tl vp1 in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star hd (Tm_Star (list_as_vprop tl) (list_as_vprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) tl_vp1
      in
      let d : vprop_equiv g (list_as_vprop (vp0 @ vp1))
                              (Tm_Star (Tm_Star hd (list_as_vprop tl)) (list_as_vprop vp1))
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
  = VE_Ctxt _ p Tm_Emp q Tm_Emp d (VE_Refl _ Tm_Emp)

let rec vprop_list_equiv (g:env)
                         (vp:term)
  : GTot (vprop_equiv g vp (canon_vprop vp))
         (decreases vp)
  = match vp with
    | Tm_Emp -> VE_Refl _ _
    | Tm_Star vp0 vp1 ->
      let eq0 = vprop_list_equiv g vp0 in
      let eq1 = vprop_list_equiv g vp1 in      
      let app_eq
        : vprop_equiv _ (canon_vprop vp) (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = list_as_vprop_append g (vprop_as_list vp0) (vprop_as_list vp1)
      in
      let step
        : vprop_equiv _ vp (Tm_Star (canon_vprop vp0) (canon_vprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> 
      VE_Sym _ _ _
        (VE_Trans _ _ _ _ (VE_Comm g vp Tm_Emp) (VE_Unit _ vp))

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
  : vprop_equiv g (Tm_Star req (list_as_vprop frame)) ctxt
  = let ctxt_l = vprop_as_list ctxt in
    let req_l = vprop_as_list req in
    let veq : vprop_equiv g (list_as_vprop (req_l @ frame))
                            (list_as_vprop ctxt_l) = veq in
    let d1 
        : vprop_equiv _ (Tm_Star (canon_vprop req) (list_as_vprop frame))
                        (list_as_vprop (req_l @ frame))
        = VE_Sym _ _ _ (list_as_vprop_append g req_l frame)
    in
    let d1 
        : vprop_equiv _ (Tm_Star req (list_as_vprop frame))
                        (list_as_vprop (req_l @ frame))
        = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (vprop_list_equiv g req) (VE_Refl _ _)) d1
    in
    let d : vprop_equiv  _ (Tm_Star req (list_as_vprop frame))
                            (canon_vprop ctxt) =
        VE_Trans _ _ _ _ d1 veq
    in
    let d : vprop_equiv _ (Tm_Star req (list_as_vprop frame))
                            ctxt =
        VE_Trans _ _ _ _ d (VE_Sym _ _ _ (vprop_list_equiv g ctxt))
    in
    d