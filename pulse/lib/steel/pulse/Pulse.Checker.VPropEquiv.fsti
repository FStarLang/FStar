module Pulse.Checker.VPropEquiv
open Pulse.Syntax
open Pulse.Typing
open FStar.List.Tot

val vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_vprop -> tot_typing g t1 tm_vprop) &
          (tot_typing g t1 tm_vprop -> tot_typing g t0 tm_vprop))

val vprop_as_list (vp:term)
  : list term

val list_as_vprop (vps:list term)
  : term

let canon_vprop (vp:term)
  : term
  = list_as_vprop (vprop_as_list vp)


val ve_unit_r (g:env) (p:term) : vprop_equiv g (tm_star p tm_emp) p

val list_as_vprop_append (g:env) (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (tm_star (list_as_vprop vp0) 
                                 (list_as_vprop vp1)))

val list_as_vprop_comm (g:env) (vp0 vp1:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1))
                        (list_as_vprop (vp1 @ vp0)))

val list_as_vprop_assoc (g:env) (vp0 vp1 vp2:list term)
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ (vp1 @ vp2)))
                        (list_as_vprop ((vp0 @ vp1) @ vp2)))

val list_as_vprop_ctx (g:env) (vp0 vp0' vp1 vp1':list term)
                      (_:vprop_equiv g (list_as_vprop vp0) (list_as_vprop vp0'))
                      (_:vprop_equiv g (list_as_vprop vp1) (list_as_vprop vp1'))
  : GTot (vprop_equiv g (list_as_vprop (vp0 @ vp1)) (list_as_vprop (vp0' @ vp1')))

val list_as_vprop_singleton (g:env) (p q:term) (d:vprop_equiv g p q)
  : GTot (vprop_equiv g (list_as_vprop [p]) (list_as_vprop [q]))
  
val vprop_list_equiv (g:env)  (vp:term)
  : GTot (vprop_equiv g vp (canon_vprop vp))

val vprop_equiv_swap_equiv (g:_) (l0 l2:list term)
                           (p q:term) (d_p_q:vprop_equiv g p q)
  : GTot (vprop_equiv g (list_as_vprop ((l0 @ [q]) @ l2))
                        (list_as_vprop ([p] @ (l0 @ l2))))

val vprop_equiv_split_frame (g:_) (ctxt req:term) (frame:list term)
                            (d:vprop_equiv g (list_as_vprop (vprop_as_list req @ frame))
                                             (list_as_vprop (vprop_as_list ctxt)))
  : vprop_equiv g (tm_star req (list_as_vprop frame)) ctxt


let vprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g ctxt p)
  : tot_typing g p tm_vprop 
  = let fwd, _ = vprop_equiv_typing d in
    fwd ctxt_typing


let vprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_vprop)
                           (#p:_) (d:vprop_equiv g p ctxt)
  : tot_typing g p tm_vprop 
  = let _, bk = vprop_equiv_typing d in
    bk ctxt_typing
