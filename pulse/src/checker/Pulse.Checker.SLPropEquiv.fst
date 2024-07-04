(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.SLPropEquiv
open Pulse.Syntax
open Pulse.Typing
open FStar.List.Tot

let ve_unit_r g (p:term) : slprop_equiv g (tm_star p tm_emp) p = 
  VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)
      
let rec list_as_slprop_append g (vp0 vp1:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1))
                        (tm_star (list_as_slprop vp0) 
                                 (list_as_slprop vp1)))
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : slprop_equiv g (list_as_slprop vp1)
                            (tm_star tm_emp (list_as_slprop vp1)) = VE_Sym _ _ _ (VE_Unit _ _)
      in
      v
    | [hd] ->
      (* Need to check vp1 too in this case *)
      begin match vp1 with
      | [] ->
        VE_Sym _ _ _
          (VE_Trans _ _ _ _ (VE_Comm g hd tm_emp) (VE_Unit _ hd))
      | _::_ ->
        VE_Refl _ _
      end
    | hd::tl ->
      let tl_vp1 = list_as_slprop_append g tl vp1 in
      let d : slprop_equiv g (list_as_slprop (vp0 @ vp1))
                              (tm_star hd (tm_star (list_as_slprop tl) (list_as_slprop vp1)))
            = VE_Ctxt _ _ _ _ _ (VE_Refl _ hd) tl_vp1
      in
      let d : slprop_equiv g (list_as_slprop (vp0 @ vp1))
                              (tm_star (tm_star hd (list_as_slprop tl)) (list_as_slprop vp1))
            = VE_Trans _ _ _ _ d (VE_Assoc _ _ _ _) in
      d


let list_as_slprop_comm g (vp0 vp1:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1))
                        (list_as_slprop (vp1 @ vp0)))
  = let d1 : _ = list_as_slprop_append g vp0 vp1 in
    let d2 : _ = VE_Sym _ _ _ (list_as_slprop_append g vp1 vp0) in
    let d1 : _ = VE_Trans _ _ _ _ d1 (VE_Comm _ _ _) in
    VE_Trans _ _ _ _ d1 d2

let list_as_slprop_assoc g (vp0 vp1 vp2:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ (vp1 @ vp2)))
                        (list_as_slprop ((vp0 @ vp1) @ vp2)))
  = List.Tot.append_assoc vp0 vp1 vp2;
    VE_Refl _ _
    
let list_as_slprop_ctx g (vp0 vp0' vp1 vp1':list term)
                        (d0:slprop_equiv g (list_as_slprop vp0) (list_as_slprop vp0'))
                        (d1:slprop_equiv g (list_as_slprop vp1) (list_as_slprop vp1'))
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1)) (list_as_slprop (vp0' @ vp1')))

  = let split_app = list_as_slprop_append _ vp0 vp1 in
    let split_app' = list_as_slprop_append _ vp0' vp1' in
    let ctxt = VE_Ctxt _ _ _ _ _ d0 d1 in
    VE_Trans _ _ _ _ split_app (VE_Trans _ _ _ _ ctxt (VE_Sym _ _ _ split_app'))
  
let list_as_slprop_singleton g
  (p q:term)
  (d:slprop_equiv g p q)
  : GTot (slprop_equiv g (list_as_slprop [p]) (list_as_slprop [q]))
  = d

let rec slprop_list_equiv (g:env)
                         (vp:term)
  : GTot (slprop_equiv g vp (canon_slprop vp))
         (decreases vp)
  = match inspect_term vp with
    | Tm_Emp -> VE_Refl _ _
    | Tm_Star vp0 vp1 ->
      let eq0 = slprop_list_equiv g vp0 in
      let eq1 = slprop_list_equiv g vp1 in      
      let app_eq
        : slprop_equiv _ (canon_slprop vp) (tm_star (canon_slprop vp0) (canon_slprop vp1))
        = list_as_slprop_append g (slprop_as_list vp0) (slprop_as_list vp1)
      in
      let step
        : slprop_equiv _ vp (tm_star (canon_slprop vp0) (canon_slprop vp1))
        = VE_Ctxt _ _ _ _ _ eq0 eq1
      in
      VE_Trans _ _ _ _ step (VE_Sym _ _ _ app_eq)
      
    | _ -> VE_Refl _ _

let slprop_equiv_swap_equiv (g:_)
                          (l0 l2:list term)
                           (p q:term) (d_p_q:slprop_equiv g p q)
  : slprop_equiv g (list_as_slprop ((l0 @ [q]) @ l2))
                  (list_as_slprop ([p] @ (l0 @ l2)))
  = let d : slprop_equiv g (list_as_slprop ((l0 @ [q]) @ l2))
                          (list_as_slprop (([q] @ l0) @ l2))
        = list_as_slprop_ctx g (l0 @ [q]) ([q] @ l0) l2 l2
                            (list_as_slprop_comm g l0 [q])
                            (VE_Refl _ _) in
    let d' : slprop_equiv g (list_as_slprop (([q] @ l0) @ l2))
                            (list_as_slprop ([q] @ (l0 @ l2)))
        = List.Tot.append_assoc [q] l0 l2;
        VE_Refl _ _ in
    let d : slprop_equiv g (list_as_slprop ((l0 @ [q]) @ l2))
                            (list_as_slprop ([q] @ (l0 @ l2)))
        = VE_Trans _ _ _ _ d d' in
    let d_q_p = VE_Sym _ _ _ d_p_q in
    let d' : slprop_equiv g (list_as_slprop [q]) (list_as_slprop [p]) = d_q_p in
    let d' : slprop_equiv g (list_as_slprop ([q] @ (l0 @ l2)))
                            (list_as_slprop ([p] @ (l0 @ l2)))
        = list_as_slprop_ctx g [q] [p] (l0 @ l2) _ d' (VE_Refl _ _) in
    VE_Trans _ _ _ _ d d'


let slprop_equiv_split_frame (g:_) (ctxt req:term) (frame:list term)
                            (veq:slprop_equiv g (list_as_slprop (slprop_as_list req @ frame))
                                               (list_as_slprop (slprop_as_list ctxt)))                                             
  : slprop_equiv g (tm_star req (list_as_slprop frame)) ctxt
  = let ctxt_l = slprop_as_list ctxt in
    let req_l = slprop_as_list req in
    let veq : slprop_equiv g (list_as_slprop (req_l @ frame))
                            (list_as_slprop ctxt_l) = veq in
    let d1 
        : slprop_equiv _ (tm_star (canon_slprop req) (list_as_slprop frame))
                        (list_as_slprop (req_l @ frame))
        = VE_Sym _ _ _ (list_as_slprop_append g req_l frame)
    in
    let d1 
        : slprop_equiv _ (tm_star req (list_as_slprop frame))
                        (list_as_slprop (req_l @ frame))
        = VE_Trans _ _ _ _ (VE_Ctxt _ _ _ _ _ (slprop_list_equiv g req) (VE_Refl _ _)) d1
    in
    let d : slprop_equiv  _ (tm_star req (list_as_slprop frame))
                            (canon_slprop ctxt) =
        VE_Trans _ _ _ _ d1 veq
    in
    let d : slprop_equiv _ (tm_star req (list_as_slprop frame))
                            ctxt =
        VE_Trans _ _ _ _ d (VE_Sym _ _ _ (slprop_list_equiv g ctxt))
    in
    d
