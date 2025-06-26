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

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base

let canon_slprop (vp:term)
  : term
  = list_as_slprop (slprop_as_list vp)

val ve_unit_r (g:env) (p:term) : slprop_equiv g (tm_star p tm_emp) p

val list_as_slprop_append (g:env) (vp0 vp1:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1))
                        (tm_star (list_as_slprop vp0) 
                                 (list_as_slprop vp1)))

val list_as_slprop_comm (g:env) (vp0 vp1:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1))
                        (list_as_slprop (vp1 @ vp0)))

val list_as_slprop_assoc (g:env) (vp0 vp1 vp2:list term)
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ (vp1 @ vp2)))
                        (list_as_slprop ((vp0 @ vp1) @ vp2)))

val list_as_slprop_ctx (g:env) (vp0 vp0' vp1 vp1':list term)
                      (_:slprop_equiv g (list_as_slprop vp0) (list_as_slprop vp0'))
                      (_:slprop_equiv g (list_as_slprop vp1) (list_as_slprop vp1'))
  : GTot (slprop_equiv g (list_as_slprop (vp0 @ vp1)) (list_as_slprop (vp0' @ vp1')))

val list_as_slprop_singleton (g:env) (p q:term) (d:slprop_equiv g p q)
  : GTot (slprop_equiv g (list_as_slprop [p]) (list_as_slprop [q]))
  
val slprop_list_equiv (g:env)  (vp:term)
  : GTot (slprop_equiv g vp (canon_slprop vp))

val slprop_equiv_swap_equiv (g:_) (l0 l2:list term)
                           (p q:term) (d_p_q:slprop_equiv g p q)
  : GTot (slprop_equiv g (list_as_slprop ((l0 @ [q]) @ l2))
                        (list_as_slprop ([p] @ (l0 @ l2))))

val slprop_equiv_split_frame (g:_) (ctxt req:term) (frame:list term)
                            (d:slprop_equiv g (list_as_slprop (slprop_as_list req @ frame))
                                             (list_as_slprop (slprop_as_list ctxt)))
  : slprop_equiv g (tm_star req (list_as_slprop frame)) ctxt


let slprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g ctxt p)
  : tot_typing g p tm_slprop 
  = let fwd, _ = slprop_equiv_typing d in
    fwd ctxt_typing


let slprop_equiv_typing_bk (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt tm_slprop)
                           (#p:_) (d:slprop_equiv g p ctxt)
  : tot_typing g p tm_slprop 
  = let _, bk = slprop_equiv_typing d in
    bk ctxt_typing
