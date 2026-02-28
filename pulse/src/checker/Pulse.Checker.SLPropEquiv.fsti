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

val ve_unit_r (g:env) (p:term) : unit

val list_as_slprop_append (g:env) (vp0 vp1:list term)
  : GTot (unit)

val list_as_slprop_comm (g:env) (vp0 vp1:list term)
  : GTot (unit)

val list_as_slprop_assoc (g:env) (vp0 vp1 vp2:list term)
  : GTot (unit)

val list_as_slprop_ctx (g:env) (vp0 vp0' vp1 vp1':list term)
  : GTot (unit)

val list_as_slprop_singleton (g:env) (p q:term)
  : GTot (unit)
  
val slprop_list_equiv (g:env)  (vp:term)
  : GTot (unit)

val slprop_equiv_swap_equiv (g:env) (l0 l2:list term)
                           (p q:term)
  : GTot (unit)

val slprop_equiv_split_frame (g:env) (ctxt req:term) (frame:list term)
  : unit


let slprop_equiv_typing_fwd (#g:env) (#ctxt:term) (ctxt_typing:unit)
                           (p:term)
  : unit 
  = let fwd, _ = slprop_equiv_typing g ctxt p in
    fwd ctxt_typing


let slprop_equiv_typing_bk (#g:env) (#ctxt:term) (ctxt_typing:unit)
                           (p:term)
  : unit 
  = let _, bk = slprop_equiv_typing g p ctxt in
    bk ctxt_typing
