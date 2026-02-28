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

let ve_unit_r g (p:term) : unit = 
  ()
      
let rec list_as_slprop_append g (vp0 vp1:list term)
  : GTot (unit)
         (decreases vp0)
  = match vp0 with
    | [] -> 
      let v : unit = ()
      in
      v
    | [hd] ->
      (* Need to check vp1 too in this case *)
      begin match vp1 with
      | [] -> ()
      | _::_ -> ()
      end
    | hd::tl ->
      let tl_vp1 = list_as_slprop_append g tl vp1 in
      let d : unit
            = ()
      in
      let d : unit
            = () in
      d


let list_as_slprop_comm g (vp0 vp1:list term)
  : GTot (unit)
  = let d1 : _ = list_as_slprop_append g vp0 vp1 in
    let d2 : _ = list_as_slprop_append g vp1 vp0 in
    ()

let list_as_slprop_assoc g (vp0 vp1 vp2:list term)
  : GTot (unit)
  = List.Tot.append_assoc vp0 vp1 vp2;
    ()
    
let list_as_slprop_ctx g (vp0 vp0' vp1 vp1':list term)
                        (d0:unit)
                        (d1:unit)
  : GTot (unit)

  = let split_app = list_as_slprop_append g vp0 vp1 in
    let split_app' = list_as_slprop_append g vp0' vp1' in
    ()
  
let list_as_slprop_singleton g
  (p q:term)
  (d:unit)
  : GTot (unit)
  = d

let rec slprop_list_equiv (g:env)
                         (vp:term)
  : GTot (unit)
         (decreases vp)
  = match inspect_term vp with
    | Tm_Emp -> ()
    | Tm_Star vp0 vp1 ->
      let eq0 = slprop_list_equiv g vp0 in
      let eq1 = slprop_list_equiv g vp1 in      
      let app_eq
        : unit
        = list_as_slprop_append g (slprop_as_list vp0) (slprop_as_list vp1)
      in
      ()
      
    | _ -> ()

let slprop_equiv_swap_equiv (g:env)
                          (l0 l2:list term)
                           (p q:term) (d_p_q:unit)
  : unit
  = let d : unit
        = () in
    let d' : unit
        = List.Tot.append_assoc [q] l0 l2;
        () in
    let d : unit
        = () in
    let d_q_p = d_p_q in
    let d' : unit = d_q_p in
    let d' : unit
        = () in
    ()


let slprop_equiv_split_frame (g:env) (ctxt req:term) (frame:list term)
                            (veq:unit)                                             
  : unit
  = let ctxt_l = slprop_as_list ctxt in
    let req_l = slprop_as_list req in
    let veq : unit = veq in
    let d1 
        : unit
        = ()
    in
    let d1 
        : unit
        = ()
    in
    let d : unit =
        ()
    in
    let d : unit =
        ()
    in
    d
