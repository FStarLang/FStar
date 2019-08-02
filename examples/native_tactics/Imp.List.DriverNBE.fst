(*
   Copyright 2008-2018 Microsoft Research

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
module Imp.List.DriverNBE
open Imp.List
module R = Registers.List
module L = FStar.List.Tot

[@unfold_defs]
let long_zero x : prog =
    let l = x_times_42 x in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    // let l = l `L.append` l in
    // let l = l `L.append` l in
    // let l = l `L.append` l in
    l `L.append` 
    [Const 0 (reg 0); Const 0 (reg 1); Const 0 (reg 2)]


unfold
let normal #a (e:a) =
  FStar.Pervasives.norm 
           [zeta;
            iota;
            delta_only [`%eval; `%eval'; `%R.upd; `%R.sel; `%R.eta_map; `%L.append; `%FStar.Mul.op_Star]; 
            delta_attr [`%unfold_defs];
            primops;
            nbe
  ] e

let norm_assert (p:Type) : Lemma (requires (normal p)) (ensures True) = ()

#set-options "--debug Imp.List.DriverNBE --debug_level print_normalized_terms --admit_smt_queries true"
let _ = norm_assert (forall x y. equiv_norm (long_zero x) (long_zero y))
