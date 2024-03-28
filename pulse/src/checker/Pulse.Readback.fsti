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

module Pulse.Readback
module R = FStar.Reflection.V2
module L = FStar.List.Tot
open Pulse.Syntax.Base
open Pulse.Elaborate.Pure

val readback_qual (q:R.aqualv)
  : option qualifier

let is_view_of (tv:term_view) (t:term) : prop =
  match tv with
  | Tm_Emp -> t == tm_emp
  | Tm_VProp -> t == tm_vprop
  | Tm_Inames -> t == tm_inames
  | Tm_EmpInames -> t == tm_emp_inames
  | Tm_Star t1 t2 ->
    t == tm_star t1 t2 /\
    t1 << t /\ t2 << t
  | Tm_ExistsSL u b body ->
    t == tm_exists_sl u b body /\
    u << t /\ b << t /\ body << t
  | Tm_ForallSL u b body ->
    t == tm_forall_sl u b body /\
    u << t /\ b << t /\ body << t
  | Tm_Pure p ->
    t == tm_pure p /\
    p << t
  | Tm_Inv p ->
    t == tm_inv p /\
    p << t
  | Tm_Unknown -> t == tm_unknown
  | Tm_AddInv i is -> True

val readback_ty (t:R.term)
  : (r:option term_view { Some? r ==> Some?.v r `is_view_of` t })

val readback_comp (t:R.term)
  : option (c:comp{ elab_comp c == t})
