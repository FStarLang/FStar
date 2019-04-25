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
module FStar.Reflection.Basic

open FStar.Order
open FStar.Reflection.Types
open FStar.Reflection.Data

(* Views  *)

(* NOTE: You probably want inspect/pack from FStar.Tactics, which work
 * over a fully named representation. If you use these, you have to
 * work with de Bruijn indices (using Tv_BVar). The only reason these
 * two exists is that they can be made Tot, and hence can be used in
 * specifications. *)
assume val inspect_ln     : (t:term) -> tv:term_view{smaller tv t}
assume val pack_ln        : term_view -> term

assume val inspect_comp   : (c:comp) -> cv:comp_view{smaller_comp cv c}
assume val pack_comp      : comp_view -> comp

assume val inspect_sigelt : sigelt -> sigelt_view
assume val pack_sigelt    : sigelt_view -> sigelt

assume val inspect_fv     : fv -> name
assume val pack_fv        : name -> fv

assume val inspect_bv     : bv -> bv_view
assume val pack_bv        : bv_view -> bv

assume val inspect_binder : binder -> bv * aqualv
assume val pack_binder    : bv -> aqualv -> binder

(* Primitives & helpers *)
assume val lookup_typ     : env -> name -> option sigelt
assume val compare_bv     : bv -> bv -> order
assume val binders_of_env : env -> binders
assume val moduleof       : env -> list string
assume val is_free        : bv -> term -> bool
assume val lookup_attr    : term -> env -> list fv
assume val term_eq        : term -> term -> bool
assume val term_to_string : term -> string

(* Attributes are terms, not to be confused with Prims.attribute *)
assume val sigelt_attrs     : sigelt -> list term
assume val set_sigelt_attrs : list term -> sigelt -> sigelt
