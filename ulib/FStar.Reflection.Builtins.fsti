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
module FStar.Reflection.Builtins

open FStar.Order
open FStar.Reflection.Types
open FStar.Reflection.Data

(* Views  *)

(* NOTE: You probably want inspect/pack from FStar.Tactics, which work
 * over a fully named representation. If you use these, you have to
 * work with de Bruijn indices (using Tv_BVar). The only reason these
 * two exists is that they can be made Tot, and hence can be used in
 * specifications. *)
val inspect_ln     : (t:term) -> tv:term_view{smaller tv t}
val pack_ln        : term_view -> term

val pack_inspect_inv : (t:term) -> Lemma (pack_ln (inspect_ln t) == t)
val inspect_pack_inv : (tv:term_view) -> Lemma (inspect_ln (pack_ln tv) == tv)

val inspect_comp   : (c:comp) -> cv:comp_view{smaller_comp cv c}
val pack_comp      : comp_view -> comp

val inspect_sigelt : sigelt -> sigelt_view
val pack_sigelt    : sigelt_view -> sigelt

val inspect_fv     : fv -> name
val pack_fv        : name -> fv

val inspect_bv     : bv -> bv_view
val pack_bv        : bv_view -> bv

val inspect_lb     : letbinding -> lb_view
val pack_lb        : lb_view -> letbinding

val inspect_binder : binder -> bv * (aqualv * list term)
val pack_binder    : bv -> aqualv -> list term -> binder

(* These are equivalent to [String.concat "."], [String.split ['.']]
 * and [String.compare]. We're only taking them as primitives to break
 * the dependency of Reflection/Tactics into * FStar.String, which
 * pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : string -> string -> int

(* Primitives & helpers *)
val lookup_typ            : env -> name -> option sigelt
val compare_bv            : bv -> bv -> order
val binders_of_env        : env -> binders
val moduleof              : env -> name
val is_free               : bv -> term -> bool
val free_bvs              : term -> list bv
val free_uvars            : term -> list int
val lookup_attr           : term -> env -> list fv
val all_defs_in_env       : env -> list fv
val defs_in_module        : env -> name -> list fv
val term_eq               : term -> term -> bool
val term_to_string        : term -> string
val comp_to_string        : comp -> string
val env_open_modules      : env -> list name

(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. *)
val push_binder           : env -> binder -> env

(* Attributes are terms, not to be confused with Prims.attribute *)
val sigelt_attrs     : sigelt -> list term
val set_sigelt_attrs : list term -> sigelt -> sigelt

(* Setting and reading qualifiers from sigelts *)
val sigelt_quals     : sigelt -> list qualifier
val set_sigelt_quals : list qualifier -> sigelt -> sigelt

(* Reading the vconfig under which a particular sigelt was typechecked *)
val sigelt_opts : sigelt -> option vconfig

(* Embed a vconfig as a term, for instance to use it with the check_with
attribute *)
val embed_vconfig : vconfig -> term

(* Marker to check a sigelt with a particular vconfig *)
irreducible
let check_with (vcfg : vconfig) : unit = ()

val subst : bv -> term -> term -> term
