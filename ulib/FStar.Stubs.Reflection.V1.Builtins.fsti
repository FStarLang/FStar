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
module FStar.Stubs.Reflection.V1.Builtins

open FStar.Order
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V1.Data
open FStar.Stubs.VConfig

(*** Views ***)

(* NOTE: You probably want inspect/pack from FStar.Tactics, which work
 * over a fully named representation. If you use these, you have to
 * work with de Bruijn indices (using Tv_BVar). The only reason these
 * two exists is that they can be made Tot, and hence can be used in
 * specifications. *)

(** "Inspecting" a term: reveal one level of its syntax via the type
term_view.

Crucially, this function guarantees that the result "precedes" the
argument, since it is morally exposing the subterms of [t] in the view.
This can be justified by this model of [term] and [term_view]:

  type term = | Pack of term_view
  let pack_ln = Pack
  let inspect_ln (Pack tv) = tv

Where inspect_ln would give exactly this guarantee on its result. Of
course, the [term] type is actually implemented via internal F* terms,
but the inspect and pack should be consistent with this model.
*)

(* Views *)
val inspect_ln     : (t:term) -> tv:term_view{tv << t}
val pack_ln        : term_view -> term

val inspect_comp   : (c:comp) -> cv:comp_view{cv << c}
val pack_comp      : comp_view -> comp

val inspect_sigelt : sigelt -> sigelt_view
val pack_sigelt    : sigelt_view -> sigelt

val inspect_fv     : fv -> name
val pack_fv        : name -> fv

val inspect_bv     : v:bv -> bvv:bv_view {bvv << v}
val pack_bv        : bv_view -> bv

val inspect_lb     : lb:letbinding -> lbv:lb_view {lbv << lb}
val pack_lb        : lb_view -> letbinding

val inspect_binder : b:binder -> bv:binder_view {bv << b}
val pack_binder    : binder_view -> binder

val inspect_universe : u:universe -> uv:universe_view{uv << u}
val pack_universe    : universe_view -> universe

(* The bijection lemmas: the view exposes all details of terms. *)
val pack_inspect_inv : (t:term) -> Lemma (~(Tv_Unsupp? (inspect_ln t)) ==> pack_ln (inspect_ln t) == t)
val inspect_pack_inv : (tv:term_view) -> Lemma (inspect_ln (pack_ln tv) == tv)

val pack_inspect_comp_inv : (c:comp) -> Lemma (pack_comp (inspect_comp c) == c)
val inspect_pack_comp_inv : (cv:comp_view) -> Lemma (inspect_comp (pack_comp cv) == cv)

val inspect_pack_bv (xv:bv_view) : Lemma (inspect_bv (pack_bv xv) == xv)
val pack_inspect_bv (x:bv) : Lemma (pack_bv (inspect_bv x) == x)

val inspect_pack_binder (bview:binder_view) : Lemma (inspect_binder (pack_binder bview) == bview)
val pack_inspect_binder (b:binder) : Lemma (pack_binder (inspect_binder b) == b)

val pack_inspect_fv (fv:fv) : Lemma (ensures pack_fv (inspect_fv fv) == fv)
val inspect_pack_fv (nm:name) : Lemma (ensures inspect_fv (pack_fv nm) == nm)

val pack_inspect_universe (u:universe) : Lemma (pack_universe (inspect_universe u) == u)
val inspect_pack_universe (uv:universe_view) : Lemma (inspect_universe (pack_universe uv) == uv)

(** These are equivalent to [String.concat "."], [String.split ['.']]
 * and [String.compare]. We're only taking them as primitives to break
 * the dependency of Reflection/Tactics into * FStar.String, which
 * pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : s1:string -> s2:string -> x:int{x == 0 <==> s1 == s2}

(** Primitives & helpers *)
val lookup_typ            : env -> name -> option sigelt
val compare_bv            : bv -> bv -> order
val binders_of_env        : env -> binders
val moduleof              : env -> name
val lookup_attr           : term -> env -> list fv
val all_defs_in_env       : env -> list fv
val defs_in_module        : env -> name -> list fv
val term_eq               : term -> term -> bool
val env_open_modules      : env -> list name

(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. TODO: Should this really be push_bv? *)
val push_binder           : env -> binder -> env

(** Attributes are terms, not to be confused with Prims.attribute. *)
val sigelt_attrs     : sigelt -> list term
val set_sigelt_attrs : list term -> sigelt -> sigelt

(** Setting and reading qualifiers from sigelts *)
val sigelt_quals     : sigelt -> list qualifier
val set_sigelt_quals : list qualifier -> sigelt -> sigelt

(** Obtains the vconfig under which a particular sigelt was typechecked.
    This function returns None if "--record_options" was not on when
    typechecking the sigelt. *)
val sigelt_opts : sigelt -> option vconfig

(** Embed a vconfig as a term, for instance to use it with the check_with attribute *)
val embed_vconfig : vconfig -> term

(** Substitute an open bv (a name) by a term [t1] in a term [t2]. *)
val subst : bv -> t1:term -> t2:term -> term

(** Close an open binder in a term (i.e. turn the name into a de Bruijn index. *)
val close_term : binder -> term -> term

(** Get the range of a term, i.e., the source location where it was defined. *)
val range_of_term : term -> range

(** Get the range of a sigelt, i.e., the source location where it was defined. *)
val range_of_sigelt : sigelt -> range
