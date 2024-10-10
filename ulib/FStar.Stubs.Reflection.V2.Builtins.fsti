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
module FStar.Stubs.Reflection.V2.Builtins

open FStar.Order
open FStar.Stubs.Syntax.Syntax
open FStar.Stubs.VConfig
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data

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
val pack_sigelt    : sv:sigelt_view{~(Unk? sv)} -> sigelt

val inspect_fv     : fv -> name
val pack_fv        : name -> fv

val inspect_namedv : v:namedv -> nv:namedv_view {nv << v}
val pack_namedv    : namedv_view -> namedv

val inspect_bv     : v:bv -> bvv:bv_view {bvv << v}
val pack_bv        : bv_view -> bv

val inspect_lb     : lb:letbinding -> lbv:lb_view {lbv << lb}
val pack_lb        : lb_view -> letbinding

val inspect_binder : b:binder -> bv:binder_view {bv << b}
val pack_binder    : binder_view -> binder

val inspect_universe : u:universe -> uv:universe_view{uv << u}
val pack_universe    : universe_view -> universe

val inspect_ident : i:ident -> iv:ident_view{iv << i}
val pack_ident    : ident_view -> ident

(* The bijection lemmas: the view exposes all details of terms. *)
val pack_inspect_inv : (t:term) -> Lemma (~(Tv_Unsupp? (inspect_ln t)) ==> pack_ln (inspect_ln t) == t)
val inspect_pack_inv : (tv:term_view) -> Lemma (inspect_ln (pack_ln tv) == tv)

val pack_inspect_comp_inv : (c:comp) -> Lemma (pack_comp (inspect_comp c) == c)
val inspect_pack_comp_inv : (cv:comp_view) -> Lemma (inspect_comp (pack_comp cv) == cv)

val inspect_pack_namedv (xv:namedv_view) : Lemma (inspect_namedv (pack_namedv xv) == xv)
val pack_inspect_namedv (x:namedv) : Lemma (pack_namedv (inspect_namedv x) == x)

val inspect_pack_bv (xv:bv_view) : Lemma (inspect_bv (pack_bv xv) == xv)
val pack_inspect_bv (x:bv) : Lemma (pack_bv (inspect_bv x) == x)

val inspect_pack_binder (bview:binder_view) : Lemma (inspect_binder (pack_binder bview) == bview)
val pack_inspect_binder (b:binder) : Lemma (pack_binder (inspect_binder b) == b)

val pack_inspect_fv (fv:fv) : Lemma (ensures pack_fv (inspect_fv fv) == fv)
val inspect_pack_fv (nm:name) : Lemma (ensures inspect_fv (pack_fv nm) == nm)

val pack_inspect_universe (u:universe) : Lemma (pack_universe (inspect_universe u) == u)
val inspect_pack_universe (uv:universe_view) : Lemma (inspect_universe (pack_universe uv) == uv)

val pack_inspect_ident (u:ident) : Lemma (pack_ident (inspect_ident u) == u)
val inspect_pack_ident (uv:ident_view) : Lemma (inspect_ident (pack_ident uv) == uv)

val pack_inspect_lb (lb:letbinding) : Lemma (pack_lb (inspect_lb lb) == lb)
val inspect_pack_lb (lbv:lb_view) : Lemma (inspect_lb (pack_lb lbv) == lbv)

val pack_inspect_sigelt (se:sigelt) : Lemma ((~(Unk? (inspect_sigelt se))) ==> pack_sigelt (inspect_sigelt se) == se)
val inspect_pack_sigelt (sev:sigelt_view { ~ (Unk? sev) }) : Lemma (inspect_sigelt (pack_sigelt sev) == sev)


val simple_binder_defn (b:binder) :
  Lemma (binder_is_simple b <==>
          Q_Explicit? (inspect_binder b).qual /\ Nil? (inspect_binder b).attrs)
        [SMTPat (binder_is_simple b)]

(** These are equivalent to [String.concat "."], [String.split ['.']]
 * and [String.compare]. We're only taking them as primitives to break
 * the dependency of Reflection/Tactics into FStar.String, which
 * pulls a LOT of modules. *)
val implode_qn     : list string -> string
val explode_qn     : string -> list string
val compare_string : s1:string -> s2:string -> x:int{x == 0 <==> s1 == s2}

(** Lookup a top-level definition in the environment (not necessarily
a type) *)
val lookup_typ            : env -> name -> option sigelt

(** Compare two bvs by their index. This should really not be a
primitive, and just use inspect to compare the index field. *)
[@@(deprecated "Use FStar.Reflection.V2.Derived.compare_bv")]
val compare_bv            : bv -> bv -> order

(** (As above.) Compare two namedv by their uniq. This should really not
be a primitive, and just use inspect to compare the uniq field. *)
[@@(deprecated "Use FStar.Reflection.V2.Derived.compare_namedv")]
val compare_namedv        : namedv -> namedv -> order

(** Returns all bindings in an environment *)
val vars_of_env           : env -> list binding

(** Returns the current module of an environment. *)
val moduleof              : env -> name

(** Returns all top-level sigelts marked with a given attribute. The
criterion used is that the [attr] attribute MUST be a top-level name
(Tv_FVar) and any sigelt that has an attribute with [attr] (possibly
applied) is returned. The sigelt can then be inspect to find the
arguments to the attribute, if needed.

Used e.g. to find all typeclass instances, and read their functional
dependencies. *)
val lookup_attr_ses       : attr:term -> env -> list sigelt

(** As [lookup_attr_ses], but just returns the name associated
to the sigelts. *)
val lookup_attr           : term -> env -> list fv

(** Returns all top-level names in an environment. *)
val all_defs_in_env       : env -> list fv

(** Returns all top-level names in a given module. *)
val defs_in_module        : env -> name -> list fv

(** Compare two terms for equality using the internal implementation.
Deprecated, we should use the userland version instead. *)
[@@(deprecated "Use FStar.Reflection.V2.TermEq.term_eq")]
val term_eq               : term -> term -> bool

(** Return all module names which are opened in the given scope. *)
val env_open_modules      : env -> list name

(** [push_binding] extends the environment with a single binding.
This is useful as one traverses the syntax of a term,
pushing bindings as one traverses (and opens) a binder in a lambda,
match, etc. *)
val push_namedv           : env -> namedv -> env

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

(** Apply a substitution on a term *)
val subst_term : subst_t -> term -> term

(** Apply a substitution on a computation. TODO: userspace? *)
val subst_comp : subst_t -> comp -> comp

(** Get the range of a term, i.e., the source location where it was defined. *)
val range_of_term : term -> range

(** Get the range of a sigelt, i.e., the source location where it was defined. *)
val range_of_sigelt : sigelt -> range
