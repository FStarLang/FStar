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
module FStar.Stubs.Reflection.V2.Data

include FStar.Stubs.Syntax.Syntax
open FStar.Stubs.Reflection.Types

(* The type of a string observable only with a tactic.
   All values of type ppname_t are provably equal *)
let ppname_t = FStar.Sealed.Inhabited.sealed ""
let as_ppname (x:string) : ppname_t = FStar.Sealed.Inhabited.seal x

noeq
type vconst =
  | C_Unit      : vconst
  | C_Int       : int -> vconst // Not exposing the full details of our integer repr.
  | C_True      : vconst
  | C_False     : vconst
  | C_String    : string -> vconst
  | C_Range     : range -> vconst
  | C_Reify     : vconst
  | C_Reflect   : name -> vconst
  | C_Real      : string -> vconst (* Real literals are represented as a string e.g. "1.2" *)
  (* TODO: complete *)

type universes = list universe

type ident_view = string & range

noeq
type pattern =
 // A built-in constant
 | Pat_Constant :
     c : vconst ->
     pattern

 // A fully applied constructor, each boolean marks whether the
 // argument was an explicitly-provided implicit argument
 | Pat_Cons :
     head    : fv ->
     univs   : option universes ->
     subpats : list (pattern & bool) ->
     pattern

 // A pattern-bound variable. It has a sealed sort in it.
 // This sort is ignored by the typechecker, but may be useful
 // for metaprogram to look at heuristically. There is nothing
 // else here but a ppname, the variable is referred to by its DB index.
 // This means all Pat_Var are provably equal.
 | Pat_Var :
     sort   : sealed term ->
     ppname : ppname_t ->
     pattern

 // Dot pattern: resolved by other elements in the pattern and type
 | Pat_Dot_Term :
     t : option term ->
     pattern

type branch = pattern & term  // | pattern -> term

noeq
type aqualv =
  | Q_Implicit
  | Q_Explicit
  | Q_Equality
  | Q_Meta of term

type argv = term & aqualv

(* A named variable, with a unique identifier *)
noeq
type namedv_view = {
  uniq   : nat;
  sort   : sealed typ; // REMOVE?
  ppname : ppname_t;
}

(* A bound variable, with a de Bruijn index *)
noeq
type bv_view = {
  index  : nat;
  sort   : sealed typ; // REMOVE?
  ppname : ppname_t;
}

(* Binders consist of a type, qualifiers, and attributes. There is also
a sealed name. *)
noeq
type binder_view = {
  sort   : typ;
  qual   : aqualv;
  attrs  : list term;
  ppname : ppname_t;
}

(* A binding is a variable in the environment. It is like a namedv, but has
an explicit (unsealed) sort *)
noeq
type binding = {
  uniq   : nat;
  sort   : typ;
  ppname : ppname_t;
}
type bindings = list binding

(** We use the binder type for letbindings and refinements,
but no qualifiers nor attributes can appear there. We call these
binders simple. This module assumes an abstract predicate
for them, which is later assumed to be equivalent to being a binder
without qualifiers nor attributes (once inspect_binder is in scope). *)
val binder_is_simple : binder -> Tot bool

type simple_binder = b:binder{binder_is_simple b}

noeq
type universe_view =
  | Uv_Zero : universe_view
  | Uv_Succ : universe -> universe_view
  | Uv_Max  : universes -> universe_view
  | Uv_BVar : nat -> universe_view
  | Uv_Name : univ_name -> universe_view
  | Uv_Unif : universe_uvar -> universe_view
  | Uv_Unk  : universe_view

noeq
type term_view =
  | Tv_Var    : v:namedv -> term_view
  | Tv_BVar   : v:bv -> term_view
  | Tv_FVar   : v:fv -> term_view
  | Tv_UInst  : v:fv -> us:universes -> term_view
  | Tv_App    : hd:term -> a:argv -> term_view
  | Tv_Abs    : bv:binder -> body:term -> term_view
  | Tv_Arrow  : bv:binder -> c:comp -> term_view
  | Tv_Type   : universe -> term_view
  | Tv_Refine : b:simple_binder -> ref:term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> term_view
  | Tv_Unknown  : term_view // An underscore: _
  | Tv_Unsupp : term_view // failed to inspect, not supported

let notAscription (tv:term_view) : bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)

// Very basic for now
noeq
type comp_view =
  | C_Total     : ret:typ -> comp_view
  | C_GTotal    : ret:typ -> comp_view
  | C_Lemma     : term -> term -> term -> comp_view // pre, post, patterns
  | C_Eff       : us:universes ->
                  eff_name:name ->
                  result:term ->
                  eff_args:(list argv) ->
                  decrs:list term ->
                  comp_view

(* Constructor for an inductive type. See explanation in
[Sg_Inductive] below. *)
type ctor = name & typ

noeq
type lb_view = {
    lb_fv : fv;
    lb_us : list univ_name;
    lb_typ : typ;
    lb_def : term
}

noeq
type sigelt_view =
  | Sg_Let :
      (r:bool) ->
      (lbs:list letbinding) ->
      sigelt_view

  // Sg_Inductive basically coalesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (nm:name) ->              // name of the inductive type being defined
      (univs:list univ_name) -> // universe variables
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      (cts:list ctor) ->        // the constructors, opened with univs and applied to params already
      sigelt_view

  | Sg_Val :
      (nm:name) ->
      (univs:list univ_name) ->
      (typ:typ) ->
      sigelt_view

  | Unk

(* Qualifiers for sigelts, see src/FStar.Syntax.Syntax for an explanation. *)
noeq
type qualifier =
  | Assumption
  | InternalAssumption
  | New
  | Private
  | Unfold_for_unification_and_vcgen
  | Visible_default
  | Irreducible
  | Inline_for_extraction
  | NoExtract
  | Noeq
  | Unopteq
  | TotalEffect
  | Logic
  | Reifiable
  | Reflectable       of name
  | Discriminator     of name
  | Projector         of name & ident
  | RecordType        of list ident & list ident
  | RecordConstructor of list ident & list ident
  | Action            of name
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName

(* Should remove, but there are clients using it. *)
let var : eqtype = nat
