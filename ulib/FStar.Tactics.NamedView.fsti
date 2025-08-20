(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Tactics.NamedView

open FStar.Tactics.Effect
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
module R = FStar.Stubs.Reflection.Types
module RD = FStar.Stubs.Reflection.V2.Data
module RB = FStar.Stubs.Reflection.V2.Builtins

(* Re export the syntax types. Expose variables as their views, users do
not need to pack/inspect these if they are using the named view. *)
type namedv   = RD.namedv_view
type bv       = RD.bv_view
type comp     = RD.comp_view
type binding  = RD.binding (* already good *)
(* Terms and universes are still *deep*, so we do not change their
representation, and the user needs to pack/inspect. *)
type term     = R.term
type universe = R.universe

[@@plugin]
noeq
type binder = {
  uniq   : nat;

  ppname : ppname_t;
  sort   : R.typ;
  qual   : aqualv;
  attrs  : list term;
}
type binders = list binder

let is_simple_binder (b:binder) = Q_Explicit? b.qual /\ Nil? b.attrs
type simple_binder = b:binder{is_simple_binder b}

type univ_name = string & Range.range

[@@plugin]
noeq
type named_universe_view =
  | Uv_Zero : named_universe_view
  | Uv_Succ : universe -> named_universe_view
  | Uv_Max  : universes -> named_universe_view
  | Uv_BVar : nat -> named_universe_view
  | Uv_Name : univ_name -> named_universe_view
  | Uv_Unif : R.universe_uvar -> named_universe_view
  | Uv_Unk  : named_universe_view

[@@plugin]
noeq
type pattern =
 // A built-in constant
 | Pat_Constant {
     c : vconst
   }

 // A fully applied constructor, each boolean marks whether the
 // argument was an explicitly-provided implicit argument
 | Pat_Cons {
     head    : fv;
     univs   : option universes;
     subpats : list (pattern & bool)
   }

 // A pattern-bound *named* variable.
 | Pat_Var {
     v    : namedv;
     sort : sealed typ;
   }

 // Dot pattern: resolved by other elements in the pattern and type
 | Pat_Dot_Term {
     t : option term;
   }

type branch = pattern & term
type match_returns_ascription = binder & (either term comp & option term & bool)

[@@plugin]
noeq
type named_term_view =
  | Tv_Var    : v:namedv -> named_term_view
  | Tv_BVar   : v:bv -> named_term_view
  | Tv_FVar   : v:fv -> named_term_view
  | Tv_UInst  : v:fv -> us:universes -> named_term_view
  | Tv_App    : hd:term -> a:argv -> named_term_view
  | Tv_Abs    : b:binder -> body:term -> named_term_view
  | Tv_Arrow  : b:binder -> c:comp -> named_term_view
  | Tv_Type   : universe -> named_term_view
  | Tv_Refine : b:simple_binder -> ref:term -> named_term_view
  | Tv_Const  : vconst -> named_term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> named_term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_Unknown  : named_term_view // An underscore: _
  | Tv_Unsupp : named_term_view // failed to inspect, not supported

(* Relating constructors between old and new view. Both flavors of
functions usually behave the same wrt the top-level constructor
of the terms involved. *)
let ctor_matches (v1:named_term_view) (v2:RD.term_view) : prop =
  match v1, v2 with
  | Tv_Var _             , RD.Tv_Var _             -> True
  | Tv_BVar _            , RD.Tv_BVar _            -> True
  | Tv_FVar _            , RD.Tv_FVar _            -> True
  | Tv_UInst _ _         , RD.Tv_UInst _ _         -> True
  | Tv_App _ _           , RD.Tv_App _ _           -> True
  | Tv_Abs _ _           , RD.Tv_Abs _ _           -> True
  | Tv_Arrow _ _         , RD.Tv_Arrow _ _         -> True
  | Tv_Type _            , RD.Tv_Type _            -> True
  | Tv_Refine _ _        , RD.Tv_Refine _ _        -> True
  | Tv_Const _           , RD.Tv_Const _           -> True
  | Tv_Uvar _ _          , RD.Tv_Uvar _ _          -> True
  | Tv_Let _ _ _ _ _     , RD.Tv_Let _ _ _ _ _     -> True
  | Tv_Match _ _ _       , RD.Tv_Match _ _ _       -> True
  | Tv_AscribedT _ _ _ _ , RD.Tv_AscribedT _ _ _ _ -> True
  | Tv_AscribedC _ _ _ _ , RD.Tv_AscribedC _ _ _ _ -> True
  | Tv_Unknown           , RD.Tv_Unknown           -> True
  | Tv_Unsupp            , RD.Tv_Unsupp            -> True
  | _ -> False

// Repeat from FStar.R.Data
let notAscription (tv:named_term_view) : bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)

[@@plugin]
noeq
type letbinding = {
  lb_fv : fv;
  lb_us : list univ_name; (* opened *)
  lb_typ : typ;
  lb_def : term;
}

[@@plugin]
noeq
type named_sigelt_view =
  | Sg_Let {
      isrec : bool;
      lbs   : list letbinding;
    }

  // Sg_Inductive basically coalesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive {
      nm     : name;             // name of the inductive type being defined
      univs  : list univ_name;   // named universe variables
      params : binders;          // parameters
      typ    : typ;              // the type annotation for the inductive, i.e., indices -> Type #u
      ctors  : list ctor;        // the constructors, opened with univs and applied to params already
    }

  | Sg_Val {
      nm    : name;
      univs : list univ_name;
      typ   : typ;
    }

  | Unk

(* Some helpers. The latter two are not marked coercions as they make a
choice to not add qualifiers/attrs, so we let the user call them. *)
[@@coercion]
let binder_to_binding (b : binder) : binding =
  {
      ppname = b.ppname;
      uniq   = b.uniq;
      sort   = b.sort;
  }
let binding_to_binder (bnd : binding) : binder =
  {
      ppname = bnd.ppname;
      uniq   = bnd.uniq;
      sort   = bnd.sort;
      qual   = Q_Explicit;
      attrs  = []
  }
let namedv_to_binder (v : namedv) (sort : term) : binder =
  {
    uniq   = v.uniq;
    sort   = sort;
    ppname = v.ppname;
    qual   = Q_Explicit;
    attrs  = [];
  }

[@@plugin; coercion]
val inspect_universe (u:universe) : Tac named_universe_view

[@@plugin; coercion]
val pack_universe (uv:named_universe_view) : Tot universe

[@@plugin]
val close_term (b:binder) (t:term) : Tot (R.binder & term)

(* Note: this cannot guarantee that the returned view ctor_matches the
  original term, since we compress the term which may resolve uvar. *)
[@@plugin; coercion]
val inspect (t:term) : Tac named_term_view

[@@plugin; coercion]
val pack (tv:named_term_view) : Tot term

(* pack, however, does guarantee that. *)
val pack_ctor_matches (tv:named_term_view)
  : Lemma (ctor_matches tv (RB.inspect_ln (pack tv)))
          [SMTPat (pack tv)]

[@@plugin; coercion]
val inspect_sigelt (s : sigelt) : Tac named_sigelt_view

[@@plugin; coercion]
val pack_sigelt (sv:named_sigelt_view{~(Unk? sv)}) : Tac sigelt

(* Some primitives mention `R.comp`, wrap them to use `ThisModule.comp = R.comp_view` *)
[@@plugin]
val tcc (e:env) (t:term) : Tac comp
[@@plugin]
val comp_to_string (c:comp) : Tac string

(* Clients of this module use the named view. *)
let universe_view = named_universe_view
let term_view     = named_term_view
let sigelt_view   = named_sigelt_view

(* Temporary adapters, to avoid breaking existing code too much. *)
let inspect_namedv   = id #namedv
let pack_namedv      = id #namedv
let inspect_bv       = id #bv
let pack_bv          = id #bv
let inspect_comp     = id #comp
let pack_comp        = id #comp

[@@plugin]
val tag_of (t:term) : Tac string
