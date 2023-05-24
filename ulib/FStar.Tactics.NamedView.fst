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
module FStar.Tactics.NamedView

open FStar.Reflection
open FStar.Tactics.Effect
open FStar.Tactics.Builtins

module RD = FStar.Reflection.Data

(** FIXME: needs named version. *)
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
     subpats : list (pattern * bool)
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

noeq
type named_binder = {
  ppname : ppname_t;
  uniq   : nat;
  sort   : typ;
  qual   : aqualv;
  attrs  : list term;
}

type simple_named_binder = b:named_binder{Q_Explicit? b.qual /\ Nil? b.attrs}

noeq
type named_term_view =
  | Tv_Var    : v:namedv -> named_term_view
  | Tv_BVar   : v:bv -> named_term_view
  | Tv_FVar   : v:fv -> named_term_view
  | Tv_UInst  : v:fv -> us:universes -> named_term_view
  | Tv_App    : hd:term -> a:argv -> named_term_view
  | Tv_Abs    : bv:named_binder -> body:term -> named_term_view
  | Tv_Arrow  : bv:named_binder -> c:comp -> named_term_view
  | Tv_Type   : universe -> named_term_view
  | Tv_Refine : b:simple_named_binder -> ref:term -> named_term_view
  | Tv_Const  : vconst -> named_term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> named_term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_named_binder -> def:term -> body:term -> named_term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_Unknown  : named_term_view // An underscore: _
  | Tv_Unsupp : named_term_view // failed to inspect, not supported

let binding_to_named_binder (bnd : binding) (b : binder) : named_binder =
  let bndv = inspect_binding bnd in
  {
      ppname = bndv.ppname;
      uniq   = bndv.uniq;
      sort   = bndv.sort;
      qual   = (inspect_binder b).qual;
      attrs  = (inspect_binder b).attrs;
  }

let named_binder_to_binding (b : named_binder) : binding =
  let bview : binding_view = {
      ppname = b.ppname;
      uniq   = b.uniq;
      sort   = b.sort;
  }
  in
  pack_binding bview

let open_view (tv:term_view) : Tac named_term_view =
  match tv with
  (* Nothing interesting *)
  | RD.Tv_Var v -> Tv_Var v
  | RD.Tv_BVar v -> Tv_BVar v
  | RD.Tv_FVar v -> Tv_FVar v
  | RD.Tv_UInst v us -> Tv_UInst v us
  | RD.Tv_App hd a -> Tv_App hd a
  | RD.Tv_Type u -> Tv_Type u
  | RD.Tv_Const c -> Tv_Const c
  | RD.Tv_Uvar n ctx_uvar_and_subst -> Tv_Uvar n ctx_uvar_and_subst
  | RD.Tv_AscribedT e t tac use_eq -> Tv_AscribedT e t tac use_eq
  | RD.Tv_AscribedC e c tac use_eq -> Tv_AscribedC e c tac use_eq
  | RD.Tv_Unknown -> Tv_Unknown
  | RD.Tv_Unsupp -> Tv_Unsupp

  (* Below are the nodes that actually involve a binder.
  Open them and convert to named binders. *)

  | RD.Tv_Abs b body ->
    let bnd, body = open_term b body in
    let nb = binding_to_named_binder bnd b in
    Tv_Abs nb body

  | RD.Tv_Arrow b c ->
    let bnd, body = open_comp b c in
    let nb = binding_to_named_binder bnd b in
    Tv_Arrow nb c

  | RD.Tv_Refine b ref ->
    let bnd, ref = open_term b ref in
    let nb = binding_to_named_binder bnd b in
    Tv_Refine nb ref

  | RD.Tv_Let recf attrs b def body ->
    let bnd, body = open_term b body in
    let nb = binding_to_named_binder bnd b in
    Tv_Let recf attrs nb def body

  (* FIXME *)
  | RD.Tv_Match scrutinee ret brs -> Tv_Match scrutinee ret brs

let close_view (tv : named_term_view) : term_view =
  match tv with
  (* Nothing interesting *)
  | Tv_Var v -> RD.Tv_Var v
  | Tv_BVar v -> RD.Tv_BVar v
  | Tv_FVar v -> RD.Tv_FVar v
  | Tv_UInst v us -> RD.Tv_UInst v us
  | Tv_App hd a -> RD.Tv_App hd a
  | Tv_Type u -> RD.Tv_Type u
  | Tv_Const c -> RD.Tv_Const c
  | Tv_Uvar n ctx_uvar_and_subst -> RD.Tv_Uvar n ctx_uvar_and_subst
  | Tv_AscribedT e t tac use_eq -> RD.Tv_AscribedT e t tac use_eq
  | Tv_AscribedC e c tac use_eq -> RD.Tv_AscribedC e c tac use_eq
  | Tv_Unknown -> RD.Tv_Unknown
  | Tv_Unsupp -> RD.Tv_Unsupp
  
  (* Below are the nodes that actually involve a binder.
  Open them and convert to named binders. *)
  
  | Tv_Abs nb body ->
    let bnd = named_binder_to_binding nb in
    let b, body = close_term bnd body in
    RD.Tv_Abs b body
  
  | Tv_Arrow nb c ->
    let bnd = named_binder_to_binding nb in
    let b, c = close_comp bnd c in
    RD.Tv_Arrow b c
  
  | Tv_Refine nb ref ->
    let bnd = named_binder_to_binding nb in
    let b, ref = close_term bnd ref in
    RD.Tv_Refine b ref
  
  | Tv_Let recf attrs nb def body ->
    let bnd = named_binder_to_binding nb in
    let b, body = close_term bnd body in
    RD.Tv_Let recf attrs b def body
  
  (* FIXME *)
  | Tv_Match scrutinee ret brs -> RD.Tv_Match scrutinee ret brs

let inspect (t:term) : Tac named_term_view =
  let tv = inspect_ln t in
  open_view tv

let pack (tv:named_term_view) : Tot term =
  let tv = close_view tv in
  pack_ln tv

(* Clients of this module use the named view. *)
let term_view = named_term_view