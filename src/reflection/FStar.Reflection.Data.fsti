(*
   Copyright 2008-2022 Microsoft Research

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
module FStar.Reflection.Data

(* NOTE: This file is exactly the same as its .fs/.fsi counterpart.
It is only here so the equally-named interface file in ulib/ is not
taken by the dependency analysis to be the interface of the .fs. We also
cannot ditch the .fs, since out bootstrapping process does not extract
any .ml file from an interface. Hence we keep both, exactly equal to
each other. *)
open FStar.Compiler.List
open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Compiler.Range
module Z     = FStar.BigInt
open FStar.Ident

type name = list string
type typ  = term
type binders = list binder

type vconst =
    | C_Unit
    | C_Int of Z.t
    | C_True
    | C_False
    | C_String of string
    | C_Range of Range.range
    | C_Reify
    | C_Reflect of name

type universes = list universe

type pattern =
    | Pat_Constant of vconst
    | Pat_Cons     of fv * option (list universe) * list (pattern * bool)
    | Pat_Var      of bv
    | Pat_Wild     of bv
    | Pat_Dot_Term of option term

type branch = pattern * term

type aqualv =
    | Q_Implicit
    | Q_Explicit
    | Q_Meta of term

type argv = term * aqualv


type universe_view =
  | Uv_Zero : universe_view
  | Uv_Succ : universe -> universe_view
  | Uv_Max  : universes -> universe_view
  | Uv_BVar : Z.t -> universe_view
  | Uv_Name : (string * Range.range) -> universe_view
  | Uv_Unif : universe_uvar -> universe_view
  | Uv_Unk  : universe_view

type term_view =
    | Tv_Var       of bv
    | Tv_BVar      of bv
    | Tv_FVar      of fv
    | Tv_UInst     of fv * universes
    | Tv_App       of term * argv
    | Tv_Abs       of binder * term
    | Tv_Arrow     of binder * comp
    | Tv_Type      of universe
    | Tv_Refine    of bv * term
    | Tv_Const     of vconst
    | Tv_Uvar      of Z.t * ctx_uvar_and_subst
    | Tv_Let       of bool * list term * bv * term * term
    | Tv_Match     of term * option match_returns_ascription * list branch
    | Tv_AscribedT of term * term * option term * bool  //if the boolean flag is true, the ascription is an equality ascription
                                                         //see also Syntax
    | Tv_AscribedC of term * comp * option term * bool  //bool is similar to Tv_AscribedT
    | Tv_Unknown

(* This is a mirror of FStar.Syntax.Syntax.qualifier *)
type qualifier =
  | Assumption
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
  | Reflectable of lid
  | Discriminator of lid
  | Projector of lid * ident
  | RecordType of (list ident * list ident)
  | RecordConstructor of (list ident * list ident)
  | Action of lid
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName

type qualifiers = list qualifier

type bv_view = {
    bv_index : Z.t;
    bv_sort : typ;
}

type binder_view = bv * (aqualv * list term)

type comp_view =
    | C_Total of typ
    | C_GTotal of typ
    | C_Lemma of term * term * term
    | C_Eff of universes * name * term * list argv * list term  // list term is the decreases clause

type ctor = name * typ

type lb_view = {
    lb_fv : fv;
    lb_us : list univ_name;
    lb_typ : typ;
    lb_def : term;
}

type sigelt_view =
    | Sg_Let of bool * list letbinding
        // The bool indicates if it's a let rec
        // Non-empty list of (possibly) mutually recursive let-bindings
    | Sg_Inductive of name * list univ_name * list binder * typ * list ctor // name, params, type, constructors
    | Sg_Val of name * list univ_name * typ
    | Unk

type var = Z.t

type exp =
    | Unit
    | Var of var
    | Mult of exp * exp

(* Needed so this appears in the ocaml output for fstar-tactics-lib *)
type decls = list sigelt

