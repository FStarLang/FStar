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

module Pulse.Extract.CompilerLib

module R = FStar.Reflection.V2
module T = FStar.Tactics.V2

val uenv : Type0
val mlexpr : Type0
val e_tag : Type0
val mlty  : Type0

val mlty_unit : mlty

val mlty_param : Type0

type mlsymbol = string
type mlident  = mlsymbol
type mlpath   = list mlsymbol * mlsymbol //Path and name of a module
type mltyscheme = list mlty_param * mlty //forall a1..an. t  (the list of binders can be empty)

val mllb : Type0

val mk_ty_param (ty_param_name:mlident) (ty_param_attrs:list mlexpr) : mlty_param

val mk_mllb_with_attrs
  (mllb_name:mlident)
  (mllb_tysc:mltyscheme)
  (mllb_def:mlexpr)
  (mllb_attrs:list mlexpr) : mllb

val mk_mllb (mllb_name:mlident)
            (mllb_tysc:mltyscheme)
            (mllb_def:mlexpr) : mllb

val mk_mut_mllb (mllb_name:mlident)
                (mllb_tysc:mltyscheme)
                (mllb_def:mlexpr) : mllb

val mlletbinding : Type0
val mk_mlletbinding (is_rec:bool) (lbs:list mllb) : mlletbinding
val mle_unit : mlexpr
val mle_var (x:mlident) : mlexpr
val mle_name (x:mlpath) : mlexpr
val mle_let (x:mlletbinding) (b:mlexpr) : mlexpr
val mle_app (x:mlexpr) (args:list mlexpr) : mlexpr
val mke_tapp (x:mlexpr) (args:list mlty) : mlexpr

// formals are: formal name, type, and binder attributes
val mle_fun (formals:list (mlident * mlty * list mlexpr)) (body:mlexpr) : mlexpr

val mle_if (guard:mlexpr) (t:mlexpr) (f:option mlexpr) : mlexpr

val mlpattern : Type0
val mlconstant : Type0

val mlconstant_of_mlexpr (e:mlexpr) : Dv (option mlconstant)
val mlp_wild : mlpattern
val mlp_var (x:mlident) : mlpattern
val mlp_const (t:mlconstant) : mlpattern
val mlp_constructor (name:mlpath) (ps:list mlpattern) : mlpattern
val mlp_tuple (ps:list mlpattern) : mlpattern

val mle_match (scrut:mlexpr) (branches:list (mlpattern & mlexpr)) : mlexpr

val e_tag_pure : e_tag
val e_tag_erasable : e_tag
val e_tag_impure : e_tag

val mlty_top : mlty

val normalize_for_extraction (g:uenv) (t:T.term) : Dv T.term
val term_as_mlexpr (g:uenv) (t:T.term) : Dv (mlexpr & e_tag & mlty)
val term_as_mlty (g:uenv) (t:T.term) : Dv mlty

module PSB = Pulse.Syntax.Base
val extend_bv (g:uenv) (np:PSB.ppname) (uniq:nat) (ty:mlty) : Dv (uenv & mlident)
val initial_core_env (g:uenv) : Pulse.Typing.Env.env
val set_tcenv (g:uenv) (e:T.env) :  uenv
val mlty_to_string (t:mlty) : Dv string
val mlexpr_to_string (e:mlexpr) : Dv string
open Pulse.Syntax.Base
val sigelt_extension_data (e:T.sigelt) : option st_term

val mlmodule1 : Type0
type mlmodule = list mlmodule1

val mlm_let_with_attrs (is_rec:bool) (lbs:list mllb) (mlattrs:list mlexpr) : mlmodule1
val mlm_let (is_rec:bool) (lbs:list mllb) : mlmodule1
val is_type (g:uenv) (t:R.typ) : Dv bool
val extend_ty (g:uenv) (a:R.namedv) : Dv uenv
val lookup_ty (g:uenv) (a:R.namedv) : Dv mlident

val iface : Type0
val exp_binding : Type0
val iface_of_bindings : list (R.fv & exp_binding) -> iface
val extend_fv : uenv -> R.fv -> mltyscheme -> Dv (uenv & mlident & exp_binding)

//
// FStar.Syntax.Syntax.terms in Dv
//

val const : Type0
val fv : Type0
val term : Type0
val binder : Type0
val unit_tm : term
val unit_ty : term
val binder_qualifier : Type0
val implicit_qual : binder_qualifier
val arg_qualifier : Type0
val implicit_arg_qual : arg_qualifier
val rt_term_to_term (t:R.term) : Dv term
val mk_binder (sort:term) (ppname:string) (q:option binder_qualifier) (attrs:list term)
  : Dv binder
val mk_abs (b:binder) (body:term) : Dv term
val mk_return (t:term) : Dv term
val mk_app (head:term) (aqual:option arg_qualifier) (arg:term) : Dv term
val mk_let (b:binder) (head body:term) : Dv term
val mk_if (b then_ else_:term) : Dv term
val pattern : Type0
val mk_fv (s:list string) : Dv fv
val mk_fv_tm (fv:fv) : Dv term
val mk_pat_cons (fv:fv) (pats:list pattern) : Dv pattern
val mk_pat_constant (c:const) : Dv pattern
val mk_pat_var (ppname:string) (sort:term) : Dv pattern
val mk_dot_pat (t:option term) : Dv pattern
val mk_const (c:R.vconst) : Dv const
val branch : Type0
val mk_branch (pat:pattern) (body:term) : Dv branch
val mk_match (scrutinee:term) (brs:list branch) : Dv term
val term_to_string (t:term) : Dv string
