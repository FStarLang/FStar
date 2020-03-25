(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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

#light "off"
module FStar.Extraction.ML.UEnv
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Ident
open FStar.Extraction.ML.Syntax
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker

// JP: my understanding of this is: we either bind a type (left injection) or a
// term variable (right injection). In the latter case, the variable may need to
// be coerced, hence the [mlexpr] (instead of the [mlident]). In order to avoid
// shadowing (which may occur, as the F* normalization potentially breaks the
// original lexical structure of the F* term), we ALSO keep the [mlsymbol], but
// only for the purpose of resolving name collisions.
// The boolean tells whether this is a recursive binding or not.
type ty_binding = {
  ty_b_name:mlident;
  ty_b_ty:mlty
}

type exp_binding = {
  exp_b_name:mlident;
  exp_b_expr:mlexpr;
  exp_b_tscheme:mltyscheme;
  exp_b_inst_ok:bool
}

type ty_or_exp_b = either<ty_binding, exp_binding>

type binding =
    | Bv  of bv * ty_or_exp_b
    | Fv  of fv * exp_binding

type tydef = {
  tydef_fv:fv;
  tydef_mlmodule_name:list<mlsymbol>;
  tydef_name:mlsymbol;
  tydef_mangled_name:option<mlsymbol>;
  tydef_def:mltyscheme
}

type uenv 

val tcenv_of_uenv : u:uenv -> TypeChecker.Env.env
val set_tcenv : u:uenv -> t:TypeChecker.Env.env -> uenv

val current_module_of_uenv : u:uenv -> mlpath
val set_current_module : u:uenv -> p:mlpath -> uenv

val bindings_of_uenv : uenv -> list<binding>

val debug: g:uenv -> f:(unit -> unit) -> unit

val mkFvvar : l:lident -> t:typ -> fv

val erasedContent:mlty

val erasableTypeNoDelta: t:mlty -> bool

val unknownType:mlty

val convIdent: id:ident -> mlident

val lookup_ty_const: env: uenv -> mlpath -> option<mltyscheme>

val maybe_mangle_type_projector: env:uenv -> fv:fv -> option<mlpath>

val try_lookup_fv: g:uenv -> fv:fv -> option<exp_binding>

val lookup_fv: g:uenv -> fv:fv -> exp_binding

val lookup_bv: g:uenv -> bv: bv -> ty_or_exp_b

val lookup_term: g:uenv -> t:term -> ty_or_exp_b * option<fv_qual>

val extend_ty: g:uenv -> a:bv -> map_to_top:bool -> uenv

val lookup_ty: g:uenv -> bv:bv -> ty_binding

val extend_bv:
    uenv ->
    bv ->
    mltyscheme ->
    add_unit: bool ->
    is_rec: bool ->
    mk_unit:
      (*some pattern terms become unit while extracting*)
      bool
  -> uenv * mlident * exp_binding

val new_mlident : g:uenv -> uenv * mlident

val extend_fv': g:uenv -> x:fv -> y:mlpath -> t_x:mltyscheme -> add_unit:bool ->
                is_rec:bool -> uenv * mlident * exp_binding

val extend_fv: g:uenv -> x:fv -> t_x:mltyscheme -> add_unit:bool ->
                is_rec:bool -> uenv * mlident * exp_binding

val extend_lb: g:uenv -> l:lbname -> t:typ -> t_x:mltyscheme -> add_unit:bool -> is_rec: bool
    -> uenv * mlident * exp_binding

val extend_tydef : g:uenv -> fv:fv -> td:one_mltydecl -> uenv * tydef
val extend_type_name: g:uenv -> fv:fv -> uenv

val is_type_name : g:uenv -> fv:fv -> bool

val is_fv_type: uenv -> fv -> bool
val emptyMlPath:mlpath
val mkContext : e:TypeChecker.Env.env -> uenv
val monad_op_name : ed:Syntax.eff_decl -> nm:string -> mlpath * lident
val action_name: ed:Syntax.eff_decl -> a:Syntax.action -> mlpath * lident

val extend_with_iface : uenv -> module_name:mlpath -> bindings:list<(fv * exp_binding)> -> tydefs:list<tydef> -> type_names:list<fv> -> uenv
