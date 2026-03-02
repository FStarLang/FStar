(*
   Copyright 2008-2020 Microsoft Research

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

module FStarC.Extraction.ML.UEnv
open FStarC
open FStarC.Class.Show
open FStarC.Effect
open FStarC.Ident
open FStarC.Extraction.ML.Syntax
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker

(** This module provides a typing environment used for extracting
    programs to ML.
    
    See the implementation for more detailed descriptions. *)


(**** Types *)

type ty_binding = {
  ty_b_name:mlident;
  ty_b_ty:mlty
}

type exp_binding = {
  exp_b_name:mlident;
  exp_b_expr:mlexpr;
  exp_b_tscheme:mltyscheme;
  exp_b_eff: e_tag
}

type ty_or_exp_b = either ty_binding exp_binding

type mlbinding =
  | Bv  of bv & ty_or_exp_b
  | Fv  of fv & exp_binding
  | ErasedFv of fv

instance val showable_mlbinding : showable mlbinding

(** Type abbreviations, aka definitions *)
val tydef : Type0
val tydef_fv : tydef -> fv
val tydef_meta : tydef -> FStarC.Extraction.ML.Syntax.metadata
val tydef_def: tydef -> mltyscheme
val tydef_mlpath : tydef -> mlpath

(** The main type of this module *)
val uenv : Type0
val with_restored_tc_scope (env:uenv) (f:uenv -> ML ('a & uenv)) : ML ('a & uenv)
instance val showable_uenv: showable uenv
val tcenv_of_uenv : u:uenv -> TypeChecker.Env.env
val set_tcenv : u:uenv -> t:TypeChecker.Env.env -> uenv
val current_module_of_uenv : u:uenv -> mlpath
val set_current_module : u:uenv -> p:mlpath -> uenv
val with_typars_env : uenv -> (RemoveUnusedParameters.env_t -> ML (RemoveUnusedParameters.env_t & 'a)) -> ML (uenv & 'a)

(** Debugging only *)
val bindings_of_uenv : uenv -> list mlbinding
val debug: g:uenv -> f:(unit -> ML unit) -> ML unit

(*** Looking up identifiers *)

(** Lookup a top-level term identifier. Raises an error/warning when the
FV has been erased, using the given range. *)
val try_lookup_fv: Range.t -> g:uenv -> fv:fv -> ML (option exp_binding)

(* As above, but will abort if the variable is not found or was erased.
Only use this for variables that must be in the environment, such as
definitions in Prims. *)
val lookup_fv: Range.t -> g:uenv -> fv:fv -> ML exp_binding

(** Lookup a local term or type variable *)
val lookup_bv: g:uenv -> bv: bv -> ML ty_or_exp_b

(** Lookup a top-level term or local type variable *)
val lookup_term: g:uenv -> t:term -> ML (ty_or_exp_b & option fv_qual)

(** Lookup a type variable *)
val lookup_ty: g:uenv -> bv:bv -> ML ty_binding

(** Lookup a type definition *)
val lookup_tydef : uenv -> mlpath -> ML (option mltyscheme)

(** Does a type definition have an accompanying `val` declaration? *)
val has_tydef_declaration : uenv -> lident -> bool

(** ML qualified name corresponding to an F* qualified name *)
val mlpath_of_lident : uenv -> lident -> ML mlpath

(** Does the fv bind an F* inductive type? *)
val is_type_name : g:uenv -> fv:fv -> ML bool

(** Does the fv bind an F* inductive type or abbreviation? *)
val is_fv_type: uenv -> fv -> ML bool

val no_fstar_stubs_ns : list mlsymbol -> ML (list mlsymbol)
val no_fstar_stubs : mlpath -> ML mlpath

(** ML record name for an F* pair of type name and field name *)
val lookup_record_field_name: uenv -> (lident & ident) -> ML mlpath

(*** Extending environment *)

(** Extend with a type variable, potentially erased to MLTY_Top *)
val extend_ty: g:uenv -> a:bv -> map_to_top:bool -> ML uenv

(** Extend with a local term variable, maybe thunked, maybe erased *)
val extend_bv:
    uenv ->
    bv ->
    mltyscheme ->
    add_unit: bool ->
    mk_unit: bool ->
    ML (uenv & mlident & exp_binding)

(** Make sure a given ML name is not used in an environment. The
scope of the environment is not changed at all. This can be used to
generate less confusing names, for instance, in `let x = E in F`, we can
burn `x` in `E` to avoid generating code like `let x = let x = 1 in x in
x`, which does not have any shadowing, but is hard to read. Of course,
`x` is burnt in `F` since it is in-scope there. *)
val burn_name:
    uenv ->
    mlident ->
    uenv

(** Fresh local identifer *)
val new_mlident : g:uenv -> ML (uenv & mlident)

(** Extend with an top-level term identifier, maybe thunked *)
val extend_fv: 
    uenv ->
    fv ->
    mltyscheme ->
    add_unit:bool ->
    ML (uenv & mlident & exp_binding)

(** Extend the fv environment by marking that a variable was erased. *)
val extend_erased_fv:
    uenv ->
    fv ->
    uenv

(** Extend with a local or top-level let binding, maybe thunked *)
val extend_lb: 
    uenv ->
    l:lbname ->
    t:typ ->
    t_x:mltyscheme ->
    add_unit:bool ->
    ML (uenv & mlident & exp_binding)

(** Extend with a type abbreviation *)
val extend_tydef:
    uenv ->
    fv ->
    mltyscheme ->
    FStarC.Extraction.ML.Syntax.metadata ->
    ML (tydef & mlpath & uenv)

(** This identifier is for the declaration of a type `val t _ : Type` 
    We record it in the environment to control later if we are
    allows to remove unused type parameters in the definition of `t`. **)
val extend_with_tydef_declaration:
    uenv ->
    lident -> 
    uenv

(** Extend with an inductive type *)
val extend_type_name: 
    uenv ->
    fv ->
    ML (mlpath & uenv)

(** Extend with a [bind] or [return], 
      returns both the ML identifier and the generated F* lid for it *)
val extend_with_monad_op_name:
    uenv ->
    Syntax.eff_decl ->
    string -> (* name of the op *)
    mltyscheme ->
    ML (mlpath & lident & exp_binding & uenv)

(** Extend with an action, returns both the ML identifer and generated F* lident *)
val extend_with_action_name:
    uenv ->
    Syntax.eff_decl ->
    Syntax.action ->
    mltyscheme -> 
    ML (mlpath & lident & exp_binding & uenv)

(** The F* record field identifier is a pair of the *typename* and the field name *)
val extend_record_field_name :
    uenv ->
    (lident & ident) ->
    ML (mlident & uenv)
    
(** ML module identifier for an F* module name *)
val extend_with_module_name : 
    uenv -> 
    lident ->
    ML (mlpath & uenv)

(** Mark exiting a module scope *)
val exit_module : uenv -> ML uenv

(** Constructor *)
val new_uenv : e:TypeChecker.Env.env -> ML uenv
