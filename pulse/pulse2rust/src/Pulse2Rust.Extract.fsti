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

module Pulse2Rust.Extract

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env

module S = FStar.Extraction.ML.Syntax

val extract_mlty (g:env) (t:S.mlty) : typ

val extract_top_level_sig
  (g:env)
  (fn_const:bool)
  (fn_name:string)
  (generic_type_params:list generic_type_param)
  (arg_names:list string)
  (arg_attrs:list (list S.mlexpr))
  (arg_ts:list S.mlty)
  (ret_t:option S.mlty)
  
  : fn_signature & env

val extract_mlconstant_to_lit (c:S.mlconstant) : lit

val extract_mlpattern_to_pat (g:env) (p:S.mlpattern) : env & pat

val extract_mlexpr (g:env) (e:S.mlexpr) : expr

val extract_mlexpr_to_stmts (g:env) (e:S.mlexpr) : list stmt

val extract_top_level_lb (g:env) (lbs:S.mlletbinding) : item & env

val extract_struct_defn (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env

val extract_type_abbrev (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env

val extract_enum (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env

val extract_mltydecl (g:env) (mlattrs:list S.mlexpr) (d:S.mltydecl) : list item & env
