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

module Pulse2Rust.Deps

open FStarC.Util
open FStarC.List
open FStarC.Effect

open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env
open Pulse2Rust.Extract

open RustBindings

module S = FStarC.Extraction.ML.Syntax


val empty_defs : reachable_defs

val singleton (p:S.mlpath) : reachable_defs

val reachable_defs_mlty (t:S.mlty) : reachable_defs

val reachable_defs_mltyscheme (ts:S.mltyscheme) : reachable_defs

val reachable_defs_mlpattern (p:S.mlpattern) : reachable_defs

val reachable_defs_expr (e:S.mlexpr) : reachable_defs

val reachable_defs_mlletbinding (lb:S.mlletbinding) : reachable_defs

val reachable_defs_mltydecl (t:S.mltydecl) : reachable_defs

val reachable_defs_mlmodule1 (m:S.mlmodule1) : reachable_defs

val reachable_defs_decls (decls:S.mlmodule) : reachable_defs

val topsort_all (d:dict) (black:list string)
  : list string

val decl_reachable (reachable_defs:reachable_defs) (mname:string) (d:S.mlmodule1) : bool