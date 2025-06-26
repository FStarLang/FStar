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

module Pulse2Rust.Env

open FStarC
open FStarC.Util
open FStarC.List
open FStarC.Effect

open Pulse2Rust.Rust.Syntax

module S = FStarC.Extraction.ML.Syntax

module UEnv = FStarC.Extraction.ML.UEnv

val fail (s:string) : 'a

val fail_nyi (s:string) : 'a

type var = string
//
// We keep the is_mut flag in the binding in gamma
// We use it to extract !x in pulse to x in rust
//   for a mutable local x
//
type binding = var & typ & bool // name, type, is_mut
type reachable_defs = RBSet.t string

val reachable_defs_to_string (d:reachable_defs) : string

type dict = SMap.t (list string & list UEnv.mlbinding & S.mlmodulebody)

type env = {
  external_libs : list string;
  fns : list (string & fn_signature);
  statics : list (string & typ);
  gamma : list binding;
  d: dict;
  all_modules : list string;
  reachable_defs : reachable_defs;
}

val empty_env (external_libs:list string) (d:dict) (all_modules:list string) (reachable_defs:reachable_defs) : env

val lookup_global_fn (g:env) (s:string) : option fn_signature

val lookup_local (g:env) (s:string) : option (typ & bool)

val push_fn (g:env) (s:string) (t:fn_signature) : env

val push_static (g:env) (s:string) (t:typ) : env

val push_local (g:env) (s:string) (t:typ) (is_mut:bool) : env

val is_external_lib (g:env) (s:string) : bool
