
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
module FStarC.Extraction.ML.RegEmb

(* This module handles registering plugins and generating
embeddings for their types. *)

open FStarC
open FStarC.Effect

open FStarC.Syntax.Syntax
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.UEnv

(* When extracting a plugin, each top-level definition marked with a `@plugin` attribute
   is extracted along with an invocation to FStarC.Tactics.Native.register_tactic or register_plugin,
   which installs the compiled term as a primitive step in the normalizer
 *)
val maybe_register_plugin (g:uenv) (se:sigelt) : list mlmodule1

val interpret_plugin_as_term_fun :
              UEnv.uenv
            -> fv:fv
            -> t:typ
            -> arity:option int
            -> ml_fv:mlexpr'
            -> option (mlexpr & mlexpr & int & bool)
