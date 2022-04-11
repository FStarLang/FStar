(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.Syntax.Free
open FStar.Compiler.Effect
open FStar.Compiler.Effect
open Prims
open FStar open FStar.Compiler
open FStar.Compiler.Util
open FStar.Syntax
open FStar.Syntax.Syntax

val new_uv_set : unit -> uvars
val new_universe_uvar_set : unit -> set universe_uvar

val empty: set bv
val names: term -> set bv
val uvars: term -> set ctx_uvar
val univs: term -> set universe_uvar
val univnames: term -> set univ_name
val univnames_comp: comp -> set univ_name
val fvars: term -> set Ident.lident
val names_of_binders: binders -> set bv

val uvars_uncached: term -> set ctx_uvar
val uvars_full: term -> set ctx_uvar
