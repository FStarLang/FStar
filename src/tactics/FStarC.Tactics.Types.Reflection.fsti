(*
   Copyright 2008-2016 Microsoft Research

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
module FStarC.Tactics.Types.Reflection

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.TypeChecker.Env

(*** These are here for userspace, the library has an interface into this module. *)
val non_informative_token (g:env) (t:typ) : Type0
val subtyping_token (g:env) (t0 t1:typ) : Type0
val equiv_token (g:env) (t0 t1:typ) : Type0
val typing_token (g:env) (e:term) (c:Core.tot_or_ghost & typ) : Type0
val match_complete_token (g:env) (sc:term) (t:typ) (pats:list pattern) : Type0
