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

module FStarC.TypeChecker.Generalize

open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

val generalize:
  env ->
  bool -> (* is_rec *)
  list (lbname & term & comp) ->
  list (lbname & univ_names & term & comp & list binder)

val generalize_universes:
  env ->
  term ->
  tscheme
