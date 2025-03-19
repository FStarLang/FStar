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
module FStarC.Syntax.Free

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

val names            : term -> FlatSet.t bv
val names_of_binders : binders -> FlatSet.t bv

val fvars            : term -> RBSet.t Ident.lident

val uvars            : term -> FlatSet.t ctx_uvar
val uvars_uncached   : term -> FlatSet.t ctx_uvar
val uvars_full       : term -> FlatSet.t ctx_uvar

val univs            : term -> FlatSet.t universe_uvar

val univnames        : term -> FlatSet.t univ_name
val univnames_comp   : comp -> FlatSet.t univ_name

(* Bad place for these instances. But they cannot be instance
Syntax.Syntax since they reference the UF graph. *)
instance val ord_ctx_uvar  : Class.Ord.ord ctx_uvar
instance val ord_univ_uvar : Class.Ord.ord universe_uvar
