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

module FStarC.TypeChecker.PatternUtils
open FStarC.Effect
open FStarC
open FStarC.Util
open FStarC.Errors
open FStarC.TypeChecker
open FStarC.Syntax
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Syntax.Subst
open FStarC.TypeChecker.Common

val elaborate_pat : env -> pat -> pat
val raw_pat_as_exp (_:Env.env) (p:pat) : option (term & list bv)

val pat_as_exp:  introduce_bv_uvars:bool
               -> inst_pat_cons_univs:bool  (* whether it should instantiate the universes for data constructor patterns, on when called from Rel *)
               -> env:Env.env
               -> p:pat
               -> list bv       (* pattern-bound variables (which may appear in the branch of match) *)
                 & term         (* expressions corresponding to the pattern *)
                 & guard_t      (* guard with all implicits introduced in the pattern *)
                 & pat          (* decorated pattern, with all the missing implicit args in p filled in *)
