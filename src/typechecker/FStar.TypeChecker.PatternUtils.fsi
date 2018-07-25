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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module FStar.TypeChecker.PatternUtils
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Syntax.Subst
open FStar.TypeChecker.Common
open FStar.Syntax

val pat_as_exp: allow_implicits:bool
              -> env:Env.env
              -> p:pat
              -> list<bv>           (* pattern-bound variables (which may appear in the branch of match) *)
                * term              (* expressions corresponding to the pattern *)
                * guard_t           (* guard for the annotations on the pattern bound variables *)
                * pat               (* decorated pattern, with all the missing implicit args in p filled in *)