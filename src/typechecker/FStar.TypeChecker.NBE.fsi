(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.TypeChecker.NBE
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.TypeChecker.Normalize
open FStar.TypeChecker.NBETerm
module Cfg = FStar.TypeChecker.Cfg

val iapp : Cfg.cfg -> t -> args -> t

val normalize_for_unit_test : steps:list<Env.step>
               -> env : Env.env
               -> e:term
               -> term

val normalize   : list<Cfg.primitive_step>
                -> list<Env.step>
                -> Env.env
                -> term
                -> term
