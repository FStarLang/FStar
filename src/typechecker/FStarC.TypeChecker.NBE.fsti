(*
   Copyright 2017-2019 Microsoft Research

   Authors: Zoe Paraskevopoulou, Guido Martinez, Nikhil Swamy

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
module FStarC.TypeChecker.NBE
open FStar.Pervasives
open FStarC.Effect
open FStar open FStarC
open FStarC
open FStarC.TypeChecker
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Errors
open FStarC.TypeChecker.Normalize
open FStarC.TypeChecker.NBETerm
module Cfg = FStarC.TypeChecker.Cfg
module PO = FStarC.TypeChecker.Primops

val normalize_for_unit_test : steps:list Env.step
               -> env : Env.env
               -> e:term
               -> term

val normalize   : list PO.primitive_step
                -> list Env.step
                -> Env.env
                -> term
                -> term
