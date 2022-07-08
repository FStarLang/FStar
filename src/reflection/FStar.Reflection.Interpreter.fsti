(*
   Copyright 2008-2022 Microsof Research

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
module FStar.Reflection.Interpreter

open FStar.Ident
open FStar.Compiler.List
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.TypeChecker.Env
open FStar.Reflection.Basic
open FStar.Reflection.Data

module Cfg   = FStar.TypeChecker.Cfg

val reflection_primops : list Cfg.primitive_step
