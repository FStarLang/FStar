(*
   Copyright 2008-2026 Microsoft Research

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

(** The top-level driver for Custard extraction.

    Unlike the other backends, Custard is not invoked once per module: it is
    given a set of entry points (--custard_entry) and pulls in only what they
    reach.  See doc/ref/custard.md, section 4. *)
module FStarC.Custard.Driver

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

module Dep   = FStarC.Parser.Dep
module TcEnv = FStarC.TypeChecker.Env

(** The entry points requested on the command line, resolved to lids. *)
val entrypoints : unit -> ML (list FStarC.Ident.lident)

(** Run the whole pipeline: resolve the entry points, extract, simplify and
    emit.  Called from FStarC.Universal once all input files have been
    typechecked. *)
val run : Dep.deps -> TcEnv.env -> ML unit
