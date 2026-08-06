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

(** The Custard extraction loop.

    See doc/ref/custard.md section 3.3.  This is the demand-driven worklist:
    starting from the entry points, we look each definition up, normalize it,
    translate it to the Custard IR, and request whatever it refers to.

    Scope of this milestone (M1): pure, first-order, monomorphic code.  No
    specialization happens yet, so a request is just a lid; monomorphization
    (M2) will replace [request] with an interning of specialization keys. *)
module FStarC.Custard.Extract

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

module Dep   = FStarC.Parser.Dep
module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

val state : Type0

val init : Dep.deps -> TcEnv.env -> ML state

(** The normalizer steps applied to every definition before translation.
    Section 3.3 of the design doc explains each one. *)
val custard_norm_steps : list TcEnv.step

(** Request the extraction of a top-level definition, returning the IR name it
    will be emitted under.  Idempotent. *)
val request : state -> Ident.lident -> ML name

(** Drain the worklist and return the program in dependency order (definitions
    before their uses), which is the order the backends want. *)
val run : state -> list Ident.lident -> ML program
