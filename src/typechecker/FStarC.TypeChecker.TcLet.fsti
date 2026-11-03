(*
   Copyright Microsoft Research

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
(* Checking a top-level [let] declaration ([Sig_let]).

   [tc_sig_let] proceeds in phases:
   1. Annotation. Each definition with a [val] declaration takes its type,
      universes and qualifiers from it; then the [preprocess_with] tactic,
      if any, runs on the definitions.
   2. Elaboration. TcTerm elaborates the definitions, as a [let] with a
      unit body, in an environment with [admit] set: it infers implicits,
      inserts coercions, runs tactics, and infers the types of unannotated
      definitions, but proves nothing.
   3. Checking. Core checks the elaboration and computes its verification
      condition, which is discharged here. Core does no inference: an
      unannotated definition is checked against its inferred type. In
      [admit] mode, only the SMT patterns are checked.
   4. Recording. The checked definitions become the [Sig_let] that is
      recorded, after the [postprocess_with] tactic, if any, runs on them.

   See doc/ref/core_typechecking.md. *)
module FStarC.TypeChecker.TcLet

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Syntax.Syntax
module Env = FStarC.TypeChecker.Env

(* Run the [postprocess_with] tactic of a [Sig_let] on its definitions (or
   [postprocess_for_extraction_with], if [for_extraction]), and on their
   types too if [postprocess_type] is also given; the attribute is removed. *)
val run_postprocess (for_extraction:bool) (env:Env.env) (se:sigelt) : ML sigelt

(* Check [se], the declaration [Sig_let {lbs; lids}] at range [r]. Returns
   the checked declaration, no new declarations, and [env]. *)
val tc_sig_let (env:Env.env) (r:Range.t) (se:sigelt) (lbs:letbindings) (lids:list lident)
  : ML (list sigelt & list sigelt & Env.env)
