(*
   Copyright 2008-2025 Microsoft Research

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

(** The karamel backend: Custard's IR to karamel's, which karamel then compiles
    to C (milestone M5 of doc/ref/custard.md).

    This is a much shorter translation than the ML extraction's
    {!FStarC.Extraction.Krml}, and for a structural reason: that one has to
    recognize monomorphic uses of polymorphic definitions, undo the
    dictionary-passing the type-class elaboration introduced, and recover block
    structure from a term language that has already lost it.  By the time
    Custard gets here the program is already whole, already monomorphic, and
    already carries an effect on every node, so the work left is a change of
    representation: names to De Bruijn indices, and our nodes to theirs. *)
module FStarC.Custard.PrintKrml

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
open FStarC.Const
open FStarC.Custard.Syntax

module K    = FStarC.Extraction.KrmlAst
module Krml = FStarC.Extraction.Krml
module SMap = FStarC.SMap
module BU   = FStarC.Util

val print_program : program -> ML (list Krml.file)

(** Write [p] to [fn] in karamel's versioned binary format. *)
val write_program : string -> program -> ML unit
