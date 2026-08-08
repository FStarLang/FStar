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

(** Give every bound name its source spelling back; see section 6 of
    doc/ref/custard.md.

    Extraction names a local after the F* [bv] it came from, which means
    [ppname ^ "_" ^ index].  The index is what makes the name unique -- two
    distinct [bv]s routinely share a [ppname] -- but it is a global counter, so
    it changes whenever anything upstream of the definition changes, and the
    generated code is unreviewable and its diffs are noise.

    This pass runs last, over the final IR, and renames every binder to its
    bare [ppname], adding a numeric suffix only where that would actually
    shadow something in scope. *)
module FStarC.Custard.Rename

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

val run : program -> ML program
