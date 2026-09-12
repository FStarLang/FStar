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

(** Layout analysis: erasure, newtype collapse and cast elimination.

    This is phase 3 (and the corresponding part of phase 4) of Custard; see
    section 5 of doc/ref/custard.md.

    The verdict types -- [slot], [ctor_layout], [newtype_layout], [layout] --
    live in {!FStarC.Custard.Syntax}, because a linked unit's verdicts come
    from its interface rather than from this pass (section 12.2). *)
module FStarC.Custard.Layout

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax

val layout_to_string : layout -> ML string

(** [run imports prog] computes the layout of every type declaration in [prog]
    and rewrites the program accordingly: erased types and their fields,
    arguments and patterns are deleted, single-field types are collapsed to
    their payload, and casts that have become identities are removed.

    [imports] carries the layout verdict of every type
    this program uses but did not compile, taken from a linked unit's
    interface (section 12.2).  Those verdicts are *pinned*: the analysis below
    reads them but never recomputes them, because the answer is a property of
    how the upstream unit was compiled, not of what this program happens to
    reach.  Uses of an imported type are still rewritten -- a constructor of a
    collapsed type collapses here too -- which is exactly why the verdicts have
    to be in the table rather than merely skipped over.

    Returns the rewritten program together with the verdict of every type
    *this* program declares, which is what a `.cui` has to record (section
    12.2): the analysis is global, so a downstream unit cannot re-derive it. *)
val run : list (dtype & type_info) -> program -> ML (program & list (name & type_info) & verdicts)
