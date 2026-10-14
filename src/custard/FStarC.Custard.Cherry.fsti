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

(** Cherry: reference counting for the direct-to-C backend (doc/ref/cherry.md).

    A *boxed* type is a variant that contains itself by value; its values are
    reference-counted heap cells.  A *non-plain* type is a boxed type or one
    that holds a non-plain type by value; its values own references.

    {!run} inserts the [RcInc]/[RcDec] operations, after every other pass and
    just before {!FStarC.Custard.PrintC}.  This prototype treats every
    parameter as owned and every call to a Custard definition as consuming its
    arguments; externals and primitive operations borrow theirs, except the
    runtime's own operations that say otherwise ([Prims.strcat] takes its
    first argument owned, so that it can append in place). *)
module FStarC.Custard.Cherry

open FStarC.Effect
open FStarC.Custard.Syntax

(** The keys {!nonplain_types} files [TRef (RGc, _)] and [TAny] under. *)
val ref_key : string
val any_key : string

val boxed_types : program -> ML (list string)

(** The named types ulib/c/cherry.h implements: [Prims.int], [Prims.string]
    and [FStar.ImmutableArray.Base.t]. *)
val runtime_types : list string


val nonplain_types : program -> ML (list string)

(** After [run]: for each definition, which parameters it takes owned (the
    others are borrowed; a plain parameter is listed as owned). *)
val param_owned : ref (FStarC.HashTable.t string (list bool))

val run : program -> ML program

(** After [run]: the definitions of [p], each marked with the calling
    convention [run] chose for it ([Syntax.CherryConv]), for the unit's
    interface. *)
val record_conventions : p:program -> ML program
