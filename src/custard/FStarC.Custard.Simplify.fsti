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

(** Effect-guarded simplification; see sections 6 and 7.3 of
    doc/ref/custard.md.

    Everything here is an instance of the same discipline: a subterm may only
    be dropped when its effect is [E_Pure] or [E_Ghost], and an impure one is
    kept in place (as a statement) instead. *)
module FStarC.Custard.Simplify

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

(** Drop unused pure let-bindings, turn unused impure ones into sequencing,
    and contract [let x = e in x] to [e]. *)
val run : program -> ML program
