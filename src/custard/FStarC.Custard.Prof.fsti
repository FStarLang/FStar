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

(** Custard's own profiler: see doc/ref/custard.md, section 12.14.

    [FStarC.Profiling] measures a phase from the outside, which is the right
    answer for a pass that runs once.  Custard's extraction is one mutually
    recursive traversal, so its counters nest -- [ty_of_typ] is called from
    [expr_of_term] and requests a declaration whose body is extracted by
    [expr_of_term] again -- and inclusive time attributes everything to the
    outermost frame.  [Profiling]'s re-entrancy guard does not help: it drops
    the inner measurement rather than subtracting it.

    So this records *exclusive* time: the time spent in a counter minus the
    time spent in counters called from it, at any depth.  Exclusive times sum
    to the whole, which is what makes them comparable. *)
module FStarC.Custard.Prof

open FStarC
open FStarC.Effect

(** Measure [f] as [name], if profiling is on; otherwise call it.  The check
    is cached: these sit on functions called millions of times. *)
val timed : string -> (unit -> ML 'a) -> ML 'a

(** Count an event, unconditionally and cheaply. *)
val count : string -> ML unit

(** Print every counter, exclusive time descending, and clear them. *)
val report : unit -> ML unit
