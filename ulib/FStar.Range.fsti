(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Range

(** [range] is the type for the internal representation of source ranges.
   Internally, it includes a "definition" range and a "use" range, each of which
   has a filename, a start position (line+col), and an end position.

   We do not fully expose this type, but [explode] below allows inspecting it,
   and [mk_range] to construct it. This type is realized in the compiler as
   [FStarC.Range.Type.range], so that ranges are the same type everywhere.

   Note: [range] used to be a *sealed* type, which made all its values provably
   equal and hence made total range-inspecting functions (like [range_of]) sound.
   It is no longer sealed, so ranges now carry observable metadata. *)

val range : eqtype

(** A dummy range constant *)
val range_0 : range

(** Building a range constant *)
val mk_range (file: string) (from_line from_col to_line to_col: int) : Tot range
(* Retained as a primop, since the extra indirection would break the custom
error messages in QuickCode. (Guido 30/Aug/2024) *)

val join_range (r1 r2 : range) : Tot range

(** [labeled] is used internally to the SMT encoding to associate a
    source-code location with an assertion. *)
irreducible
let labeled (r : range) (msg: string) (b: prop) : prop = b

val explode (r : range) : Tot (string & int & int & int & int)
