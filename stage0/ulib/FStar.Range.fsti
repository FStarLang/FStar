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

open FStar.Sealed

(** [__range] is a type for the internal representations of source
   ranges. Internally, it includes a "definition" range and a "use" range, each
   of which has a filename, a start position (line+col), and an end position.

   We do not fully expose this type, but explode below allows to inspect it,
   and __mk_range to construct it.

   [range] is a sealed version of [__range], meaning it does not provide
   any facts about its values. We use this type since we have *total* functions
   inspecting terms and returning their range metadada (like the range_of constant).
   Given that range is sealed, it is sound to make range_of total.
*)

assume new type __range

type range = sealed __range

(** A dummy range constant *)
val __range_0 : __range
let range_0 : range = seal __range_0

(** Building a range constant *)
val __mk_range (file: string) (from_line from_col to_line to_col: int) : Tot __range

val mk_range (file: string) (from_line from_col to_line to_col: int) : Tot range
(* This is essentially
unfold
let mk_range (file: string) (from_line from_col to_line to_col: int) : Tot range =
     seal (__mk_range file from_line from_col to_line to_col)
but the extra indirection breaks the custom errors messages in QuickCode.
Just retaining this as a primop for now (Guido 30/Aug/2024) *)

val join_range (r1 r2 : range) : Tot range

(** [labeled] is used internally to the SMT encoding to associate a
    source-code location with an assertion. *)
irreducible
let labeled (r : range) (msg: string) (b: Type) : Type = b

val explode (r : __range) : Tot (string * int * int * int * int)
