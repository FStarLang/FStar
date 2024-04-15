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

(** [range] is a type for the internal representations of source
   ranges The functions that follow below allow manipulating ranges
   abstractly.  Importantly, while we allow constructing ranges, we do
   not allow destructing them, since that would reveal that
   internally, set_range_of is not an identity function.  *)
assume new type __range

type range = sealed __range

(** A dummy range constant *)
val range_0 : range

(** Building a range constant *)
val mk_range (file: string) (from_line from_col to_line to_col: int) : Tot range

(** [labeled] is used internally to the SMT encoding to associate a
    source-code location with an assertion. *)
irreducible
let labeled (r : range) (msg: string) (b: Type) : Type = b
