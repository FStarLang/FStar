(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy
*)

(* This module provides a primitive type of immutable arrays,
   implemented in OCaml by an array.

   The main intended usage of this module, as suggested by Jay Lorch,
   is to provide a sequence-like type with constant-time random access
   of elements, as opposed to FStar.Seq and related types, which
   provide only linear time access.
   
   Both the F* normalizer and NBE engine are aware of this type and
   reduce its three functions, `of_list`, `length`, and `index`, by
   invoking the corresponding operations on the underlying OCaml array
   that represents a `t`.

   See tests/micro-benchmarks/TestImmutableArray.fst for some samples
   
   And also FStar.ImmutableArray, which includes this interface and 
   augments it with various properties of the functions below.
  
*)
module FStar.ImmutableArray.Base

(* The main type of immutable arrays *)
new
val t ([@@@strictly_positive] a:Type u#a) : Type u#a

(* An array supports equality when its elements also do. *)
val array_has_eq (a : Type) : Lemma
  (requires hasEq a)
  (ensures hasEq (t a))
  [SMTPat (hasEq (t a))]

(* Creating an immutable array from a list *)
val of_list (#a:Type u#a) (l:list a) : Tot (t a)

(* The length of an array (is the length of the list from which it was created) *)
val length (#a:Type) (s:t a) : Tot nat

(* Indexing the array `s` at offset `i`, which must be within bounds *)
val index (#a:Type) (s:t a) (i:nat { i < length s }) : Tot a
