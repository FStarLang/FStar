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
module FStar.ImmutableArray
include FStar.ImmutableArray.Base

(* Converting an immutable array back to a list *)
val to_list (#a:Type u#a) (s:t a)
  : Tot (list a)

(* to_list is the inverse of of_list *)
val to_list_of_list (#a:Type u#a) (l:list a)
  : Lemma (to_list (of_list l) == l)
          [SMTPat (of_list l)]

(* of_list is the inverse of to_list *)
val of_list_to_list (#a:Type u#a) (s:t a)
  : Lemma (of_list (to_list s) == s)

(* The length of an immutable array is the length of its corresponding list *)
val length_spec (#a:Type u#a) (s:t a)
  : Lemma (length s == FStar.List.Tot.length (to_list s))
          [SMTPat (length s)]

(* The indexes of an immutable array are in correspondence with its underling list *)
val index_spec (#a:Type u#a) (s:t a) (i:nat{ i < length s })
  : Lemma (index s i == FStar.List.Tot.index (to_list s) i)
          [SMTPat (index s i)]

(* The list of elements precedes the array.*)
val to_list_precedes (#a:Type u#a) (s:t a)
  : Lemma (to_list s << s)

(* Idem. *)
let of_list_precedes (#a:Type u#a) (l:list a)
  : Lemma (l << of_list l)
  = to_list_precedes (of_list l)

(* An explicit proof that elements of the array precede the array. *)
let elem_precedes (#a:Type u#a) (s:t a) (i : nat{i < length s})
  : Lemma (index s i << s)
  = FStar.List.Tot.(
      to_list_precedes s;
      let l = to_list s in
      assert (memP (index l i) l);
      memP_precedes (index l i) l
    )
