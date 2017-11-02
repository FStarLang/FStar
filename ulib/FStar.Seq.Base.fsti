(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(* Immutable sequences indexed by natural numbers in [0, n) *)
module FStar.Seq.Base
module List = FStar.List.Tot

/// `seq a`: The main type of this interface
///
///     - It is marked a `new` type, meaning that it that `seq a` is
///       provably distinct from other inductive and new types
///
///      For instance, you can prove the follow heterogeuous
///      inequality
///
///      let test (a:Type) (s:seq a) (l:list a) =
///          assert (~ (s === l))
new val seq (a:Type u#a) : Type u#a

////////////////////////////////////////////////////////////////////////////////
/// Sequences are isomorphic to lists, as can be seen by reveal and hide, below
///
/// However, we treat `seq a` as a distinct abstract type because
///
///    1. Its interface is geared towards reasoning about index manipulations,
///       rather than recursion and pattern-matching.
///
///    2. Being a distinct abstract type, we are free to implement it differently
///       from lists when extracting to OCaml or KreMLin.
///
///       For example, we may choose a representation that provides constant time
///       index access, rather than the linear time access that lists provide.
///
///       So far, however, sequences are just extracted to lists,
///       though that may change in the future.
////////////////////////////////////////////////////////////////////////////////

val reveal:
    #a:Type
  -> seq a
  -> GTot (list a)

val hide:
    #a:Type
  -> list a
  -> GTot (seq a)

val reveal_hide:
    #a:Type
  -> l:list a
  -> Lemma
    (ensures (reveal (hide l) == l))
    [SMTPat (hide l)]

val hide_reveal:
    #a:Type
  -> s:seq a
  -> Lemma
    (ensures (hide (reveal s) == s))
    [SMTPat (reveal s)]

/// `seq a` supports decidable equality, when `a` does.
val seq_hasEq:
    a:Type
  -> Lemma
    (requires (hasEq a))
    (ensures (hasEq (seq a)))
    [SMTPat (hasEq  (seq a))]

////////////////////////////////////////////////////////////////////////////////
/// Sequences have three eliminators:
///     -- length
///     -- index: access element and an index
///     -- equal: extensional equality
////////////////////////////////////////////////////////////////////////////////

/// length s: The length is dynamically computable
val length:
    #a:Type
  -> s:seq a
  -> Tot nat

/// index s i: Accessing the i'th element of s
val index:
    #a:Type
  -> s:seq a
  -> i:nat{i < length s}
  -> Tot a

/// s.(i) is the common way of writing index s i
unfold
let op_Array_Access #a = index #a

/// equal: Extensional equality on seq
val equal:
    #a:Type
  -> seq a
  -> seq a
  -> Type0

////////////////////////////////////////////////////////////////////////////////
/// Sequences can be introduced in several ways:
///     - Creating sequences from scratch
///              -- empty, create, init, of_list
///     - Creating sequences from other sequences
///              -- update, append, sub
////////////////////////////////////////////////////////////////////////////////

(** Creating sequences from scratch **)

/// empty: An empty sequence
val empty:
    #a:Type
  -> Tot (s:(seq a){length s=0})

[@"deprecated"]
unfold let createEmpty #a = empty #a

/// create n e: A sequence of length `n` with `e` at each index
val create:
    #a:Type
  -> size:nat
  -> element:a
  -> Tot (seq a)

/// init n f: A more general version of `create`
///           The i'th element contains `f i`
val init:
    #a:Type
  -> len:nat
  -> contents: (i:nat { i < len } -> Tot a)
  -> Tot (seq a)

/// of_list: One more constructor for sequences
///          Analogous to `init`,
///          except using a list instead of a function
val of_list:
    #a:Type
  -> list a
  -> Tot (seq a)

(** Creating sequences from other sequences **)

/// update s i a: A sequence that differs from s only at i
val update:
    #a:Type
  -> s:seq a
  -> i:nat{i < length s}
  -> a
  -> Tot (seq a)

/// s.(i) <- e : The common way of writing (update s i e)
unfold
let op_Array_Assignment #a = update #a

/// append s1 s2: The concatenation of two sequences
val append:
    #a:Type
  -> seq a
  -> seq a
  -> Tot (seq a)

/// s1 @| s2 : the common way of writing append s1 s2
unfold
let (@|) #a = append #a

/// sub s i j: the sub-sequence of s containing elements from the interval [i, j)
val sub:
    #a:Type
  -> s:seq a
  -> i:nat
  -> j:nat{i <= j && j <= length s}
  -> Tot (r:seq a)

[@"deprecated"]
unfold
let slice #a = sub #a

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about length
////////////////////////////////////////////////////////////////////////////////

val length_create:
    #a:Type
  -> n:nat
  -> i:a
  -> Lemma
    (ensures (length (create n i) = n))
    [SMTPat (length (create n i))]

val length_init:
    #a:Type
  -> n:nat
  -> contents: (i:nat { i < n } -> Tot a)
  -> Lemma
    (ensures (length (init n contents) = n))
    [SMTPat (length (init n contents))]

val length_of_list:
    #a:Type
  -> l:list a
  -> Lemma
    (ensures (length (of_list l) = List.length l))
    [SMTPat (length (of_list l))]

val length_update:
    #a:Type
  -> n:nat
  -> v:a
  -> s:seq a{n < length s}
  -> Lemma
    (ensures (length (s.(n) <- v) = length s))
    [SMTPat (length (s.(n) <- v))]

val length_append:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (ensures (length (s1 @| s2) = length s1 + length s2))
    [SMTPat (length (s1 @| s2))]

val length_sub:
    #a:Type
  -> s:seq a
  -> i:nat
  -> j:nat{i <= j && j <= length s}
  -> Lemma
    (ensures (length (sub s i j) = j - i))
    [SMTPat (length (sub s i j))]

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about index
////////////////////////////////////////////////////////////////////////////////

val index_create:
    #a:Type
  -> n:nat
  -> v:a
  -> i:nat{i < n}
  -> Lemma
    (ensures (create n v).(i) == v)
    [SMTPat  (create n v).(i)]

val index_init:
    #a:Type
  -> len:nat
  -> (contents:(i:nat { i < len } -> Tot a))
  -> i:nat{i<len}
  -> Lemma
    (ensures (init len contents).(i) == contents i)
    [SMTPat  (init len contents).(i)]

val index_of_list:
    #a:Type
  -> l:list a
  -> i:nat{i < List.length l}
  -> Lemma
    (ensures (of_list l).(i) == List.index l i)
    [SMTPat  (of_list l).(i)]

val index_update_here:
    #a:Type
  -> s:seq a
  -> i:nat{i < length s}
  -> v:a
  -> Lemma
    (ensures (s.(i) <- v).(i) == v)
    [SMTPat  (s.(i) <- v).(i)]

val index_update_there:
    #a:Type
  -> s:seq a
  -> j:nat{j < length s}
  -> v:a
  -> i:nat{i<>j /\ i < length s}
  -> Lemma
    (ensures (s.(j) <- v).(i) == s.(i))
    [SMTPat  (s.(j) <- v).(i)]

val index_append_left:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> i:nat{i < length s1}
  -> Lemma
    (ensures (s1 @| s2).(i) == s1.(i))
    [SMTPat  (s1 @| s2).(i)]

val index_append_right:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> i:nat{length s1 <= i /\ i < length s1 + length s2}
  -> Lemma
    (ensures (s1 @| s2).(i) == s2.(i - length s1))
    [SMTPat  (s1 @| s2).(i)]

val index_sub:
    #a:Type
  -> s:seq a
  -> i:nat
  -> j:nat{i <= j /\ j <= length s}
  -> k:nat{k < j - i}
  -> Lemma
    (ensures (sub s i j).(k) == s.(k + i))
    [SMTPat  (sub s i j).(k)]

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about equal
///////////////////////////////////////////////////////////////////////////////////

/// Introducing equal, by proving the sequences have equal elements, pointwise
val equal_intro:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
     (requires (length s1 = length s2 /\
               (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)}
                                          index s1 i == index s2 i)))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

/// Extensional equality on sequences coincides with `==`
val equal_elim:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
     (requires equal s1 s2)
     (ensures s1==s2)
     [SMTPat (equal s1 s2)]

/// equal is reflexive
val equal_refl:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
     (requires (s1 == s2))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]

////////////////////////////////////////////////////////////////////////////////
/// Revealing certain operations are isomorphic to their operations on lists
////////////////////////////////////////////////////////////////////////////////
val reveal_length:
    #a:Type
  -> s:seq a
  -> Lemma
    (length s == List.length (reveal s))

val reveal_index:
    #a:Type
  -> s:seq a
  -> i:nat{i<length s}
  -> Lemma
    (reveal_length s;
     s.(i) == List.index (reveal s) i)

val reveal_append:
    #a:Type
  -> s1:seq a
  -> s2:seq a
  -> Lemma
    (reveal (s1 @| s2) == reveal s1 @ reveal s2)
