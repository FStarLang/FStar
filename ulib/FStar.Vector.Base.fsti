 (*
      Copyright 2008-2017 Microsoft Research

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

(*

   A library for vectors, i.e., immutable arrays, whose length is
   representable by a machine integer, FStar.UInt32.t.

   This is closely related to FStar.Seq, with the following main
   differences:

     1. The length of a vector is representable in a U32.t

     2. Vectors receive special treatment during extraction, especially
        by KreMLin, which extracts a vector to a raw C pointer.

     3. The interface is designed around a length-indexed type: this
        enables the compilation to raw pointers (point 2, above), since
        this ensures that all functions that manipulate vectors always
        have a U32 variable describing that vector's length in scope.

        A length-indexed interface is also suitable for clients for whom
        proving properties about the length is a primary concern: the
        signatures in this interface carry intrinsic proofs about length
        properties, simplifying proof obligations in client code.

   @summary Immutable vectors whose length is les than  `pow2 32`
*)

module FStar.Vector.Base
module U32 = FStar.UInt32
module S = FStar.Seq

////////////////////////////////////////////////////////////////////////////////
/// The basic model of vectors as u32-length sequences
////////////////////////////////////////////////////////////////////////////////

/// The length of a vector fits in 32 bits
let len_t = U32.t

/// The main type provided by this module
val vec:
    a:Type u#a
  -> l:len_t
  -> Type u#a

/// A convenience to use `nat` for the length of vector in specs and proofs
let length (#a:Type) (#l:len_t) (v:vec a l) : GTot nat = U32.v l

(**
    Abstractly, a `vec a l` is just a sequence whose length is `U32.v l`.
    `reveal` and `hide` build an isomorphism establishing this
**)

val reveal:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> GTot (s:S.seq a{S.length s = length v})

val hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> GTot (vec a (U32.uint_to_t (S.length s)))

val hide_reveal:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> Lemma (ensures (hide (reveal v) == v))
          [SMTPat (reveal v)]

val reveal_hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> Lemma (ensures (reveal (hide s) == s))
          [SMTPat (hide s)]

/// The type has decidable equality, so long as each of its elements does
val t_has_eq:
    l:len_t
  -> a:Type
  -> Lemma
    (requires (hasEq a))
    (ensures (hasEq (vec a l)))
    [SMTPat (hasEq (vec a l))]

/// Extensional equality for vectors
let equal (#a:Type) (#l:len_t) (v1:vec a l) (v2:vec a l) =
    Seq.equal (reveal v1) (reveal v2)

/// Extensional equality can be used to prove syntactic equality
val extensionality:
    #a:Type
  -> #l:len_t
  -> v1:vec a l
  -> v2:vec a l
  -> Lemma (requires (equal v1 v2))
          (ensures (v1 == v2))

////////////////////////////////////////////////////////////////////////////////
/// end of the basic model
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
/// A small set of basic operations on vectors, corresponding to the operations on
/// sequences. Other operations can be derived from these, as we do for seq.
///    -- init, index, update, append, slice
////////////////////////////////////////////////////////////////////////////////

/// `index_t v`: is the type of a within-bounds index of `v`
let index_t (#a:Type) (#l:len_t) (v:vec a l) =
    m:len_t{U32.v m < U32.v l}

/// `init l contents`:
///    initialize an `l`-sized vector using `contents i` for the `i`th element
val init:
    #a:Type
  -> l:len_t
  -> contents: (i:nat { i < U32.v l } -> Tot a)
  -> Tot (vec a l)

/// `index v i`: get the `i`th element of `v`
val index:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:index_t v
  -> Tot a

/// `v.(i)` is shorthand for `index v i`
unfold let op_Array_Access = index

/// `update v i x`:
///     a new vector that differs from `v` only at index `i`, where it contains `x`.
val update:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:index_t v
  -> x:a
  -> Tot (vec a l)

/// `v.(i) <- x` is shorthand for `update v i x`
unfold let op_Array_Assignment = update

/// `append v1 v2`:
///    requires proving that the sum of the lengths of v1 and v2 still fit in a u32
val append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:vec a l1
  -> v2:vec a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Tot (vec a U32.(l1 +^ l2))

/// `v1 @| v2`: shorthand for `append v1 v2`
unfold let (@|) = append

/// `slice v i j`:
///    the sub-vector of `v` starting from index `i` up to, but not including, `j`
val slice:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Tot (vec a U32.(j -^ i))

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about the basic operations, all rather boring
///    -- Each is just a lifting specifying the corresponding operation on seq
////////////////////////////////////////////////////////////////////////////////

val reveal_init:
    #a:Type
  -> l:len_t
  -> contents: (i:nat { i < U32.v l } -> Tot a)
  -> Lemma
    (ensures (reveal (init l contents) == Seq.init (U32.v l) contents))
    [SMTPat (init l contents)]

val reveal_index:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:index_t v
  -> Lemma
    (ensures (v.(i) == Seq.index (reveal v) (U32.v i)))
    [SMTPat (v.(i))]

val reveal_update:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:index_t v
  -> x:a
  -> Lemma
    (ensures (reveal (v.(i) <- x) == Seq.upd (reveal v) (U32.v i) x))
    [SMTPat (v.(i) <- x)]

val reveal_append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:vec a l1
  -> v2:vec a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Lemma
    (ensures (reveal (v1 @| v2) == Seq.append (reveal v1) (reveal v2)))
    [SMTPat (v1 @| v2)]

val reveal_slice:
    #a:Type
  -> #l:len_t
  -> v:vec a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Lemma
    (ensures (reveal (slice v i j) == S.slice (reveal v) (U32.v i) (U32.v j)))
    [SMTPat (slice v i j)]
