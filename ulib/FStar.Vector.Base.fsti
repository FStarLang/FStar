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

   The type `raw a l`: A raw vector

     1. Raw vectors receive special treatment during extraction,
        especially by KaRaMeL, which extracts a vector to a raw C
        pointer. When extracting to OCaml, a `raw a l` is a
        `Batteries.Vect t a`

     2. The length of a vector is representable in a U32.t

     3. The interface is designed around a length-indexed type: this
        enables the compilation to raw pointers, since this ensures
        that all functions that manipulate vectors always have a U32
        variable describing that vector's length in scope.

        A length-indexed interface is also suitable for clients for whom
        proving properties about the length is a primary concern: the
        signatures in this interface carry intrinsic proofs about length
        properties, simplifying proof obligations in client code.

     4. Raw vectors lack decidable equality (since that cannot be
        implemented given the representation choice in KaRaMeL)

   The type `t a`: A dynamically sized vector

     1. Conceptually, a `t a` is a pair of a `len:U32.t` and a `raw a
        len`. They are implemented as such by KaRaMeL. When extracting
        to OCaml, `t a` is identical to `raw a _`, i.e., it is still
        extracted to a `Batteries.Vect.t a`

     2. Unlike raw vectors, `t a` supports decidable equality when it
        is supported by `a`. This is the main reason `t a` is provided
        at an abstract type, rather than being exposed as a pair of a
        U32 and a raw vector, since the latter does not support
        decidable equality.

   @summary Immutable vectors whose length is less than  `pow2 32`
*)

module FStar.Vector.Base
module U32 = FStar.UInt32
module S = FStar.Seq

////////////////////////////////////////////////////////////////////////////////
/// The basic model of raw vectors as u32-length sequences
////////////////////////////////////////////////////////////////////////////////

/// The length of a vector fits in 32 bits
let len_t = U32.t

/// A raw vector.
///   - `vector a n` is extracted to an `a*` in C by KaRaMeL
///   - Does not support decidable equality
val raw ([@@@strictly_positive] a:Type u#a)
        (l:len_t)
  : Type u#a

/// A convenience to use `nat` for the length of vector in specs and proofs
let raw_length (#a:Type) (#l:len_t) (v:raw a l) : GTot nat = U32.v l

(**
    Abstractly, a `vec a l` is just a sequence whose length is `U32.v l`.
    `reveal` and `hide` build an isomorphism establishing this
**)

val reveal:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> GTot (s:S.seq a{S.length s = raw_length v})

val hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> GTot (raw a (U32.uint_to_t (S.length s)))

val hide_reveal:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> Lemma (ensures (hide (reveal v) == v))
          [SMTPat (reveal v)]

val reveal_hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> Lemma (ensures (reveal (hide s) == s))
          [SMTPat (hide s)]

/// Extensional equality for vectors
let equal (#a:Type) (#l:len_t) (v1:raw a l) (v2:raw a l) =
    Seq.equal (reveal v1) (reveal v2)

/// Extensional equality can be used to prove syntactic equality
val extensionality:
    #a:Type
  -> #l:len_t
  -> v1:raw a l
  -> v2:raw a l
  -> Lemma (requires (equal v1 v2))
          (ensures (v1 == v2))

////////////////////////////////////////////////////////////////////////////////
/// end of the basic model
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
/// A small set of basic operations on raw vectors, corresponding to the operations
/// on sequences. Other operations can be derived from these, as we do for seq.
///    -- init, index, update, append, slice
////////////////////////////////////////////////////////////////////////////////

/// `index_t v`: is the type of a within-bounds index of `v`
let index_t (#a:Type) (#l:len_t) (v:raw a l) =
    m:len_t{U32.v m < U32.v l}

/// `init l contents`:
///    initialize an `l`-sized vector using `contents i` for the `i`th element
val init:
    #a:Type
  -> l:len_t
  -> contents: (i:nat { i < U32.v l } -> Tot a)
  -> Tot (raw a l)

/// `index v i`: get the `i`th element of `v`
val index:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> Tot a

/// `v.[i]` is shorthand for `index v i`
unfold let op_String_Access #a #l = index #a #l

/// `update v i x`:
///     - a new vector that differs from `v` only at index `i`, where it contains `x`.
///     - Incurs a full copy in KaRaMeL
///     - In OCaml, the new vector shares as much as possible with `v`
val update:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> x:a
  -> Tot (raw a l)

/// `v.[i] <- x` is shorthand for `update v i x`
unfold let op_String_Assignment #a #l = update #a #l

/// `append v1 v2`:
///     - requires proving that the sum of the lengths of v1 and v2 still fit in a u32
///     - Incurs a full copy in KaRaMeL
///     - Amortized constant time in OCaml
val append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:raw a l1
  -> v2:raw a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Tot (raw a U32.(l1 +^ l2))

/// `v1 @| v2`: shorthand for `append v1 v2`
unfold let (@|) #a #l1 #l2 = append #a #l1 #l2

/// `sub v i j`:
///     - the sub-vector of `v` starting from index `i` up to, but not including, `j`
///     - Constant time in KaRaMeL (just an addition on a pointer)
///     - Worst-case (log l) time in OCaml
val sub:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Tot (raw a U32.(j -^ i))

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
  -> v:raw a l
  -> i:index_t v
  -> Lemma
    (ensures (v.[i] == Seq.index (reveal v) (U32.v i)))
    [SMTPat (v.[i])]

val reveal_update:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> x:a
  -> Lemma
    (ensures (reveal (v.[i] <- x) == Seq.upd (reveal v) (U32.v i) x))
    [SMTPat (v.[i] <- x)]

val reveal_append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:raw a l1
  -> v2:raw a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Lemma
    (ensures (reveal (v1 @| v2) == Seq.append (reveal v1) (reveal v2)))
    [SMTPat (v1 @| v2)]

val reveal_sub:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Lemma
    (ensures (reveal (sub v i j) == S.slice (reveal v) (U32.v i) (U32.v j)))
    [SMTPat (sub v i j)]

////////////////////////////////////////////////////////////////////////////////
/// Now, we have `Vector.Base.t`, abstractly, a raw vector paired with its u32 length
////////////////////////////////////////////////////////////////////////////////
val t:
    a:Type u#a
  -> Type u#a

/// Unlike raw vectors, t-vectors support decidable equality
val t_has_eq:
    a:Type u#a
  -> Lemma
    (requires (hasEq a))
    (ensures  (hasEq (t a)))
    [SMTPat (hasEq (t a))]

/// The length of a t-vector is a dynamically computable u32
val len:
    #a:Type
  -> t a
  -> len_t

/// A convenience to access the length of a t-vector as a nat
[@@"deprecated: this will be moved to the ghost effect"]
let length (#a:Type) (x:t a) : nat = U32.v (len x)

/// Access the underlying raw vector
val as_raw:
    #a:Type
  -> x:t a
  -> raw a (len x)

/// Promote a raw vector
val from_raw:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> x:t a{len x = l}

/// as_raw and from_raw are mutual inverses
val as_raw_from_raw:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> Lemma (ensures (as_raw (from_raw v) == v))
          [SMTPat (from_raw v)]

val from_raw_as_raw:
    #a:Type
  -> x:t a
  -> Lemma (ensures (from_raw (as_raw x) == x))
          [SMTPat (as_raw x)]

/// `v.(i)` accesses the ith element of v
unfold
let op_Array_Access
    (#a:Type)
    (x:t a)
    (i:index_t (as_raw x))
  : Tot a
  = (as_raw x).[i]

/// `v.(i) <- x` is a new t-vector that differs from v only at i
unfold
let op_Array_Assignment
    (#a:Type)
    (x:t a)
    (i:index_t (as_raw x))
    (v:a)
  : Tot (t a)
  = from_raw ((as_raw x).[i] <- v)

/// `v1 @@ v2`: appending t-vectors
unfold
let (@@)
    (#a:Type)
    (x1:t a)
    (x2:t a{UInt.size (length x1 + length x2) U32.n})
  : Tot (t a)
  = from_raw (as_raw x1 @| as_raw x2)

/// `slice v i j`:
///     the sub-vector of `v` starting from index `i` up to, but not including, `j`
unfold
let slice
    (#a:Type)
    (x:t a)
    (i:len_t)
    (j:len_t{U32.(v i <= v j /\ v j <= length x)})
  : Tot (t a)
  = from_raw (sub (as_raw x) i j)

val dummy : unit
