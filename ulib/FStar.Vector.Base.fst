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
module FStar.Vector.Base
module U32 = FStar.UInt32
module S = FStar.Seq

/// The raw vector type: the main type provided by this module
let raw a l = s:S.seq a{S.length s = U32.v l}

/// Abstractly, a `raw a l` is just a sequence whose length is `U32.v l`.
/// `reveal` and `hide` build an isomorphism establishing this
let reveal #a #l v = v
let hide #a s = s
let hide_reveal #a #l v = ()
let reveal_hide #a s = ()

/// Extensional equality can be used to prove syntactic equality
let extensionality #a #l v1 v2 = ()

////////////////////////////////////////////////////////////////////////////////
/// A small set of basic operations on vectors, corresponding to the operations on
/// sequences. Other operations can be derived from these, as we do for seq.
///    -- init, index, update, append, slice
////////////////////////////////////////////////////////////////////////////////

/// `init l contents`:
///    initialize an `l`-sized vector using `contents i` for the `i`th element
let init #a l contents = Seq.init (U32.v l) contents

/// `index v i`: get the `i`th element of `v`
let index #a #l v i = Seq.index v (U32.v i)

/// `update v i x`:
///     a new vector that differs from `v` only at index `i`, where it contains `x`.
let update #a #l v i x = Seq.upd v (U32.v i) x

/// `append v1 v2`:
///    requires proving that the sum of the lengths of v1 and v2 still fit in a u32
let append #a #l1 #l2 v1 v2 = Seq.append v1 v2

/// `sub v i j`:
///    the sub-vector of `v` starting from index `i` up to, but not including, `j`
let sub #a #l v i j = Seq.slice v (U32.v i) (U32.v j)

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about the basic operations, all rather boring
///    -- Each is just a lifting specifying the corresponding operation on seq
////////////////////////////////////////////////////////////////////////////////
let reveal_init #a l contents = ()
let reveal_index #a #l v i = ()
let reveal_update #a #l v i x = ()
let reveal_append #a #l1 #l2 v1 v2 = ()
let reveal_sub #a #l v i j = ()

////////////////////////////////////////////////////////////////////////////////
/// Dynamically sized vectors
////////////////////////////////////////////////////////////////////////////////

let t a = (l:len_t & raw a l)


/// Unlike raw vectors, t-vectors support decidable equality
let t_has_eq a = ()

/// The length of a t-vector is a dynamically computable u32
let len #a (| l , _ |) = l

/// Access the underlying raw vector
let as_raw #a (|_, v|) = v

/// Promote a raw vector
let from_raw #a #l v = (| l, v |)

/// as_raw and from_raw are mutual inverses
let as_raw_from_raw #a #l v = ()
let from_raw_as_raw #a x = ()

let dummy = ()
