(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module P = LowStar.Permissions

/// `LowStar.Array` is the new workhorse of Low*, as the base class for every memory-allocated
/// object that can be extracted to C. An array `b` is conceptually defined as a portion of a memory
/// unit returned by a `malloc` call:
///
/// ```
/// [Memory contents]
///        +                        b.idx      b.idx + b.length    b.max_length
///        +                          ↓              ↓                  ↓
///    b.content  <-  [---------------|++++++++++++++|------------------]
///        +                                ↑
///        +                as_seq b, as_perm_seq b (depends on b.pid)
///  [End of memory]
/// ```
///
/// Each cell of the array is modelled as an independent memory location. You can view the contents
/// of `b` in two different ways:
///  * `as_seq h b` gives you access to the values stored at memory address `b.content` in heap `h`;
///  * `as_perm_seq h b` gives the state of the permissions `b` currently owns over the cells of the
///    array.
///
/// Indeed, `LowStar.Array` arrays are managed by a permission system, allowing you to effectively
/// track aliasing over the memory location covered by the array. The permission system rely on a
/// permission identifier `pid` stored in `b.pid`. You can have two arrays `b1` and `b2` pointing to
/// the same memory location and same portion of an array, but distinc since they have different
/// `pid`s.
///
/// The invariant maintained by the permission system is that for every cell of `b.content`, the sum
/// of all permissions belonging to all the `pid`s created so far is less than the value 1, which
/// represents full permission. Since all write-related operations require full permission to be
/// called, this invariant effectively enforces a Rust-like aliasing rule : only one mutable alias
/// at a time.

/// `LowStar.Array.Defs` contains the base definitions of the class, while `LowStar.Array.Modifies`
/// defines the `modifies` clauses theory on which our dynamic frame style of memory safety relies
/// upon. The rest of this file defines all the stateful operations allowed on arrays.

include LowStar.Array.Defs
include LowStar.Array.Modifies


(**** Allocation and deallocation *)

val alloc (#a:Type0) (init:a) (len:U32.t)
  : ST (array a)
       (requires fun _ -> U32.v len > 0)
       (ensures fun h0 b h1 ->
         modifies loc_none h0 h1 /\
         fresh_loc (loc_array b) h0 h1 /\
         writeable h1 b /\
         freeable b /\
         as_seq h1 b == Seq.create (U32.v len) init /\
         length b = len)


/// As per the C semantics, you can only free the entire allocation unit returned to you by
/// `malloc`. This behavior is enforced by the `freeable` predicate, which doesn't depend on the
/// heap. `freeable b` morally means : "`b` is not a subarray". `freeable` is preserved by all the
/// functions that don't split their argument spatially. Freeing also requires full permission.
val free (#a: Type) (b: array a) : HST.ST unit
  (requires (fun h0 -> writeable h0 b /\ live h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    modifies (loc_array b) h0 h1
  ))

(****  Reading and writing *)

/// The read operation only requires the array to be live.
val index (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

/// But to update, you need the full permission on the cell you want to change.
val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b}) (v:a) : Stack unit
  (requires fun h -> writeable_cell h b (U32.v i) /\ live h b)
  (ensures fun h0 _ h1 ->  writeable_cell h1 b (U32.v i) /\
    modifies (loc_array b) h0 h1 /\
    as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v /\
    as_perm_seq h1 b == as_perm_seq h0 b
  )

(**** Permissions management *)

/// `share b` effectively allocates a new `pid` and a corresponding array `b1` for the array `b`.
/// The new `b1` array will conceptually be a immutable reference to `b` with same contents.
/// However `b1` is disjoint from `b`; that is compatible with the `modifies` clause because neither
/// `b` or `b1` will have full permission in `h1`, so you cannot modify the contents (with `upd`) of
/// either of the two buffers. Caution: `b` is affected by `share` and loses half of its permission;
/// if you had full permission on `b` in `h0`, it is no longer the case in `h1`.
val share (#a:Type0) (b:array a) : Stack (array a)
  (requires fun h0 -> live h0 b /\ vlength b > 0)
  (ensures fun h0 b' h1 ->
    modifies (loc_array b) h0 h1 /\
    live h1 b /\ live h1 b' /\
    loc_disjoint (loc_array b) (loc_array b') /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    as_seq h1 b' == as_seq h1 b /\ // The values of the new array are the same as the initial array
    gatherable b b' /\
    fresh_loc (loc_array b') h0 h1 /\
    (freeable b ==> freeable b') /\
    (forall (i:nat{i < vlength b}). {:pattern get_perm h1 b' i \/ get_perm h1 b i }
    // The permission gets split in two
      get_perm h1 b' i == P.half_permission (get_perm h0 b i) /\
      get_perm h1 b i == P.half_permission (get_perm h0 b i)
    ))

/// `share` issues a `gatherable` predicate used to track equivalence classes of references to the
/// same thing. As such it is transitive (with a additional disjointness requirement), as well as
/// commutative.
val gatherable_trans (#a: Type0) (b1 b2 b3: array a): Lemma
  (requires (gatherable b1 b2 /\ gatherable b2 b3 /\ loc_disjoint (loc_array b1) (loc_array b3)))
  (ensures (gatherable b1 b3))
  [SMTPat [gatherable b1 b2; gatherable b2 b3; gatherable b1 b3]]

/// Gather is the reciprocal operation of `share`. It has to be use if you want to regain full
/// permission on an array that you shared previously. The precondition of `gather` requires you to
/// prove that you are managing your permissions correcty, since the permissions of `b` and `b1`
/// have to be addable.
val gather:
  #a: Type ->
  b: array a ->
  b1: array a ->
  Stack unit (requires (fun h0 ->
    gatherable b b1 /\
    live h0 b /\ live h0 b1 /\
    (forall (i:nat{i < vlength b}). summable_permissions h0 b b1  )
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < vlength b}). {:pattern (get_perm h1 b i)}
    // Permissions are summed into the first array
      get_perm h1 b i ==  P.sum_permissions (get_perm h0 b i) (get_perm h0 b1 i)
    ) /\
    as_seq h1 b == as_seq h0 b /\ // The value of the array are not modifies
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))

/// `move` implements a different permission management pattern than `share`. It effectively
/// "deactivates" the current reference to the array by giving it permission 0 and transferring
/// the old permission to a new fresh reference.
val move:
  #a: Type ->
  b: array a ->
  Stack (array a) (requires (fun h0 ->
    live h0 b
  )) (ensures (fun h0 b' h1 ->
    live h1 b' /\ gatherable b b' /\ modifies (loc_array b) h0 h1 /\
    loc_disjoint (loc_array b) (loc_array b') /\
    fresh_loc (loc_array b') h0 h1  /\
    (freeable b ==> freeable b') /\
    as_seq h0 b == as_seq h1 b' /\
    as_perm_seq h0 b == as_perm_seq h1 b'
  ))

(**** Spatial decomposition *)

/// Standard sub-array extraction. The `gsub` postcondition is instrumented with lemmas such that
/// `sub b` acts like a narrower view on the array `b`. However, it does not infer disjointness
/// between non-overlapping `sub` of the same array. For that, see the functions below.
val sub:
 #a:Type0 ->
 b:array a ->
 i:U32.t ->
 len:U32.t{U32.v len > 0} ->
  Stack (array a)
    (requires (fun h ->
      U32.v i + U32.v len <= vlength b /\ live h b
    ))
    (ensures (fun h y h' ->
      h == h' /\ y == gsub b i len
    ))

/// `split b` decomposes into to parts `b1` and `b2` such that `b` is the concatenation of `b1` and
/// `b2`. These two parts are disjoints, so that modifying them plays nicely with the `modifies`
/// theory. While `b1` and `b2` are in scope, you cannot use `b` anymore since it has lost its
/// liveness.
val split:
  #a: Type ->
  b: array a ->
  idx: U32.t{ U32.v idx > 0 /\ U32.v idx < vlength b} ->
  Stack (array a & array a) (requires (fun h0 ->
    live h0 b
  )) (ensures (fun h0 bs h1 ->
    is_split_into b (fst bs, snd bs) /\ live h1 (fst bs) /\ live h1 (snd bs) /\
    modifies loc_none h0 h1 /\
    loc_disjoint (loc_array (fst bs)) (loc_array (snd bs)) /\
    as_seq h1 (fst bs) == Seq.slice (as_seq h0 b) 0 (U32.v idx) /\
    as_seq h1 (snd bs) == Seq.slice (as_seq h0 b) (U32.v idx) (vlength b) /\
    as_perm_seq h1 (fst bs) == Seq.slice (as_perm_seq h0 b) 0 (U32.v idx) /\
    as_perm_seq h1 (snd bs) == Seq.slice (as_perm_seq h0 b) (U32.v idx) (vlength b)
  ))

/// `glue` is the reciprocal of `split` in the same way `gather` is the reciprocal of `share`.
/// However, `glue` is less flexible than `gather` since you have to provide the original `b`
/// from which `b1` and `b2` have been `split` from.
val glue:
  #a: Type ->
  b: array a ->
  b1: array a ->
  b2: array a ->
  Stack unit
    (requires (fun h0 ->
      live h0 b1 /\ live h0 b2 /\ is_split_into b (b1,b2)
    )) (ensures (fun h0 _ h1 ->
      live h1 b /\
      modifies loc_none h0 h1 /\
      as_seq h1 b == Seq.append (as_seq h0 b1) (as_seq h0 b2) /\
      as_perm_seq h1 b == Seq.append (as_perm_seq h0 b1) (as_perm_seq h0 b2)
    ))
