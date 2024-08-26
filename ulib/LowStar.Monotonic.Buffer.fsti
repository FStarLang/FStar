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
module LowStar.Monotonic.Buffer

module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* Most comments are taken from the Low* tutorial at:
   https://fstarlang.github.io/lowstar/html/LowStar.html
 *)

(* Shorthand for preorder over sequences *)
unfold let srel (a:Type0) = Preorder.preorder (Seq.seq a)

(*
 * A compatibility relation between preorders of a sequence and its subsequence
 *)
[@@"opaque_to_smt"]
unfold
let compatible_subseq_preorder (#a:Type0)
  (len:nat) (rel:srel a) (i:nat) (j:nat{i <= j /\ j <= len}) (sub_rel:srel a)
  = (forall (s1 s2:Seq.seq a). {:pattern (rel s1 s2); (sub_rel (Seq.slice s1 i j) (Seq.slice s2 i j))}  //for any two sequences s1 and s2
                         (Seq.length s1 == len /\ Seq.length s2 == len /\ rel s1 s2) ==>  //of length len, and related by rel
		         (sub_rel (Seq.slice s1 i j) (Seq.slice s2 i j))) /\  //their slices [i, j) are related by sub_rel
    (forall (s s2:Seq.seq a). {:pattern (sub_rel (Seq.slice s i j) s2); (rel s (Seq.replace_subseq s i j s2))}  //for any two sequences s and s2
                        (Seq.length s == len /\ Seq.length s2 == j - i /\ sub_rel (Seq.slice s i j) s2) ==>  //such that s has length len and s2 has length (j - i), and the slice [i, j) of s is related to s2 by sub_rel
  		        (rel s (Seq.replace_subseq s i j s2)))  //if we replace the slice [i, j) in s by s2, then s and the resulting buffer are related by rel


/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KaRaMeL implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.
///
/// The type is indexed by two preorders:
/// rrel is the preorder with which the buffer is initially created
/// rel  is the preorder of the current buffer (which could be a sub-buffer of the original one)
///
/// The buffer contents are constrained to evolve according to rel

(*
 * rrel is part of the type for technical reasons
 * If we make it part of the implementation of the buffer type,
 * it bumps up the universe of buffer itself by one,
 * which is too restrictive (e.g. no buffers of buffers)
 *
 * We expect that clients will rarely work with this directly
 * Most of the times, they will use wrappers such as buffer, immutable buffer etc.
 *)
val mbuffer (a:Type0) (rrel rel:srel a) :Tot Type0

/// The C ``NULL`` pointer is represented as the Low* ``null`` buffer. For
/// any given type, there is exactly one ``null`` buffer of this type,
/// just like there is exactly one C ``NULL`` pointer of any given type.
///
/// The nullity test ``g_is_null`` is ghost, for proof purposes
/// only. The corresponding stateful nullity test is ``is_null``, see
/// below.

(* FIXME: The nullity test for proof purposes is currently expressed
   as a ghost predicate, `g_is_null`, but it is scheduled to be
   replaced with equality with `null` *)

val g_is_null (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot bool

val mnull (#a:Type0) (#rrel #rel:srel a) :Tot (b:mbuffer a rrel rel {g_is_null b})

val null_unique (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :Lemma (g_is_null b <==> b == mnull)

/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

val unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem) :GTot Type0


/// ``live h b`` holds if, and only if, buffer ``b`` is currently
/// allocated in ``h`` and has not been deallocated yet.
///
/// This predicate corresponds to the C notion of "lifetime", and as
/// such, is a prerequisite for all stateful operations on buffers
/// (see below), per the C standard:
///
///   If an object is referred to outside of its lifetime, the
///   behavior is undefined.
///
///   -- ISO/IEC 9899:2011, Section 6.2.4 paragraph 2
///
/// By contrast, it is not required for the ghost versions of those
/// operators.

val live (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot Type0


/// The null pointer is always live.

val live_null (a:Type0) (rrel rel:srel a) (h:HS.mem) :Lemma (live h (mnull #a #rrel #rel))

val live_is_null (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true))
         (ensures (live h b))
         [SMTPat (live h b)]

/// A live buffer has already been allocated.

val live_not_unused_in (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h)) (ensures False)


/// If two memories have equal domains, then liveness in one implies liveness in the other

val lemma_live_equal_mem_domains (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h0 h1:HS.mem)
  :Lemma (requires (HST.equal_domains h0 h1 /\ live h0 b))
         (ensures  (live h1 b))
	 [SMTPat (HST.equal_domains h0 h1); SMTPat (live h1 b)]


(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

val live_not_unused_in' (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h))
         (ensures False)
         [SMTPat (live h b); SMTPat (b `unused_in` h)]


/// Buffers live in the HyperStack model, which is an extension of
/// the HyperHeap model, a hierarchical memory model that divides the
/// heap into a tree of regions. This coarse-grained separation
/// allows the programmer to state modifies clauses at the level of
/// regions, rather than on individual buffers.
///
/// The HyperHeap memory model is described:
///  - in the 2016 POPL paper: https://www.fstar-lang.org/papers/mumon/
///  - in the relevant section of the F* tutorial: http://www.fstar-lang.org/tutorial/
///
/// ``frameOf b`` returns the identifier of the region in which the
/// buffer ``b`` lives.

val frameOf (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :Tot HS.rid


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

val as_addr (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot nat


/// A buffer is unused if, and only if, its address is unused.

val unused_in_equiv (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (unused_in b h <==>
          (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b))))


/// If a buffer is live, then so is its region.

val live_region_frameOf (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b))
         (ensures (HS.live_region h (frameOf b)))
         [SMTPatOr [
	     [SMTPat (live h b)];
             [SMTPat (HS.live_region h (frameOf b))];
         ]]


/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

val len (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot U32.t

let length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot nat = U32.v (len b)


/// The null pointer has length 0.

val len_null (a:Type0) (rrel rel:srel a) :Lemma (len (mnull #a #rrel #rel) == 0ul)

val length_null_1 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (length b =!= 0)) (ensures (g_is_null b == false))
         [SMTPat (length b)]

val length_null_2 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true)) (ensures (length b == 0))
         [SMTPat (g_is_null b)]


/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

(* TODO: why not return a lseq and remove length_as_seq lemma? *)
val as_seq (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot (Seq.seq a)


/// The contents of a buffer ``b`` has the same length as ``b`` itself.

val length_as_seq (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (Seq.length (as_seq h b) == length b)
         [SMTPat (Seq.length (as_seq h b))]


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.


let get (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (p:mbuffer a rrel rel) (i:nat)
  :Ghost a (requires (i < length p)) (ensures (fun _ -> True))
  = Seq.index (as_seq h p) i

/// Injectivity in the first preorder

val mbuffer_injectivity_in_first_preorder (_:unit)
  : Lemma (forall (a:Type0) (rrel1 rrel2 rel1 rel2:srel a)
             (b1:mbuffer a rrel1 rel1)
	     (b2:mbuffer a rrel2 rel2).
	     rrel1 =!= rrel2 ==> ~ (b1 === b2))

/// Before defining sub-buffer related API, we need to define the notion of "compatibility"
///
///
/// Sub-buffers can be taken at a different preorder than their parent buffers
/// But we need to ensure that the changes to the sub-buffer are compatible with the preorder
/// of the parent buffer, and vice versa.

(*
 * The quantifiers are fiercely guarded, so if you are working directly with them,
 * you may have to write additional asserts as triggers
 *)
[@@"opaque_to_smt"]
unfold let compatible_sub
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t{U32.v i + U32.v len <= length b}) (sub_rel:srel a)
  = compatible_subseq_preorder (length b) rel (U32.v i) (U32.v i + U32.v len) sub_rel


/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// Further the clients can attach a preorder with the subbuffer (sub_rel),
/// provided it is compatible
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

val mgsub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t)
  :Ghost (mbuffer a rrel sub_rel)
         (requires (U32.v i + U32.v len <= length b))
	 (ensures (fun _ -> True))

// goffset

/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a:Type0) (#rrel #rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures  (live h b <==> (live h (mgsub sub_rel b i len) /\ (exists h0 . {:pattern (live h0 b)} live h0 b))))
         [SMTPatOr [
             [SMTPat (live h (mgsub sub_rel b i len))];
             [SMTPat (live h b); SMTPat (mgsub sub_rel b i len);]
         ]]


val gsub_is_null (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b))
         (ensures (g_is_null (mgsub sub_rel b i len) <==> g_is_null b))
         [SMTPat (g_is_null (mgsub sub_rel b i len))]


/// The length of a sub-buffer is exactly the one provided at ``gsub``.


val len_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len':U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len' <= length b))
         (ensures (len (mgsub sub_rel b i len') == len'))
         [SMTPatOr [
             [SMTPat (len (mgsub sub_rel b i len'))];
             [SMTPat (length (mgsub sub_rel b i len'))];
         ]]


val frameOf_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b))
         (ensures (frameOf (mgsub sub_rel b i len) == frameOf b))
  [SMTPat (frameOf (mgsub sub_rel b i len))]

val as_addr_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b))
         (ensures (as_addr (mgsub sub_rel b i len) == as_addr b))
         [SMTPat (as_addr (mgsub sub_rel b i len))]

val mgsub_inj (#a:Type0) (#rrel #rel:srel a) (sub_rel1 sub_rel2:srel a)
  (b1 b2:mbuffer a rrel rel)
  (i1 i2:U32.t)
  (len1 len2:U32.t)
  :Lemma (requires (U32.v i1 + U32.v len1 <= length b1 /\
                    U32.v i2 + U32.v len2 <= length b2 /\
		    mgsub sub_rel1 b1 i1 len1 === mgsub sub_rel2 b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

val gsub_gsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:U32.t) (len1:U32.t) (sub_rel1:srel a)
  (i2: U32.t) (len2: U32.t) (sub_rel2:srel a)
  :Lemma (requires (U32.v i1 + U32.v len1 <= length b /\
                    U32.v i2 + U32.v len2 <= U32.v len1))
         (ensures  (((compatible_sub b i1 len1 sub_rel1 /\  compatible_sub (mgsub sub_rel1 b i1 len1) i2 len2 sub_rel2) ==> compatible_sub b (U32.add i1 i2) len2 sub_rel2) /\
                    mgsub sub_rel2 (mgsub sub_rel1 b i1 len1) i2 len2 == mgsub sub_rel2 b (U32.add i1 i2) len2))
         [SMTPat (mgsub sub_rel2 (mgsub sub_rel1 b i1 len1) i2 len2)]


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

val gsub_zero_length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (compatible_sub b 0ul (len b) rel /\ b == mgsub rel b 0ul (len b))


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

val as_seq_gsub (#a:Type0) (#rrel #rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b))
         (ensures (as_seq h (mgsub sub_rel b i len) == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len)))
         [SMTPat (as_seq h (mgsub sub_rel b i len))]

/// Two live non-null buffers having the same region and address have
/// their elements of the same type.

val live_same_addresses_equal_types_and_preorders
  (#a1 #a2: Type0)
  (#rrel1 #rel1: srel a1)
  (#rrel2 #rel2: srel a2)
  (b1: mbuffer a1 rrel1 rel1)
  (b2: mbuffer a2 rrel2 rel2)
  (h: HS.mem)
: Lemma
  ((frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2 /\ live h b1 /\ live h b2 /\ (~ (g_is_null b1 /\ g_is_null b2))) ==> (a1 == a2 /\ rrel1 == rrel2))


/// # The modifies clause
///
/// The modifies clause for regions, references and buffers.
/// ==========================================================
///
/// This module presents the modifies clause, a way to track the set
/// of memory locations modified by a stateful Low* (or even F*)
/// program. The basic principle of modifies clauses is that any
/// location that is disjoint from a set of memory locations modified
/// by an operation is preserved by that operation.
///
/// We start by specifying a monoid of sets of memory locations. From
/// a rough high-level view, ``loc`` is the type of sets of memory
/// locations, equipped with an identity element ``loc_none``,
/// representing the empty set, and an associative and commutative
/// operator, ``loc_union``, representing the union of two sets of
/// memory locations.
///
/// Moreover, ``loc_union`` is idempotent, which is useful to cut SMT
/// matching loops with ``modifies_trans`` and ``modifies_refl`` below.

[@@erasable]
val loc : Type0

val loc_none: loc

val loc_union
  (s1 s2: loc)
: GTot loc

val loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_union_comm
  (s1 s2: loc)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)
  [SMTPat (loc_union s1 s2)]

val loc_union_assoc
  (s1 s2 s3: loc)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_idem_1
  (s1 s2: loc)
: Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2))]

val loc_union_idem_2
  (s1 s2: loc)
: Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]

val loc_union_loc_none_l
  (s: loc)
: Lemma
  (loc_union loc_none s == s)
  [SMTPat (loc_union loc_none s)]

val loc_union_loc_none_r
  (s: loc)
: Lemma
  (loc_union s loc_none == s)
  [SMTPat (loc_union s loc_none)]

/// ``loc_buffer b`` is the set of memory locations associated to a buffer ``b``.

val loc_buffer_from_to (#a:Type0) (#rrel #rel:srel a) (b: mbuffer a rrel rel) (from to: U32.t) : GTot loc

val loc_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot loc

val loc_buffer_eq (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) : Lemma
  (loc_buffer b == loc_buffer_from_to b 0ul (len b))

val loc_buffer_from_to_high (#a: Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t)
: Lemma
  (requires (length b <= U32.v to))
  (ensures (loc_buffer_from_to b from to == loc_buffer_from_to b from (len b)))

val loc_buffer_from_to_none (#a: Type) (#rrel #rel: srel a) (b: mbuffer a rrel rel) (from to: U32.t)
: Lemma
  (requires (g_is_null b \/ length b < U32.v from \/ U32.v to < U32.v from))
  (ensures (loc_buffer_from_to b from to == loc_none))

val loc_buffer_from_to_mgsub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t)
  (from to: U32.t)
: Lemma
  (requires (
    U32.v i + U32.v len <= length b /\
    U32.v from <= U32.v to /\ U32.v to <= U32.v len
  ))
  (ensures (
    loc_buffer_from_to (mgsub sub_rel b i len) from to == loc_buffer_from_to b (i `U32.add` from) (i `U32.add` to)
  ))

val loc_buffer_mgsub_eq (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t)
  :Lemma
         (requires (U32.v i + U32.v len <= length b))
	 (ensures (loc_buffer (mgsub sub_rel b i len) == loc_buffer_from_to b i (i `U32.add` len)))

val loc_buffer_null (a:Type0) (rrel rel:srel a)
  :Lemma (loc_buffer (mnull #a #rrel #rel) == loc_none)
         [SMTPat (loc_buffer (mnull #a #rrel #rel))]

val loc_buffer_from_to_eq
  (#a:Type0) (#rrel #rel:srel a)
  (b: mbuffer a rrel rel)
  (from to: U32.t)
: Lemma
  (requires (U32.v from <= U32.v to /\ U32.v to <= length b))
  (ensures (loc_buffer_from_to b from to == loc_buffer (mgsub rel b from (to `U32.sub` from))))
  [SMTPat (loc_buffer_from_to b from to)]

val loc_buffer_mgsub_rel_eq
  (#a:Type0) (#rrel #rel:srel a)
  (b: mbuffer a rrel rel)
  (rel1 rel2: srel a)
  (i len: U32.t)
: Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (loc_buffer (mgsub rel1 b i len) == loc_buffer (mgsub rel2 b i len)))
  [SMTPat (loc_buffer (mgsub rel1 b i len)); SMTPat (loc_buffer (mgsub rel2 b i len))]


/// ``loc_addresses r n`` is the set of memory locations associated to a
/// set of addresses ``n`` in a given region ``r``.

val loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc

unfold let loc_addr_of_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot loc =
  loc_addresses false (frameOf b) (Set.singleton (as_addr b))

/// ``loc_regions r`` is the set of memory locations associated to a set
/// ``r`` of regions.

val loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: GTot loc


/// ``loc_mreference b`` is the set of memory locations associated to a
/// reference ``b``, which is actually the set of memory locations
/// associated to the address of ``b``.

unfold
let loc_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses true (HS.frameOf b) (Set.singleton (HS.as_addr b))

unfold
let loc_freed_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses false (HS.frameOf b) (Set.singleton (HS.as_addr b))


/// ``loc_region_only r`` is the set of memory locations associated to a
/// region ``r`` but not any region ``r'`` that extends ``r`` (in the sense
/// of ``FStar.HyperStack.extends``.)

unfold
let loc_region_only
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (Set.singleton r)


/// ``loc_all_regions_from r`` is the set of all memory locations
/// associated to a region ``r`` and any region ``r'`` that transitively
/// extends ``r`` (in the sense of ``FStar.HyperStack.extends``,
/// e.g. nested stack frames.)

unfold
let loc_all_regions_from
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (HS.mod_set (Set.singleton r))


/// We equip the ``loc`` monoid of sets of memory locations with an
/// inclusion relation, ``loc_includes``, which is a preorder compatible
/// with ``loc_union``. Although we consider sets of memory locations,
/// we do not specify them using any F* set library such as
/// ``FStar.Set``, ``FStar.TSet`` or ``FStar.GSet``, because ``loc_includes``
/// encompasses more than just set-theoretic inclusion.

val loc_includes
  (s1 s2: loc)
: GTot Type0

val loc_includes_refl
  (s: loc)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_trans_backwards
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]

val loc_includes_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))

val loc_includes_union_l
  (s1 s2 s: loc)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))


val loc_includes_union_l'
  (s1 s2 s: loc)
  : Lemma
      (requires (loc_includes s1 s \/ loc_includes s2 s))
      (ensures (loc_includes (loc_union s1 s2) s))
      [SMTPat (loc_includes (loc_union s1 s2) s)]

val loc_includes_union_r'
  (s s1 s2: loc)
: Lemma
  (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_none
  (s: loc)
: Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]


/// If a buffer ``b1`` includes a buffer ``b2`` in the sense of the buffer
/// theory (see ``LowStar.Buffer.includes``), then so are their
/// corresponding sets of memory locations.

val loc_includes_gsub_buffer_r
  (l:loc)
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt32.t) (len:UInt32.t) (sub_rel:srel a)
: Lemma (requires (UInt32.v i + UInt32.v len <= (length b) /\
                   loc_includes l (loc_buffer b)))
        (ensures  (loc_includes l (loc_buffer (mgsub sub_rel b i len))))
        [SMTPat (loc_includes l (loc_buffer (mgsub sub_rel b i len)))]

val loc_includes_gsub_buffer_r' (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt32.t) (len:UInt32.t) (sub_rel:srel a)
  :Lemma (requires (UInt32.v i + UInt32.v len <= (length b)))
         (ensures  (loc_includes (loc_buffer b) (loc_buffer (mgsub sub_rel b i len))))
         [SMTPat (mgsub sub_rel b i len)]

val loc_includes_gsub_buffer_l (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (i1:UInt32.t) (len1:UInt32.t) (sub_rel1:srel a)
  (i2:UInt32.t) (len2:UInt32.t) (sub_rel2:srel a)
  :Lemma (requires (UInt32.v i1 + UInt32.v len1 <= (length b) /\
                    UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1
         ))
         (ensures  (loc_includes (loc_buffer (mgsub sub_rel1 b i1 len1)) (loc_buffer (mgsub sub_rel2 b i2 len2))))
         [SMTPat (mgsub sub_rel1 b i1 len1); SMTPat (mgsub sub_rel2 b i2 len2)]

val loc_includes_loc_buffer_loc_buffer_from_to
  (#a: _) (#rrel #rel: _)
  (b: mbuffer a rrel rel)
  (from to: U32.t)
: Lemma
  (loc_includes (loc_buffer b) (loc_buffer_from_to b from to))

val loc_includes_loc_buffer_from_to
  (#a: _) (#rrel #rel: _)
  (b: mbuffer a rrel rel)
  (from1 to1 from2 to2: U32.t)
: Lemma
  (requires (U32.v from1 <= U32.v from2 /\ U32.v to2 <= U32.v to1))
  (ensures (loc_includes (loc_buffer_from_to b from1 to1) (loc_buffer_from_to b from2 to2)))

/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val loc_includes_as_seq (#a:Type0) (#rrel #rel1 #rel2:srel a)
  (h1 h2:HS.mem) (larger:mbuffer a rrel rel1) (smaller:mbuffer a rrel rel2)
  :Lemma (requires (loc_includes (loc_buffer larger) (loc_buffer smaller) /\
                    as_seq h1 larger == as_seq h2 larger /\
		    (live h1 larger \/ live h1 smaller) /\ (live h2 larger \/ live h2 smaller)))
         (ensures  (as_seq h1 smaller == as_seq h2 smaller))

/// Given a buffer ``b``, if its address is in a set ``s`` of addresses in
/// the region of ``b``, then the set of memory locations corresponding
/// to ``b`` is included in the set of memory locations corresponding to
/// the addresses in ``s`` in region ``r``.
///
/// In particular, the set of memory locations corresponding to a
/// buffer is included in the set of memory locations corresponding to
/// its region and address.

val loc_includes_addresses_buffer (#a:Type0) (#rrel #rel:srel a)
  (preserve_liveness:bool) (r:HS.rid) (s:Set.set nat) (p:mbuffer a rrel rel)
  :Lemma (requires (frameOf p == r /\ Set.mem (as_addr p) s))
         (ensures  (loc_includes (loc_addresses preserve_liveness r s) (loc_buffer p)))
         [SMTPat (loc_includes (loc_addresses preserve_liveness r s) (loc_buffer p))]

val loc_includes_addresses_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_addresses true (frameOf b) (Set.singleton (as_addr b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]


/// The set of memory locations corresponding to a buffer is included
/// in the set of memory locations corresponding to its region.

val loc_includes_region_buffer (#a:Type0) (#rrel #rel:srel a)
  (preserve_liveness:bool) (s:Set.set HS.rid) (b:mbuffer a rrel rel)
  :Lemma (requires (Set.mem (frameOf b) s))
         (ensures (loc_includes (loc_regions preserve_liveness s) (loc_buffer b)))
         [SMTPat (loc_includes (loc_regions preserve_liveness s) (loc_buffer b))]

val loc_includes_region_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_regions true (Set.singleton (frameOf b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]


/// If a region ``r`` is in a set of regions ``s``, then the set of memory
/// locations corresponding to a set of addresses ``a`` in ``r`` is
/// included in the set of memory locations corresponding to the
/// regions in ``s``.
///
/// In particular, the the set of memory locations corresponding to a
/// set of addresses ``a`` in a given region ``r`` is included in the set
/// of memory locations corresponding to region ``r``.

val loc_includes_region_addresses
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a))]

val loc_includes_region_addresses'
  (preserve_liveness: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (loc_includes (loc_regions true (Set.singleton r)) (loc_addresses preserve_liveness r a))
  [SMTPat (loc_addresses preserve_liveness r a)]

/// If a set of region identifiers ``s1`` includes a set of region
/// identifiers ``s2``, then so are their corresponding sets of memory
/// locations.

val loc_includes_region_region
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2))]

val loc_includes_region_region'
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions false s) (loc_regions preserve_liveness s))
  [SMTPat (loc_regions preserve_liveness s)]

/// The following lemma can act as a cut when reasoning with sets of
/// memory locations corresponding to sets of regions.

val loc_includes_region_union_l
  (preserve_liveness: bool)
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2)))
  [SMTPat (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2))]


/// If a set of addresses ``s1`` includes a set of addresses ``s2``,
/// then so are their corresponding memory locations
val loc_includes_addresses_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r s1) (loc_addresses preserve_liveness2 r s2)))

val loc_includes_addresses_addresses_1
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires (r1 == r2 /\ (preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2)))
  [SMTPat (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2))]

val loc_includes_addresses_addresses_2
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
: Lemma
  (loc_includes (loc_addresses false r s) (loc_addresses preserve_liveness r s))
  [SMTPat (loc_addresses preserve_liveness r s)]

/// Patterns with loc_includes, union on the left

val loc_includes_union_l_buffer
  (s1 s2:loc)
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  :Lemma (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
         (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
         [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]

val loc_includes_union_l_addresses
  (s1 s2: loc)
  (prf: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (loc_includes s1 (loc_addresses prf r a) \/ loc_includes s2 (loc_addresses prf r a)))
  (ensures (loc_includes (loc_union s1 s2) (loc_addresses prf r a)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_addresses prf r a))]

val loc_includes_union_l_regions
  (s1 s2: loc)
  (prf: bool)
  (r: Set.set HS.rid)
: Lemma
  (requires (loc_includes s1 (loc_regions prf r) \/ loc_includes s2 (loc_regions prf r)))
  (ensures (loc_includes (loc_union s1 s2) (loc_regions prf r)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_regions prf r))]

/// Since inclusion encompasses more than just set-theoretic
/// inclusion, we also need to specify disjointness accordingly, as a
/// symmetric relation compatible with union.

val loc_disjoint
  (s1 s2: loc)
: GTot Type0

val loc_disjoint_sym
  (s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))

val loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))


/// If two sets of memory locations are disjoint, then so are any two
/// included sets of memory locations.

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]

val loc_disjoint_gsub_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:UInt32.t) (len1:UInt32.t) (sub_rel1:srel a)
  (i2:UInt32.t) (len2:UInt32.t) (sub_rel2:srel a)
  :Lemma (requires (UInt32.v i1 + UInt32.v len1 <= (length b) /\
                    UInt32.v i2 + UInt32.v len2 <= (length b) /\
		    (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
                     UInt32.v i2 + UInt32.v len2 <= UInt32.v i1)))
         (ensures  (loc_disjoint (loc_buffer (mgsub sub_rel1 b i1 len1)) (loc_buffer (mgsub sub_rel2 b i2 len2))))
         [SMTPat (mgsub sub_rel1 b i1 len1); SMTPat (mgsub sub_rel2 b i2 len2)]

val loc_disjoint_loc_buffer_from_to
  (#a: _) (#rrel #rel: _)
  (b: mbuffer a rrel rel)
  (from1 to1 from2 to2: U32.t)
: Lemma
  (requires (U32.v to1 <= U32.v from2 \/ U32.v to2 <= U32.v from1))
  (ensures (loc_disjoint (loc_buffer_from_to b from1 to1) (loc_buffer_from_to b from2 to2)))

/// If two sets of addresses correspond to different regions or are
/// disjoint, then their corresponding sets of memory locations are
/// disjoint.

val loc_disjoint_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2))]

/// If two sets of region identifiers are disjoint, then so are their
/// corresponding sets of memory locations.

val loc_disjoint_regions
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2)))
  [SMTPat (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2))]


/// Some utilities to work with lists of buffers and locs

(* buf_t is a `buffer` at some type `a` *)
let buf_t = a:Type0 & rrel:srel a & rel:srel a & mbuffer a rrel rel

(* A convenience to construct a buf_t *)
[@@BigOps.__reduce__]
let buf (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) : buf_t = (|a, rrel, rel, b|)

(* A conjunction of liveness conditions on the buffers in `l`
   Implicitly reduced at typechecking time *)
[@@"opaque_to_smt"]
unfold
let all_live (h:HS.mem) (l:list buf_t) : Type0 =
  BigOps.big_and #buf_t (fun (| _, _, _, b |) -> live h b) l

(* Pairwise disjointness of locations;
   Implicitly reduced at typechecking time *)
[@@"opaque_to_smt"]
unfold
let all_disjoint (l:list loc) : Type0 =
  BigOps.pairwise_and loc_disjoint l

(* Union of a list of locations;
   Implicitly reduced at typechecking time *)
[@@"opaque_to_smt"]
unfold
let loc_union_l (l:list loc) =
  BigOps.normal (List.Tot.fold_right_gtot l loc_union loc_none)

(*
 * Same as all_disjoint, retaining for backward compatibility
 *)
[@@"opaque_to_smt"]
unfold
let loc_pairwise_disjoint (l:list loc) :Type0 = BigOps.pairwise_and loc_disjoint l

/// The modifies clauses proper.
///
/// Let ``s`` be a set of memory locations, and ``h1`` and ``h2`` be two
/// memory states. Then, ``s`` is modified from ``h1`` to ``h2`` only if,
/// any memory location disjoint from ``s`` is preserved from ``h1`` into
/// ``h2``. Elimination lemmas illustrating this principle follow.

val modifies
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0

/// If a region ``r`` is disjoint from a set ``s`` of memory locations
/// which is modified, then its liveness is preserved.

val modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]

/// If a reference ``b`` is disjoint from a set ``p`` of memory locations
/// which is modified, then its liveness and contents are preserved.

val modifies_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h' b) ]
  ] ]

/// If a buffer ``b`` is disjoint from a set ``p`` of
/// memory locations which is modified, then its liveness and contents
/// are preserved.

val modifies_buffer_elim (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (p:loc) (h h':HS.mem)
  :Lemma (requires (loc_disjoint (loc_buffer b) p /\ live h b /\ modifies p h h'))
         (ensures  (live h' b /\ (as_seq h b == as_seq h' b)))
         [SMTPatOr [
             [ SMTPat (modifies p h h'); SMTPat (as_seq h b) ] ;
             [ SMTPat (modifies p h h'); SMTPat (live h b) ];
             [ SMTPat (modifies p h h'); SMTPat (as_seq h' b) ] ;
             [ SMTPat (modifies p h h'); SMTPat (live h' b) ]
         ]]

val modifies_buffer_from_to_elim (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (from to: U32.t) (p:loc) (h h':HS.mem)
  :Lemma (requires (loc_disjoint (loc_buffer_from_to b from to) p /\ live h b /\ modifies p h h' /\ U32.v from <= U32.v to /\ U32.v to <= length b))
         (ensures  (live h' b /\ Seq.slice (as_seq h b) (U32.v from) (U32.v to) == Seq.slice (as_seq h' b) (U32.v from) (U32.v to)))

/// If the memory state does not change, then any memory location is
/// modified (and, in particular, the empty set, ``loc_none``.)

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]


/// If a set ``s2`` of memory locations is modified, then so is any set
/// ``s1`` that includes ``s2``. In other words, it is always possible to
/// weaken a modifies clause by widening its set of memory locations.

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]

/// Some memory locations are tagged as liveness-insensitive: the
/// liveness preservation of a memory location only depends on its
/// disjointness from the liveness-sensitive memory locations of a
/// modifies clause.

val address_liveness_insensitive_locs: loc

val region_liveness_insensitive_locs: loc

val address_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))
         [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))]

val address_liveness_insensitive_addresses (r: HS.rid) (a: Set.set nat) : Lemma
  (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))
  [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))]

val region_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))
         [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))]

val region_liveness_insensitive_addresses (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))]

val region_liveness_insensitive_regions (rs: Set.set HS.rid) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))]

val region_liveness_insensitive_address_liveness_insensitive:
  squash (region_liveness_insensitive_locs `loc_includes` address_liveness_insensitive_locs)

val modifies_liveness_insensitive_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ address_liveness_insensitive_locs `loc_includes` l2 /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
  ]]
  (* TODO: pattern *)

val modifies_liveness_insensitive_buffer
  (l1 l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies (loc_union l1 l2) h h' /\
                    loc_disjoint l1 (loc_buffer x)  /\
		    address_liveness_insensitive_locs `loc_includes` l2 /\
		    live h x))
         (ensures  (live h' x))
         [SMTPatOr [
           [SMTPat (live h x); SMTPat (modifies (loc_union l1 l2) h h');];
           [SMTPat (live h' x); SMTPat (modifies (loc_union l1 l2) h h');];
         ]]

let modifies_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
 : Lemma (requires (modifies l h h' /\
                    address_liveness_insensitive_locs `loc_includes` l /\
		    h `HS.contains` x))
         (ensures  (h' `HS.contains` x))
         [SMTPatOr [
           [SMTPat (h `HS.contains` x); SMTPat (modifies l h h');];
           [SMTPat (h' `HS.contains` x); SMTPat (modifies l h h');];
         ]]
  = modifies_liveness_insensitive_mreference loc_none l h h' x

let modifies_liveness_insensitive_buffer_weak
  (l:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ live h x))
         (ensures  (live h' x))
         [SMTPatOr [
             [SMTPat (live h x); SMTPat (modifies l h h');];
             [SMTPat (live h' x); SMTPat (modifies l h h');];
         ]]
  = modifies_liveness_insensitive_buffer loc_none l h h' x

val modifies_liveness_insensitive_region
  (l1 l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_region_only false x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' x)];
  ]]

val modifies_liveness_insensitive_region_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]

val modifies_liveness_insensitive_region_buffer
  (l1 l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_buffer x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
         [SMTPatOr [
             [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h (frameOf x))];
             [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' (frameOf x))];
         ]]

val modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' x)];
  ]]

val modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
  : Lemma (requires (modifies l2 h h' /\
                     region_liveness_insensitive_locs `loc_includes` l2 /\
		     HS.live_region h (HS.frameOf x)))
          (ensures (HS.live_region h' (HS.frameOf x)))
          [SMTPatOr [
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
          ]]

val modifies_liveness_insensitive_region_buffer_weak
  (l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies l2 h h' /\
                    region_liveness_insensitive_locs `loc_includes` l2 /\
		    HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
         [SMTPatOr [
           [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (frameOf x))];
           [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (frameOf x))];
         ]]

/// Modifies clauses are transitive. This lemma is the most general
/// one.

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val modifies_trans_linear (l l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies l h1 h2 /\ modifies l_goal h2 h3 /\ l_goal `loc_includes` l))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (modifies l h1 h2); SMTPat (modifies l_goal h1 h3)]


/// Regions that are not live can be removed from sets of memory
/// locations that are modified.

val modifies_only_live_regions
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions false rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

/// As a consequence, fresh regions can be removed from modifies
/// clauses.

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]

val new_region_modifies (m0: HS.mem) (r0: HS.rid) (col: option int) : Lemma
  (requires (HST.is_eternal_region r0 /\ HS.live_region m0 r0 /\ (None? col \/ HS.is_heap_color (Some?.v col))))
  (ensures (
    let (_, m1) = HS.new_eternal_region m0 r0 col in
    modifies loc_none m0 m1
  ))
  [SMTPat (HS.new_eternal_region m0 r0 col)]


/// Stack discipline: any stack frame (and all its transitively
/// extending regions) that is pushed, modified and popped can be
/// removed from a modifies clause.

/// AR: 01/29/2019: Removing the smt pattern from this lemma.
///                 Clients are no longer expected to call it explicitly,
///                 if you are having to, please raise an issue.

val modifies_fresh_frame_popped
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_all_regions_from false (HS.get_tip h1)) s) h1 h2 /\
    (HS.get_tip h2) == (HS.get_tip h1) /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    (HS.get_tip h3) == HS.get_tip h0
  ))

/// Compatibility lemmas to rescue modifies clauses specified in the
/// standard F* HyperStack library.

val modifies_loc_regions_intro
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions true rs) h1 h2))

val modifies_loc_addresses_intro
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only false r) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses true r a) l) h1 h2))

/// Modifies clauses for allocating a reference: nothing is
/// modified. (In particular, a modifies clause does not track
/// memory locations that are created.)

val modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel)
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.ralloc_post i init h x h')]

val modifies_salloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HS.is_stack_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.salloc_post init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.salloc_post init h x h')]

/// Modifies clause for freeing a reference: the address is modified.

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference r) m (HS.free r m))
  [SMTPat (HS.free r m)]

/// Another compatibility lemma

val modifies_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))
  [SMTPat (HST.modifies_none h1 h2)]

/// Compatibility with HS.upd

val modifies_upd
  (#t: Type) (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (v: t)
  (h: HS.mem)
: Lemma
  (requires (HS.contains h r))
  (ensures (modifies (loc_mreference r) h (HS.upd h r v)))
  [SMTPat (HS.upd h r v)]

/// Introduction lemma for modifying loc_buffer_from_to

val modifies_loc_buffer_from_to_intro
  (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (from to: U32.t)
  (l: loc) (h h' : HS.mem)
: Lemma
  (requires (
    let s = as_seq h b in
    let s' = as_seq h' b in
    live h b /\
    modifies (loc_union l (loc_buffer b)) h h' /\
    U32.v from <= U32.v to /\
    U32.v to <= length b /\
    Seq.slice s 0 (U32.v from) `Seq.equal` Seq.slice s' 0 (U32.v from) /\
    Seq.slice s (U32.v to) (length b) `Seq.equal` Seq.slice s' (U32.v to) (length b)
  ))
  (ensures (modifies (loc_union l (loc_buffer_from_to b from to)) h h'))


///  A memory ``h`` does not contain address ``a`` in region ``r``, denoted
///  ``does_not_contain_addr h (r, a)``, only if, either region ``r`` is
///  not live, or address ``a`` is unused in region ``r``.

(* BEGIN TODO: move to FStar.Monotonic.HyperStack *)

val does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: GTot Type0

val not_live_region_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: Lemma
  (requires (~ (HS.live_region h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val unused_in_does_not_contain_addr
  (h: HS.mem)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (h `does_not_contain_addr` (HS.frameOf r, HS.as_addr r)))

val addr_unused_in_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: Lemma
  (requires (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val free_does_not_contain_addr
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid & nat)
: Lemma
  (requires (
    HS.is_mm r /\
    m `HS.contains` r /\
    fst x == HS.frameOf r /\
    snd x == HS.as_addr r
  ))
  (ensures (
    HS.free r m `does_not_contain_addr` x
  ))
  [SMTPat (HS.free r m `does_not_contain_addr` x)]

val does_not_contain_addr_elim
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid & nat)
: Lemma
  (requires (
    m `does_not_contain_addr` x /\
    HS.frameOf r == fst x /\
    HS.as_addr r == snd x
  ))
  (ensures (~ (m `HS.contains` r)))

(** END TODO *)

/// Addresses that have not been allocated yet can be removed from
/// modifies clauses.

val modifies_only_live_addresses
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses false r a) l) h h' /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))


(* Generic way to ensure that a buffer just allocated is disjoint from
   any other object, however the latter's liveness is defined. *)

val loc_not_unused_in (h: HS.mem) : GTot loc

val loc_unused_in (h: HS.mem) : GTot loc

(* Shortcut notations with more handy names *)

let loc_in (l: loc) (h: HS.mem) =
  loc_not_unused_in h `loc_includes` l

let loc_not_in (l: loc) (h: HS.mem) =
  loc_unused_in h `loc_includes` l

val loc_regions_unused_in (h: HS.mem) (rs: Set.set HS.rid) : Lemma
  (requires (forall r . Set.mem r rs ==> (~ (HS.live_region h r))))
  (ensures (loc_unused_in h `loc_includes` loc_regions false rs))

val loc_unused_in_not_unused_in_disjoint (h: HS.mem) : Lemma
  (loc_disjoint (loc_unused_in h) (loc_not_unused_in h))

val not_live_region_loc_not_unused_in_disjoint
  (h0: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (~ (HS.live_region h0 r)))
  (ensures (loc_disjoint (loc_region_only false r) (loc_not_unused_in h0)))

val fresh_frame_loc_not_unused_in_disjoint
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (loc_disjoint (loc_region_only false (HS.get_tip h1)) (loc_not_unused_in h0)))
  [SMTPat (HS.fresh_frame h0 h1)]

val live_loc_not_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b))
         (ensures  (loc_not_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (live h b)]

val unused_in_loc_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (unused_in b h))
         (ensures  (loc_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (unused_in b h)]

val modifies_address_liveness_insensitive_unused_in
  (h h' : HS.mem)
: Lemma
  (requires (modifies (address_liveness_insensitive_locs) h h'))
  (ensures (loc_not_unused_in h' `loc_includes` loc_not_unused_in h /\ loc_unused_in h `loc_includes` loc_unused_in h'))

/// Addresses that have not been allocated yet can be removed from
/// modifies clauses.

val modifies_only_not_unused_in
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_union (loc_unused_in h) l) h h'))
  (ensures (modifies l h h'))

val mreference_live_loc_not_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.contains h r)];
    [SMTPat (loc_not_unused_in h `loc_includes` loc_mreference r)];
    [SMTPat (loc_not_unused_in h `loc_includes` loc_freed_mreference r)];
  ]]

val mreference_unused_in_loc_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in h `loc_includes` loc_freed_mreference r /\ loc_unused_in h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.unused_in r h)];
    [SMTPat (loc_unused_in h `loc_includes` loc_mreference r)];
    [SMTPat (loc_unused_in h `loc_includes` loc_freed_mreference r)];
  ]]

val unused_in_not_unused_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_not_unused_in h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2)]

val modifies_loc_unused_in
  (l: loc)
  (h1 h2: HS.mem)
  (l' : loc)
: Lemma
  (requires (
    modifies l h1 h2 /\
    address_liveness_insensitive_locs `loc_includes` l /\
    loc_unused_in h2 `loc_includes` l'
  ))
  (ensures (loc_unused_in h1 `loc_includes` l'))
  [SMTPatOr [
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in h2 `loc_includes` l')];
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in h1 `loc_includes` l')];
  ]]

/// Shorthand: freshness

let fresh_loc (l: loc) (h h' : HS.mem) : GTot Type0 =
  loc_unused_in h `loc_includes` l /\
  loc_not_unused_in h' `loc_includes` l

val ralloc_post_fresh_loc (#a:Type) (#rel:Preorder.preorder a) (i: HS.rid) (init:a) (m0: HS.mem)
                       (x: HST.mreference a rel{HST.is_eternal_region (HS.frameOf x)}) (m1: HS.mem) : Lemma
    (requires (HST.ralloc_post i init m0 x m1))
    (ensures (fresh_loc (loc_freed_mreference x) m0 m1))
    [SMTPat (HST.ralloc_post i init m0 x m1)]

//AR: this is needed for liveness across fresh_frame
val fresh_frame_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures  (modifies loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]

val popped_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures  (modifies (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]

val modifies_remove_new_locs (l_fresh l_aux l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (fresh_loc l_fresh h1 h2 /\
                     modifies l_aux h1 h2 /\
		     l_goal `loc_includes` l_aux /\
                     modifies (loc_union l_fresh l_goal) h2 h3))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (fresh_loc l_fresh h1 h2);
	   SMTPat (modifies l_aux h1 h2);
	   SMTPat (modifies l_goal h1 h3)]

(*
 * AR: this lemma is framing the modifies clause across a fresh frame
 *     one way to do it would have been to reuse the lemma modifies_remove_new_locs,
 *       treating the fresh frame as another new location
 *     however, the way library is set up, loc_region in any form cannot be considered
 *       a fresh loc
 *     so, we have a special lemma for fresh_frame
 *)
val modifies_remove_fresh_frame (h1 h2 h3:HS.mem) (l:loc)
  : Lemma (requires (HS.fresh_frame h1 h2 /\
                     modifies (loc_union (loc_all_regions_from false (HS.get_tip h2)) l) h2 h3))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies l h1 h3); SMTPat (HS.fresh_frame h1 h2)]

/// Legacy shorthands for disjointness and inclusion of buffers
///

let disjoint (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2) :GTot Type0 =
  loc_disjoint (loc_buffer b1) (loc_buffer b2)

let includes (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2) :GTot Type0 =
  loc_includes (loc_buffer b1) (loc_buffer b2) /\
  (g_is_null b1 <==> g_is_null b2)

val disjoint_neq (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (disjoint b1 b2 /\ U32.v (len b1) > 0))
         (ensures (~(b1 === b2)))

val empty_disjoint (#t1 #t2: Type) (#rrel1 #rel1: srel t1) (#rrel2 #rel2: srel t2) (b1: mbuffer t1 rrel1 rel1) (b2: mbuffer t2 rrel2 rel2) : Lemma
  (requires (length b1 == 0))
  (ensures (disjoint b1 b2))


(*
/// The liveness of a sub-buffer entails from the liveness
/// of its enclosing buffer.

val includes_live (#a:Type0) (#rrel #rel1 #rel2:srel a)
  (h:HS.mem) (larger:mbuffer a rrel rel1) (smaller:mbuffer a rrel rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures  (live h larger ==> live h smaller))
         [SMTPatOr [
             [SMTPat (includes larger smaller); SMTPat (live h larger)];
             [SMTPat (includes larger smaller); SMTPat (live h smaller)];
         ]]
*)

val includes_frameOf_as_addr (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
         [SMTPat (larger `includes` smaller)]

///
/// Useful shorthands for pointers, or maybe-null pointers

inline_for_extraction
type mpointer (a:Type0) (rrel:srel a) (rel:srel a)  =
  b:mbuffer a rrel rel{length b == 1}

inline_for_extraction
type mpointer_or_null (a:Type0) (rrel:srel a) (rel:srel a) =
  b:mbuffer a rrel rel{if g_is_null b then True else length b == 1}

unfold
let deref (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (x:mpointer a rrel rel) =
  get h x 0


/// Two pointers having different contents are disjoint. This is valid
/// only for pointers, i.e. buffers of size 1.

val pointer_distinct_sel_disjoint
  (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (b1:mpointer a rrel1 rel1)
  (b2:mpointer a rrel2 rel2)
  (h:HS.mem)
  :Lemma (requires (live h b1 /\ live h b2 /\ get h b1 0 =!= get h b2 0))
         (ensures  (disjoint b1 b2))

/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// The nullity test, ``is_null b``, which KaRaMeL compiles to C as ``b == NULL``.

val is_null (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack bool (requires (fun h -> live h b))
                  (ensures  (fun h y h' -> h == h' /\ y == g_is_null b))


/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KaRaMeL extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val msub (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a) (b:mbuffer a rrel rel)
  (i:U32.t) (len:Ghost.erased U32.t)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U32.v i + U32.v (Ghost.reveal len) <= length b /\ compatible_sub b i (Ghost.reveal len) sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == mgsub sub_rel b i (Ghost.reveal len)))

/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U32.sub (len b) i``. KaRaMeL compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val moffset (#a:Type0) (#rrel #rel:srel a) (sub_rel:srel a) (b:mbuffer a rrel rel)
  (i:U32.t)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U32.v i <= length b /\ compatible_sub b i (U32.sub (len b) i) sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == mgsub sub_rel b i (U32.sub (len b) i)))
// goffset


/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KaRaMeL compiles it as b[i].

val index (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (i:U32.t)
  :HST.Stack a (requires (fun h -> live h b /\ U32.v i < length b))
               (ensures  (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))


/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

/// ``g_upd_seq b s h`` updates the entire buffer `b`'s contents in
/// heap `h` to correspond to the sequence `s`

val g_upd_seq (#a:Type0) (#rrel #rel:srel a)
              (b:mbuffer a rrel rel) (s:Seq.lseq a (length b))
	      (h:HS.mem{live h b})
  :GTot HS.mem

val lemma_g_upd_with_same_seq (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b)) (ensures (g_upd_seq b (as_seq h b) h == h))

/// A lemma specifying `g_upd_seq` in terms of its effect on the
/// buffer's underlying sequence

val g_upd_seq_as_seq (#a:Type0) (#rrel #rel:srel a)
                     (b:mbuffer a rrel rel)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b})
  : Lemma (let h' = g_upd_seq b s h in
           (Seq.length s > 0 ==> not (g_is_null b)) /\
           modifies (loc_buffer b) h h' /\
           live h' b /\
           HST.equal_domains h h' /\
           as_seq h' b == s)

/// ``g_upd b i v h`` updates the buffer `b` in heap `h` at location
/// `i` writing ``v`` there. This is the spec analog of the stateful
/// update `upd` below.

let g_upd (#a:Type0) (#rrel #rel:srel a)
          (b:mbuffer a rrel rel)
          (i:nat{i < length b})
          (v:a)
          (h:HS.mem{live h b})
  : GTot HS.mem
  = g_upd_seq b (Seq.upd (as_seq h b) i v) h

val g_upd_modifies_strong (#a:Type0) (#rrel #rel:srel a)
                   (b:mbuffer a rrel rel)
                   (i:nat{i < length b})
                   (v:a)
                   (h:HS.mem{live h b})
  : Lemma (modifies (loc_buffer_from_to b (U32.uint_to_t i) (U32.uint_to_t (i + 1))) h (g_upd b i v h))

/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KaRaMeL compiles it as ``b[i] = v``.

val upd'
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i:U32.t)
  (v:a)
  :HST.Stack unit (requires (fun h -> live h b /\ U32.v i < length b /\
                                   rel (as_seq h b) (Seq.upd (as_seq h b) (U32.v i) v)))
                  (ensures  (fun h _ h' -> h' == g_upd b (U32.v i) v h))

inline_for_extraction
let upd
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i:U32.t)
  (v:a)
  : HST.Stack unit (requires (fun h -> live h b /\ U32.v i < length b /\
                                    rel (as_seq h b) (Seq.upd (as_seq h b) (U32.v i) v)))
                   (ensures (fun h _ h' -> (not (g_is_null b)) /\
                                        modifies (loc_buffer b) h h' /\
                                        live h' b /\
                                        as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v))
  = let h = HST.get () in
    upd' b i v;
    g_upd_seq_as_seq b (Seq.upd (as_seq h b) (U32.v i) v) h

(* FIXME: Comment on `recall` *)

val recallable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0

val region_lifetime_buf (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) : Type0

(*
 * A functoriality lemma
 *)
unfold
let rrel_rel_always_compatible (#a:Type0) (rrel rel:srel a) =
  forall (len:nat) (i:nat) (j:nat{i <= j /\ j <= len}). compatible_subseq_preorder len rrel i j rel


val region_lifetime_sub (#a:Type0) (#rrel #rel #subrel:srel a)
  (b0:mbuffer a rrel rel)
  (b1:mbuffer a rrel subrel)
: Lemma
  (requires rrel_rel_always_compatible rrel subrel)
  (ensures
    (region_lifetime_buf b0 /\
     (exists i len. U32.v i + U32.v len <= length b0 /\ b1 == mgsub subrel b0 i len)) ==> region_lifetime_buf b1)

val recallable_null (#a:Type0) (#rrel #rel:srel a)
  :Lemma (recallable (mnull #a #rrel #rel)) [SMTPat (recallable (mnull #a #rrel #rel))]

(*
val recallable_includes (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (recallable larger <==> recallable smaller))
         [SMTPatOr [
             [SMTPat (recallable larger); SMTPat (recallable smaller);];
             [SMTPat (larger `includes` smaller)];
         ]]
*)

val recallable_mgsub (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel /\ recallable b))
         (ensures  (recallable (mgsub sub_rel b i len)))
         [SMTPatOr [
             [SMTPat (recallable (mgsub sub_rel b i len))];
             [SMTPat (recallable b); SMTPat (mgsub sub_rel b i len);]
         ]]

val recall (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack unit (requires (fun m -> recallable b \/ (region_lifetime_buf b /\ HS.live_region m (frameOf b))))
                  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))

(*
 * Begin: API for general witness and recall
 *        Clients can witness predicates on the contents of the buffer, and later recall them
 *        Provided the predicates are stable w.r.t. the buffer preorder
 *)

(* Shorthand for predicates of Seq.seq a *)
unfold let spred (a:Type0) = Seq.seq a -> Type0

(*
 * Note the tight patterns on the quantifier, you may need to write additional triggers
 * if you are directly working with them
 *)
unfold let stable_on (#a:Type0) (p:spred a) (rel:srel a) =
  forall (s1 s2:Seq.seq a).{:pattern (p s1); (rel s1 s2); (p s2)} (p s1 /\ rel s1 s2) ==> p s2

(* Clients get this pure token when they witness a predicate *)
val witnessed (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a) :Type0

(*
 * We can only support witness and recall for gc-malloced buffers (i.e. recallable ones)
 * This is not a fundamental limitation, but needs some tweaks to the underlying state model
 *)
val witness_p (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a)
  :HST.ST unit (requires (fun h0      -> p (as_seq h0 b) /\ p `stable_on` rel))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ b `witnessed` p))

val recall_p (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a)
  :HST.ST unit (requires (fun h0      -> (recallable b \/ live h0 b) /\ b `witnessed` p))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ p (as_seq h0 b)))

val witnessed_functorial (#a:Type0)
  (#rrel #rel1 #rel2:srel a)
  (b1:mbuffer a rrel rel1) (b2:mbuffer a rrel rel2) (i len:U32.t)
  (s1 s2:spred a)
: Lemma
  (requires
    rrel_rel_always_compatible rrel rel1 /\  //e.g. trivial_preorder, immutable preorder etc.
    U32.v i + U32.v len <= length b1 /\
    b2 == mgsub rel2 b1 i len /\  //the underlying allocation unit for b1 and b2 must be the same
    witnessed b1 s1 /\
    (forall h. s1 (as_seq h b1) ==> s2 (as_seq h b2)))
  (ensures witnessed b2 s2)

(*
 * A stateful version that relaxes the rrel and rel compatibility
 *   but requires liveness of b1
 *)
val witnessed_functorial_st (#a:Type0)
  (#rrel #rel1 #rel2:srel a)
  (b1:mbuffer a rrel rel1) (b2:mbuffer a rrel rel2) (i len:U32.t)
  (s1 s2:spred a)
: HST.Stack unit
  (requires fun h ->
    live h b1 /\
    U32.v i + U32.v len <= length b1 /\
    b2 == mgsub rel2 b1 i len /\
    witnessed b1 s1 /\
    (forall h. s1 (as_seq h b1) ==> s2 (as_seq h b2)))
  (ensures fun h0 _ h1 -> h0 == h1 /\ witnessed b2 s2)

(* End: API for general witness and recall *)


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0

val free (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.ST unit (requires (fun h0 -> live h0 b /\ freeable b))
               (ensures  (fun h0 _ h1 -> (not (g_is_null b)) /\
                                      Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
                                      (HS.get_tip h1) == (HS.get_tip h0) /\
                                      modifies (loc_addr_of_buffer b) h0 h1 /\
                                      HS.live_region h1 (frameOf b)))

val freeable_length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (freeable b)) (ensures (length b > 0))
         [SMTPat (freeable b)]

val freeable_disjoint (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))

val freeable_disjoint' (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (loc_disjoint (loc_addr_of_buffer b1) (loc_addr_of_buffer b2)))
         [SMTPat (freeable b1); SMTPat (disjoint b1 b2)]

(***** Begin allocation functions *****)


/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

(*
 * Allocation functions:
 *   In the return type, we try to give heap-independent postconditions (such as length)
 *   in the refinement of the buffer type (for the usage pattern of top-level buffers)
 *   while heap dependent postconditions are provided in the ensures clause
 *
 *   One unsatisfying aspect is that these functions are duplicated in the wrappers that we write
 *   (e.g. Buffer, ImmutableBuffer, etc.)
 *   If we don't duplicate, then the clients may face type inference issues (for preorders)
 *
 *   So, if you change any of the pre- or postcondition, you should change the pre and post spec functions
 *   (such as alloc_post_mem_common etc.), rather than the specs directly

 *   Perhaps we can rely on F* type inference and not write specs explicitly in those wrappers?
 *   Will try that
 *
 *   For memory dependent post, alloc_post_mem_common is the one used by everyone
 *
 *   For heap allocations, the library also provides partial functions that could return null
 *     Clients need to explicitly check for non-null values when using these functions
 *     Partial function specs use alloc_partial_post_mem_common
 *
 *   NOTE: a useful test for the implementation of partial functions is that
 *         their spec should be valid even when their implementation just returns null
 *)

unfold let lmbuffer (a:Type0) (rrel rel:srel a) (len:nat)
  = b:mbuffer a rrel rel{length b == len /\ not (g_is_null b)}

unfold
let alloc_post_mem_common (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h0 h1:HS.mem) (s:Seq.seq a)
  = live h1 b /\
    unused_in b h0 /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies loc_none h0 h1 /\
    as_seq h1 b == s

(* Return type and post for partial allocation functions *)
unfold let lmbuffer_or_null (a:Type0) (rrel rel:srel a) (len:nat) (r:HS.rid)
  = b:mbuffer a rrel rel{(not (g_is_null b)) ==> (length b == len /\ frameOf b == r)}

unfold let alloc_partial_post_mem_common (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h0 h1:HS.mem) (s:Seq.seq a)
  = (g_is_null b /\ h0 == h1) \/
    ((not (g_is_null b)) /\ alloc_post_mem_common b h0 h1 s)


unfold let malloc_pre (r:HS.rid) (len:U32.t) = HST.is_eternal_region r /\ U32.v len > 0


/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

(*
 * See the Allocation comment above when changing the spec
 *)
val mgcmalloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == r /\ recallable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))


(*
 * Allocate a memory-managed buffer initialized with contents from src
 *
 * This allocates and initializes the buffer atomically (from the perspective of the Low* clients)
 *)
val mgcmalloc_and_blit (#a:Type0) (#rrel:srel a) (r:HS.rid)
  (#rrel1 #rel1:srel a) (src:mbuffer a rrel1 rel1) (id_src:U32.t) (len:U32.t)
  : HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == r /\ recallable b})
    (requires fun h0 ->
      malloc_pre r len /\
      live h0 src /\ U32.v id_src + U32.v len <= length src)
    (ensures fun h0 b h1 ->
      alloc_post_mem_common b h0 h1
        (Seq.slice (as_seq h0 src) (U32.v id_src) (U32.v id_src + U32.v len)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mgcmalloc_partial (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (U32.v len) r{recallable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))
  = mgcmalloc r init len


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

(*
 * See the Allocation comment above when changing the spec
 *)
val mmalloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == r /\ freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))

(*
 * Allocate a hand-managed buffer initialized with contents from src
 *
 * This allocates and initializes the buffer atomically (from the perspective of the Low* clients)
 *)
val mmalloc_and_blit (#a:Type0) (#rrel:srel a) (r:HS.rid)
  (#rrel1 #rel1:srel a) (src:mbuffer a rrel1 rel1) (id_src:U32.t) (len:U32.t)
  : HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == r /\ freeable b})
    (requires fun h0 ->
      malloc_pre r len /\
      live h0 src /\ U32.v id_src + U32.v len <= length src)
    (ensures fun h0 b h1 ->
      alloc_post_mem_common b h0 h1
        (Seq.slice (as_seq h0 src) (U32.v id_src) (U32.v id_src + U32.v len)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mmalloc_partial (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (U32.v len) r{(not (g_is_null b)) ==> freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))
  = mmalloc r init len


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

unfold let alloca_pre (len:U32.t) = U32.v len > 0

(*
 * See the Allocation comment above when changing the spec
 *)
val malloca (#a:Type0) (#rrel:srel a)
  (init:a) (len:U32.t)
  :HST.StackInline (lmbuffer a rrel rrel (U32.v len))
                   (requires (fun _       -> alloca_pre len))
                   (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init) /\
		                          frameOf b == HS.get_tip h0))

(*
 * Allocate a stack buffer initialized with contents from src
 *
 * This allocates and initializes the buffer atomically (from the perspective of the Low* clients)
 *)
val malloca_and_blit (#a:Type0) (#rrel:srel a)
  (#rrel1 #rel1:srel a) (src:mbuffer a rrel1 rel1) (id_src:U32.t) (len:U32.t)
  : HST.StackInline (lmbuffer a rrel rrel (U32.v len))
    (requires fun h0 ->
      alloca_pre len /\
      live h0 src /\ U32.v id_src + U32.v len <= length src)
    (ensures fun h0 b h1 ->
      alloc_post_mem_common b h0 h1
        (Seq.slice (as_seq h0 src) (U32.v id_src) (U32.v id_src + U32.v len)) /\
      frameOf b == HS.get_tip h0)


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloca_of_list_pre (#a:Type0) (init:list a) =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

(*
 * See the Allocation comment above when changing the spec
 *)
val malloca_of_list (#a:Type0) (#rrel:srel a) (init: list a)
  :HST.StackInline (lmbuffer a rrel rrel (normalize_term (List.Tot.length init)))
                   (requires (fun _      -> alloca_of_list_pre init))
                   (ensures (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init) /\
		                         frameOf b == HS.get_tip h0))

unfold let gcmalloc_of_list_pre (#a:Type0) (r:HS.rid) (init:list a) =
  HST.is_eternal_region r /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

(*
 * See the Allocation comment above when changing the spec
 *)
val mgcmalloc_of_list (#a:Type0) (#rrel:srel a) (r:HS.rid) (init:list a)
  :HST.ST (b:lmbuffer a rrel rrel (normalize_term (List.Tot.length init)){frameOf b == r /\ recallable b})
          (requires (fun _       -> gcmalloc_of_list_pre r init))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init)))

(*
 * See the Allocation comment above when changing the spec
 *)
inline_for_extraction
let mgcmalloc_of_list_partial (#a:Type0) (#rrel:srel a) (r:HS.rid) (init:list a)
  :HST.ST (b:lmbuffer_or_null a rrel rrel (normalize_term (List.Tot.length init)) r{recallable b})
          (requires (fun _       -> gcmalloc_of_list_pre r init))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.seq_of_list init)))

  = mgcmalloc_of_list r init


unfold let alloc_drgn_pre (h:HS.mem) (d:HST.drgn) (len:U32.t) = h `HS.live_region` (HST.rid_of_drgn d) /\ U32.v len > 0

val mmalloc_drgn (#a:Type0) (#rrel:srel a)
  (d:HST.drgn) (init:a) (len:U32.t)
: HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == HST.rid_of_drgn d /\ region_lifetime_buf b})
  (requires fun h -> alloc_drgn_pre h d len)
  (ensures fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init))

val mmalloc_drgn_mm (#a:Type0) (#rrel:srel a)
  (d:HST.drgn) (init:a) (len:U32.t)
: HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == HST.rid_of_drgn d /\ freeable b})
  (requires fun h -> alloc_drgn_pre h d len)
  (ensures fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init))

val mmalloc_drgn_and_blit (#a:Type0) (#rrel:srel a)
  (#rrel1 #rel1:srel a)
  (d:HST.drgn) (src:mbuffer a rrel1 rel1) (id_src:U32.t) (len:U32.t)
: HST.ST (b:lmbuffer a rrel rrel (U32.v len){frameOf b == HST.rid_of_drgn d /\ region_lifetime_buf b})
  (requires fun h ->
    alloc_drgn_pre h d len /\
    live h src /\
    U32.v id_src + U32.v len <= length src)
  (ensures fun h0 b h1 ->
    alloc_post_mem_common b h0 h1
      (Seq.slice (as_seq h0 src) (U32.v id_src) (U32.v id_src + U32.v len)))



(***** End allocation functions *****)


/// Derived operations

val blit (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (src:mbuffer a rrel1 rel1)
  (idx_src:U32.t)
  (dst:mbuffer a rrel2 rel2)
  (idx_dst:U32.t)
  (len:U32.t)
  :HST.Stack unit (requires (fun h -> live h src /\ live h dst /\
                                    U32.v idx_src + U32.v len <= length src /\
                                    U32.v idx_dst + U32.v len <= length dst /\
                                    (* TODO: remove the rhs part of this disjunction once patterns on loc_buffer_from_to are introduced *)
                                    (loc_disjoint (loc_buffer_from_to src idx_src (idx_src `U32.add` len)) (loc_buffer_from_to dst idx_dst (idx_dst `U32.add` len)) \/ disjoint src dst) /\
				    rel2 (as_seq h dst)
				         (Seq.replace_subseq (as_seq h dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len)
					                     (Seq.slice (as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len)))))
                  (ensures (fun h _ h' -> modifies (loc_buffer dst) h h' /\
                                        live h' dst /\
                                        Seq.slice (as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
                                        Seq.slice (as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len) /\
                                        Seq.slice (as_seq h' dst) 0 (U32.v idx_dst) ==
                                        Seq.slice (as_seq h dst) 0 (U32.v idx_dst) /\
                                        Seq.slice (as_seq h' dst) (U32.v idx_dst + U32.v len) (length dst) ==
                                        Seq.slice (as_seq h dst) (U32.v idx_dst + U32.v len) (length dst)))

val fill (#t:Type) (#rrel #rel: srel t)
  (b: mbuffer t rrel rel)
  (z:t)
  (len:U32.t)
: HST.Stack unit
  (requires (fun h ->
    live h b /\
    U32.v len <= length b /\
    rel (as_seq h b) (Seq.replace_subseq (as_seq h b) 0 (U32.v len) (Seq.create (U32.v len) z))
  ))
  (ensures  (fun h0 _ h1 ->
    modifies (loc_buffer b) h0 h1 /\
    live h1 b /\
    Seq.slice (as_seq h1 b) 0 (U32.v len) == Seq.create (U32.v len) z /\
    Seq.slice (as_seq h1 b) (U32.v len) (length b) == Seq.slice (as_seq h0 b) (U32.v len) (length b)
  ))

/// Type class instantiation for compositionality with other kinds of memory locations than regions, references or buffers (just in case).
/// No usage pattern has been found yet.

module MG = FStar.ModifiesGen

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (abuffer' region addr)

val cloc_cls: MG.cls abuffer

val cloc_of_loc (l: loc) : Tot (MG.loc cloc_cls)

val loc_of_cloc (l: MG.loc cloc_cls) : Tot loc

val loc_of_cloc_of_loc (l: loc) : Lemma
  (loc_of_cloc (cloc_of_loc l) == l)
  [SMTPat (loc_of_cloc (cloc_of_loc l))]

val cloc_of_loc_of_cloc (l: MG.loc cloc_cls) : Lemma
  (cloc_of_loc (loc_of_cloc l) == l)
  [SMTPat (cloc_of_loc (loc_of_cloc l))]

val cloc_of_loc_none: unit -> Lemma (cloc_of_loc loc_none == MG.loc_none)

val cloc_of_loc_union (l1 l2: loc) : Lemma
  (cloc_of_loc (loc_union l1 l2) == MG.loc_union (cloc_of_loc l1) (cloc_of_loc l2))

val cloc_of_loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (cloc_of_loc (loc_addresses preserve_liveness r n) == MG.loc_addresses preserve_liveness r n)

val cloc_of_loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (cloc_of_loc (loc_regions preserve_liveness r) == MG.loc_regions preserve_liveness r)

val loc_includes_to_cloc (l1 l2: loc) : Lemma
  (loc_includes l1 l2 <==> MG.loc_includes (cloc_of_loc l1) (cloc_of_loc l2))

val loc_disjoint_to_cloc (l1 l2: loc) : Lemma
  (loc_disjoint l1 l2 <==> MG.loc_disjoint (cloc_of_loc l1) (cloc_of_loc l2))

val modifies_to_cloc (l: loc) (h1 h2: HS.mem) : Lemma
  (modifies l h1 h2 <==> MG.modifies (cloc_of_loc l) h1 h2)
