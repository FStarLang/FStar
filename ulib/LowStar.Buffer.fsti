module LowStar.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

(* Most comments are taken from the Low* tutorial at:
   https://fstarlang.github.io/lowstar/html/LowStar.html
 *)

/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.

val buffer (a: Type0) : Tot Type0


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

val g_is_null (#a: Type) (b: buffer a) : GTot bool

val null (#a: Type) : Tot (b: buffer a { g_is_null b } )

val null_unique (#a: Type) (b: buffer a) : Lemma
  (g_is_null b <==> b == null)


/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

val unused_in (#a: Type) (b: buffer a) (h: HS.mem) : GTot Type0


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

val live (#a: Type) (h: HS.mem) (b: buffer a) : GTot Type0


/// The null pointer is always live.

val live_null (a: Type) (h: HS.mem) : Lemma
  (live h (null #a))

let live_is_null (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (live h b))
  [SMTPat (live h b)]
= null_unique b;
  live_null a h


/// A live buffer has already been allocated.

val live_not_unused_in (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)

(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)
  [SMTPat (live h b); SMTPat (b `unused_in` h)]
= live_not_unused_in h b


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

val frameOf (#a: Type) (b: buffer a) : GTot HS.rid


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

val as_addr (#a: Type) (b: buffer a) : GTot nat


/// A buffer is unused if, and only if, its address is unused.

val unused_in_equiv (#a: Type) (b: buffer a) (h: HS.mem) : Lemma
  (ensures (unused_in b h <==> (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b)))))


/// If a buffer is live, then so is its region.

val live_region_frameOf (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b))
  (ensures (HS.live_region h (frameOf b)))
  [SMTPatOr [
    [SMTPat (live h b)];
    [SMTPat (HS.live_region h (frameOf b))];
  ]]


/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

val len (#a: Type) (b: buffer a) : GTot U32.t

let length (#a: Type) (b: buffer a) : GTot nat = U32.v (len b)


/// The null pointer has length 0.

val len_null (a: Type) : Lemma
  (len (null #a) == 0ul)

let length_null_1 (#a: Type) (b: buffer a) : Lemma
  (requires (length b <> 0))
  (ensures (g_is_null b == false))
  [SMTPat (length b)]
= len_null a;
  null_unique b

let length_null_2 (#a: Type) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (length b == 0))
  [SMTPat (g_is_null b)]
= len_null a;
  null_unique b


/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

val as_seq (#a: Type) (h: HS.mem) (b: buffer a) : GTot (Seq.seq a)


/// The contents of a buffer ``b`` has the same length as ``b`` itself.

val length_as_seq (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (Seq.length (as_seq h b) == length b)
  [SMTPat (Seq.length (as_seq h b))]


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.

let get (#a: Type) (h: HS.mem) (p: buffer a) (i: nat) : Ghost a
  (requires (i < length p))
  (ensures (fun _ -> True))
= Seq.index (as_seq h p) i


/// A buffer ``smaller`` is included in another buffer ``larger``, denoted
/// as ``includes larger smaller``, if ``smaller`` is a sub-buffer of
/// ``larger``. (See ``gsub`` below for how to actually construct such a
/// sub-buffer of a buffer.)

val includes (#a: Type) (larger smaller: buffer a) : GTot Type0


/// The liveness of a sub-buffer is exactly equivalent to the liveness
/// of its enclosing buffer.

val includes_live (#a: Type) (h: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (live h larger <==> live h smaller))
  [SMTPatOr [
    [SMTPat (includes larger smaller); SMTPat (live h larger)];
    [SMTPat (includes larger smaller); SMTPat (live h smaller)];
  ]]


/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val includes_as_seq (#a: Type) (h1 h2: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller /\ as_seq h1 larger == as_seq h2 larger))
  (ensures (as_seq h1 smaller == as_seq h2 smaller))


/// Inclusion is a preorder.

val includes_refl (#a: Type) (x: buffer a) : Lemma
  (includes x x)
  [SMTPat (includes x x)]

val includes_trans (#a: Type) (x y z: buffer a) : Lemma
  (requires (x `includes` y /\ y `includes` z))
  (ensures (x `includes` z))
  [SMTPatOr [
    [SMTPat (x `includes` y); SMTPat (y `includes` z)];
    [SMTPat (x `includes` y); SMTPat (x `includes` z)];
    [SMTPat (y `includes` z); SMTPat (x `includes` z)];
  ]]


/// A buffer and any of its sub-buffers live in the same region, and
/// at the same address, and are either both null or both not null.

val includes_frameOf_as_addr (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
  [SMTPat (larger `includes` smaller)]


/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

val gsub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : Ghost (buffer a)
  (requires (U32.v i + U32.v len <= length b))
  (ensures (fun y -> True))

/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPat (live h (gsub b i len))]


/// A sub-buffer is included in its enclosing buffer.

val includes_gsub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (b `includes` gsub b i len))
  [SMTPat (gsub b i len)]


/// The length of a sub-buffer is exactly the one provided at ``gsub``.

val len_gsub (#a: Type) (b: buffer a) (i: U32.t) (len': U32.t) : Lemma
  (requires (U32.v i + U32.v len' <= length b))
  (ensures (len (gsub b i len') == len'))
  [SMTPatOr [
    [SMTPat (len (gsub b i len'))];
    [SMTPat (length (gsub b i len'))];
  ]]


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

val gsub_gsub (#a: Type) (b: buffer a) (i1: U32.t) (len1: U32.t) (i2: U32.t) (len2: U32.t) : Lemma
  (requires (U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1))
  (ensures (
    U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2
  ))
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

val gsub_zero_length (#a: Type) (b: buffer a) : Lemma
  (b == gsub b 0ul (len b))


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

val as_seq_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (as_seq h (gsub b i len) == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len)))
  [SMTPat (as_seq h (gsub b i len))]


/// Two buffers are disjoint only if they span disjoint ranges of a
/// common enclosing buffer, or if they live in different regions or
/// at different addresses.

val disjoint (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : GTot Type0


/// Disjointness is symmetric.

val disjoint_sym (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (disjoint b1 b2 <==> disjoint b2 b1)
  [SMTPat (disjoint b1 b2)]


/// If two buffers are disjoint, then so are any of their sub-buffers.

val disjoint_includes_l (#a1 #a2: Type) (b1 b1' : buffer a1) (b2: buffer a2) : Lemma
  (requires (includes b1 b1' /\ disjoint b1 b2))
  (ensures (disjoint b1' b2))
  [SMTPat (disjoint b1' b2); SMTPat (includes b1 b1')] 

val disjoint_includes_r (#a1 #a2: Type) (b1 : buffer a1) (b2 b2': buffer a2) : Lemma
  (requires (includes b2 b2' /\ disjoint b1 b2))
  (ensures (disjoint b1 b2'))
  [SMTPat (disjoint b1 b2'); SMTPat (includes b2 b2')] 


/// A buffer that has not been allocated yet is disjoint from all
/// buffers that are already currently allocated. Consequently, two
/// buffers that are allocated separately are disjoint.

val live_unused_in_disjoint (#a1 #a2: Type) (h: HS.mem) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (live h b1 /\ (unused_in b2 h)))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (live h b1); SMTPat (disjoint b1 b2)];
    [SMTPat (live h b1); SMTPat (unused_in b2 h)];
    [SMTPat (unused_in b2 h); SMTPat (disjoint b1 b2)];
  ]]


/// If two buffers live in different regions or at different
/// addresses, then they are disjoint.

val as_addr_disjoint (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (disjoint b1 b2)];
    [SMTPat (frameOf b1); SMTPat (frameOf b2)];
    [SMTPat (as_addr b1); SMTPat (as_addr b2)];
  ]]


/// If two buffers span disjoint ranges from a common enclosing
/// buffer, then they are disjoint.

val gsub_disjoint (#a: Type) (b: buffer a) (i1 len1 i2 len2: U32.t) : Lemma
  (requires (
    U32.v i1 + U32.v len1 <= length b /\
    U32.v i2 + U32.v len2 <= length b /\
    (U32.v i1 + U32.v len1 <= U32.v i2 \/ U32.v i2 + U32.v len2 <= U32.v i1)
  ))
  (ensures (disjoint (gsub b i1 len1) (gsub b i2 len2)))
  [SMTPat (disjoint (gsub b i1 len1) (gsub b i2 len2))]


/// Useful shorthands for pointers, or maybe-null pointers

inline_for_extraction
type pointer (t: Type0) =
  b:buffer t { length b == 1 }

inline_for_extraction
type pointer_or_null (t: Type0) =
  b:buffer t { if g_is_null b then True else length b == 1 }


/// Two pointers having different contents are disjoint. This is valid
/// only for pointers, i.e. buffers of size 1.

val pointer_distinct_sel_disjoint
  (#a: Type)
  (b1: pointer a)
  (b2: pointer a)
  (h: HS.mem)
: Lemma
  (requires (
    live h b1 /\
    live h b2 /\
    get h b1 0 =!= get h b2 0
  ))
  (ensures (
    disjoint b1 b2
  ))


/// The following definitions are needed to implement the generic
/// modifies clause. Those should not be used in client code. They
/// appear in the interface only because the modifies clause is
/// defined in another module, ``LowStar.Modifies``.

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (abuffer' region addr)

val abuffer_preserved (#r: HS.rid) (#a: nat) (b: abuffer r a) (h h' : HS.mem) : GTot Type0

val abuffer_preserved_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) (h : HS.mem) : Lemma
  (abuffer_preserved b h h)

val abuffer_preserved_trans (#r: HS.rid) (#a: nat) (b: abuffer r a) (h1 h2 h3 : HS.mem) : Lemma
  (requires (abuffer_preserved b h1 h2 /\ abuffer_preserved b h2 h3))
  (ensures (abuffer_preserved b h1 h3))

val same_mreference_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
  (f: (
    (a' : Type) ->
    (pre: Preorder.preorder a') ->
    (r': HS.mreference a' pre) ->
    Lemma
    (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
    (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (abuffer_preserved b h1 h2)

val addr_unused_in_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel (HS.get_hmap h1) r)))
  (ensures (abuffer_preserved b h1 h2))

val abuffer_of_buffer (#t: Type) (b: buffer t) : Tot (abuffer (frameOf b) (as_addr b))

val abuffer_preserved_elim (#t: Type) (b: buffer t) (h h' : HS.mem) : Lemma
  (requires (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h' /\ live h b))
  (ensures (live h' b /\ as_seq h b == as_seq h' b))

let unused_in_abuffer_preserved
  (#t: Type)
  (b: buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (b `unused_in` h))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'))
= Classical.move_requires (fun b -> live_not_unused_in #t h b) b;
  live_null t h;
  null_unique b;
  unused_in_equiv b h;
  addr_unused_in_abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'

val abuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) : GTot Type0

val abuffer_includes_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) : Lemma
  (b `abuffer_includes` b)

val abuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: abuffer r a) : Lemma
  (requires (b1 `abuffer_includes` b2 /\ b2 `abuffer_includes` b3))
  (ensures (b1 `abuffer_includes` b3))

val abuffer_includes_abuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (larger `abuffer_includes` smaller /\ abuffer_preserved larger h1 h2))
  (ensures (abuffer_preserved smaller h1 h2))

val abuffer_includes_intro (#t: Type) (larger smaller: buffer t) : Lemma
  (requires (larger `includes` smaller))
  (ensures (
    let r = frameOf larger in
    let a = as_addr larger in
    abuffer_includes #r #a (abuffer_of_buffer larger) (abuffer_of_buffer smaller)
  ))

val abuffer_disjoint (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : GTot Type0

val abuffer_disjoint_sym (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : Lemma
  (abuffer_disjoint b1 b2 <==> abuffer_disjoint b2 b1)

val abuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: abuffer r a) (smaller1 smaller2: abuffer r a) : Lemma
  (requires (abuffer_disjoint larger1 larger2 /\ larger1 `abuffer_includes` smaller1 /\ larger2 `abuffer_includes` smaller2))
  (ensures (abuffer_disjoint smaller1 smaller2))

val abuffer_disjoint_intro (#t1 #t2: Type) (b1: buffer t1) (b2: buffer t2) : Lemma
  (requires (disjoint b1 b2 /\ frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2))
  (ensures (
    let r = frameOf b1 in
    let a = as_addr b1 in
    abuffer_disjoint #r #a (abuffer_of_buffer b1) (abuffer_of_buffer b2)
  ))

val liveness_preservation_intro
  (#t: Type) (h h' : HS.mem) (b: buffer t)
  (f: (
    (t' : Type) ->
    (pre: Preorder.preorder t') ->
    (r: HS.mreference t' pre) ->
    Lemma
    (requires (HS.frameOf r == frameOf b /\ HS.as_addr r == as_addr b /\ h `HS.contains` r))
    (ensures (h' `HS.contains` r))
  ))
: Lemma
  (requires (live h b))
  (ensures (live h' b))

(* Basic, non-compositional modifies clauses, used only to implement the generic modifies clause. DO NOT USE in client code *)

val modifies_0 (h1 h2: HS.mem) : GTot Type0

val modifies_0_live_region (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_0 h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_0_mreference (#a: Type) (#pre: Preorder.preorder a) (h1 h2: HS.mem) (r: HS.mreference a pre) : Lemma
  (requires (modifies_0 h1 h2 /\ h1 `HS.contains` r))
  (ensures (h2 `HS.contains` r /\ h1 `HS.sel` r == h2 `HS.sel` r))

let modifies_0_abuffer
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (abuffer_preserved b h1 h2))
= same_mreference_abuffer_preserved b h1 h2 (fun a' pre r' -> modifies_0_mreference h1 h2 r')

val modifies_1 (#a: Type) (b: buffer a) (h1 h2: HS.mem) : GTot Type0

val modifies_1_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_1_liveness
  (#a: Type) (b: buffer a) (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r'))

val modifies_1_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

val modifies_1_abuffer
  (#a: Type) (b : buffer a)
  (h1 h2: HS.mem)
  (b' : abuffer (frameOf b) (as_addr b))
: Lemma
  (requires (modifies_1 b h1 h2 /\ abuffer_disjoint #(frameOf b) #(as_addr b) (abuffer_of_buffer b) b'))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))

val modifies_1_null
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_1 b h1 h2 /\ g_is_null b))
  (ensures (modifies_0 h1 h2))

val modifies_addr_of
  (#a: Type)
  (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_addr_of_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_addr_of b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_addr_of_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_addr_of b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))


/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// The nullity test, ``is_null b``, which KreMLin compiles to C as ``b == NULL``.

val is_null (#a: Type) (b: buffer a) : HST.Stack bool
  (requires (fun h -> live h b))
  (ensures (fun h y h' -> h == h' /\ y == g_is_null b))


/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KreMLin extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val sub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i + U32.v len <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i len))


/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U32.sub (len b) i``. KreMLin compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val offset (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (len b) i)))


/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KreMLin compiles it as b[i].
val index (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack a
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))


/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

(* FIXME: their postconditions are using non-compositional modifies
   clauses, which are automatically converted to compositional
   modifies clauses by lemmas from LowStar.Modifies through
   patterns. In a future version, LowStar.Modifies could actually be
   merged into LowStar.Buffers so that postconditions of those
   operations would directly be specified in terms of the
   compositional modifies clauses.
 *)

/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KreMLin compiles it as ``b[i] = v``.

val upd
  (#a: Type)
  (b: buffer a)
  (i: U32.t)
  (v: a)
: HST.Stack unit
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h _ h' ->
    (not (g_is_null b)) /\
    modifies_1 b h h' /\
    live h' b /\
    as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v
  ))

(* FIXME: Comment on `recall` *)

val recallable (#a: Type) (b: buffer a) : GTot Type0

val recallable_includes (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (recallable larger <==> recallable smaller))
  [SMTPatOr [
    [SMTPat (recallable larger); SMTPat (recallable smaller);];
    [SMTPat (larger `includes` smaller)];
  ]]

val recall
  (#a:Type)
  (b:buffer a)
: HST.Stack unit
  (requires (fun _ -> recallable b))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a: Type) (b: buffer a) : GTot Type0

val free
  (#a: Type)
  (b: buffer a)
: HST.ST unit
  (requires (fun h0 -> live h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    (not (g_is_null b)) /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies_addr_of b h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))

/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

let alloc_post_static
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
: GTot Type0
= (not (g_is_null b)) /\
  frameOf b == r /\
  length b == len

let alloc_post_common
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
  (h0 h1: HS.mem)
: GTot Type0
= alloc_post_static r len b /\
  b `unused_in` h0 /\
  live h1 b /\
  Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
  (HS.get_tip h1) == (HS.get_tip h0) /\
  modifies_0 h0 h1

/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

val gcmalloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (b: buffer a {
    recallable b /\
    alloc_post_static r (U32.v len) b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

val malloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    freeable b
  ))


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

val alloca
  (#a: Type)
  (init: a)
  (len: U32.t)
: HST.StackInline (buffer a)
  (requires (fun h -> U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common (HS.get_tip h) (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloc_of_list_pre (#a: Type0) (init: list a) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

unfold let alloc_of_list_post (#a: Type) (len: nat) (buf: buffer a) : GTot Type0 =
  normalize (length buf == len)

val alloca_of_list
  (#a: Type0)
  (init: list a)
: HST.StackInline (buffer a)
  (requires (fun h -> alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common (HS.get_tip h) len b h h' /\
    as_seq h' b == Seq.of_list init /\
    alloc_of_list_post #a len b
  ))

val gcmalloc_of_list
  (#a: Type0)
  (r: HS.rid)
  (init: list a)
: HST.ST (b: buffer a {
    let len = FStar.List.Tot.length init in
    recallable b /\
    alloc_post_static r len b /\
    alloc_of_list_post len b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common r len b h h' /\
    as_seq h' b == Seq.of_list init
  ))
