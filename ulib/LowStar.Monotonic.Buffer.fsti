module LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* Most comments are taken from the Low* tutorial at:
   https://fstarlang.github.io/lowstar/html/LowStar.html
 *)

(* Shorthand for preorder over sequences *)
type srel (a:Type0) = P.preorder (Seq.seq a)


/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.
///
/// The type is indexed by two preorders:
/// rrel is the starting preorder with which the original buffer was initially created
/// rel  is the preorder of the current buffer (which could be a sub-buffer of the original one)
///
/// The buffer contents are constrained to evolve according to rel

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

val null (#a:Type0) (#rrel #rel:srel a) :Tot (b:mbuffer a rrel rel {g_is_null b})

val null_unique (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :Lemma (g_is_null b <==> b == null)

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

val live_null (a:Type0) (rrel rel:srel a) (h:HS.mem) :Lemma (live h (null #a #rrel #rel))

let live_is_null (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true))
         (ensures (live h b))
         [SMTPat (live h b)]
  = null_unique b;
    live_null a rrel rel h

/// A live buffer has already been allocated.

val live_not_unused_in (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h)) (ensures False)


(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h))
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

val len_null (a:Type0) (rrel rel:srel a) :Lemma (len (null #a #rrel #rel) == 0ul)

let length_null_1 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (length b =!= 0)) (ensures (g_is_null b == false))
         [SMTPat (length b)]
  = len_null a rrel rel;
    null_unique b

let length_null_2 (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true)) (ensures (length b == 0))
         [SMTPat (g_is_null b)]
  = len_null a rrel rel;
    null_unique b


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

/// Before defining sub-buffer related API, we need to define the notion of "compatibility"
///
/// Sub-buffers can be taken at a different preorder than their parent buffers
/// But it is subject to the following compatibility relation:
///
/// The main idea is to ensure that any modifications to the parent buffer are compatible with the sub-buffer preorder
/// and vice-versa

let compatible_sub_preorder (#a:Type0)
  (len:nat) (pre:srel a)
  (offset:nat) (sub_len:nat{offset + sub_len <= len}) (sub_pre:srel a)
  = (forall (s1 s2:Seq.seq a). (Seq.length s1 == len /\ Seq.length s2 == len /\ pre s1 s2) ==>
		          (sub_pre (Seq.slice s1 offset (offset + sub_len))
			           (Seq.slice s2 offset (offset + sub_len)))) /\
    (forall (s s2:Seq.seq a). (Seq.length s == len /\ Seq.length s2 == sub_len /\ sub_pre (Seq.slice s offset (offset + sub_len)) s2) ==>
  		         (pre s (replace_subseq s offset sub_len s2)))

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

// goffset

/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPatOr [
    [SMTPat (live h (gsub b i len))];
    [SMTPat (live h b); SMTPat (gsub b i len);]
  ]]


val gsub_is_null (#t: Type) (b: buffer t) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (g_is_null (gsub b i len) <==> g_is_null b))
  [SMTPat (g_is_null (gsub b i len))]

/// The length of a sub-buffer is exactly the one provided at ``gsub``.

val len_gsub (#a: Type) (b: buffer a) (i: U32.t) (len': U32.t) : Lemma
  (requires (U32.v i + U32.v len' <= length b))
  (ensures (len (gsub b i len') == len'))
  [SMTPatOr [
    [SMTPat (len (gsub b i len'))];
    [SMTPat (length (gsub b i len'))];
  ]]

val frameOf_gsub (#a: Type) (b: buffer a) (i: U32.t) (len : U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (frameOf (gsub b i len) == frameOf b))
  [SMTPat (frameOf (gsub b i len))]

val as_addr_gsub (#a: Type) (b: buffer a) (i: U32.t) (len : U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (as_addr (gsub b i len) == as_addr b))
  [SMTPat (as_addr (gsub b i len))]

val gsub_inj
  (#t: Type)
  (b1 b2: buffer t)
  (i1 i2: U32.t)
  (len1 len2: U32.t)
: Lemma
  (requires (U32.v i1 + U32.v len1 <= length b1 /\ U32.v i2 + U32.v len2 <= length b2 /\ gsub b1 i1 len1 == gsub b2 i2 len2))
  (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))

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

