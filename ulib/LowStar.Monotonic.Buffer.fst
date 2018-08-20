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

/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.

(*
 * Replacing subsequence in s at (offset, offset + len) by sub
 *)
private let replace_subseq (#a:Type0)
  (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) (sub:Seq.lseq a len)
  :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 offset) (Seq.append sub (Seq.slice s (offset + len) (Seq.length s)))

(*
 * Shorthand slice, that takes length as the second argument
 *)
private let mslice (#a:Type0) (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) :Tot (Seq.seq a) =
  Seq.slice s offset (offset + len)

(*
 * Key lemma to prove the transitivity of the compatibility relation (to come later)
 * The lemma says that replace_subseq commutes with slice
 * We can either
 *  (a) Replace a subsequence in s at (offset1 + offset2, offset1 + offset2 + len2) by s2, OR
 *  (b) Take the slice of s at (offset1, offset1 + len1),
        replace subsequence in the slice at (offset2, offset2 + len2),
	and then replace the subsequence in s at (offset1, offset1 + len1) with this updated slice
 * Both give us the same sequence
 *)
private let lemma_replace_subseq_slice
  (a:Type0) (len offset1 len1 offset2 len2:nat)
  (s:Seq.lseq a len) (s2:Seq.lseq a len2)
  :Lemma ((offset1 + len1 <= len /\ offset2 + len2 <= len1) ==>
	  (Seq.equal (replace_subseq s (offset1 + offset2) len2 s2)
	             (replace_subseq s offset1 len1 (replace_subseq (mslice s offset1 len1)
						                    offset2 len2 s2))))
  = ()

type srel (a:Type0) = P.preorder (Seq.seq a)

(*
 * Abbreviation for preorders on l-sequences
 *)
private type lsrel (a:Type0) (len:nat) = P.preorder (Seq.lseq a len)
private let srel_to_lsrel (#a:Type0) (len:nat) (pre:srel a) :lsrel a len = fun s1 s2 -> pre s1 s2

(*
 * Notion of compatibility for the preorders on subbuffers
 *
 * The compatibility is both ways implication
 *   (a) When the parent sequence changes according to its preorder,
 *       the subsequence (offset, offset + len) should respect the sub preorder
 *   (b) When the subsequence (offset, offset + len) changed accoring to the sub preorder,
 *       the replace_subseq in the parent sequence should respect its preorder
 *
 * The direction (b) is required for valid updates
 *   In the sense that clients will update the buffer according to the buffer preorder,
 *   And since this will result in an update in the underlying reference, we need the direction (b)
 *
 * Where will the direction (a) be required? My guess is, when witnessing predicates on the buffer preorder
 *   Again, clients will witness according to the buffer preorder,
 *   And this will result in witness on the underlying reference, so we would need the direction (a)
 *)
let compatible_sub_preorder (#a:Type0)
  (len:nat) (pre:srel a)
  (offset:nat) (sub_len:nat{offset + sub_len <= len}) (sub_pre:srel a)
  = (forall (s1 s2:Seq.seq a). (Seq.length s1 == len /\ Seq.length s2 == len /\ pre s1 s2) ==>
		          (sub_pre (mslice s1 offset sub_len) (mslice s2 offset sub_len))) /\  //(a)
    (forall (s s2:Seq.seq a). (Seq.length s == len /\ Seq.length s2 == sub_len /\ sub_pre (mslice s offset sub_len) s2) ==>
  		         (pre s (replace_subseq s offset sub_len s2)))  //(b)

(*
 * Reflexivity of the compatibility relation
 *)
let lemma_sub_compatilibity_is_reflexive (#a:Type0) (len:nat) (pre:srel a)
  :Lemma (compatible_sub_preorder len pre 0 len pre)
  = assert (forall (s1 s2:Seq.seq a). Seq.length s1 == Seq.length s2 ==>
                                 Seq.equal (replace_subseq s1 0 (Seq.length s1) s2) s2)

(*
 * Transitivity of the compatibility relation
 *)
let lemma_sub_compatibility_is_transitive (#a:Type0)
  (len:nat) (pre:srel a)
  (offset1 len1:nat) (pre1:srel a)
  (offset2 len2:nat) (pre2:srel a)
  :Lemma (requires (offset1 + len1 <= len /\ offset2 + len2 <= len1 /\
                    compatible_sub_preorder len pre offset1 len1 pre1 /\
                    compatible_sub_preorder len1 pre1 offset2 len2 pre2))
	 (ensures  (compatible_sub_preorder len pre (offset1 + offset2) len2 pre2))
  = Classical.forall_intro_2 (lemma_replace_subseq_slice a len offset1 len1 offset2 len2)

(*
 * The type is indexed by two preorders:
 *   rrel: is the preorder of the underlying reference
 *   rel : is the preorder of the buffer itself
 * It is less than ideal to keep rrel in the index :(
 * But hiding it in the inductive bumps up the universe to Type u#1
 *   which means no buffers of buffers
 * Hopefully we can build libraries over it so that rarely will clients need to use mbuffer a rrel rel
 *)
abstract noeq type mbuffer (a:Type0) (rrel:srel a) (rel:srel a) :Type0 =
  | Null
  | Buffer:
    max_length: U32.t ->
    content: HST.mreference (Seq.lseq a (U32.v max_length)) (srel_to_lsrel (U32.v max_length) rrel) ->
    idx: U32.t ->
    length: U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
    compatible: squash (compatible_sub_preorder (U32.v max_length) rrel
                                                (U32.v idx) (U32.v length) rel) ->  //proof of compatibility
    mbuffer a rrel rel

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

abstract val g_is_null (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot bool
let g_is_null #_ #_ #_ b = Null? b

abstract val null (#a:Type0) (#rrel:srel a) (#rel:srel a) :Tot (b:mbuffer a rrel rel {g_is_null b})
let null #_ #_ #_ = Null

abstract val null_unique (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (g_is_null b <==> b == null)
let null_unique #_ #_ #_ _ = ()

/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

abstract val unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem) :GTot Type0
let unused_in #_ #_ #_ b h =
  match b with
  | Null -> False
  | Buffer _ content _ _ _ -> content `HS.unused_in` h

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

abstract val live (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot Type0
let live #_ #_ #_ h b =
  match b with
  | Null -> True
  | Buffer _ content _ _ _ -> h `HS.contains` content

/// The null pointer is always live.

abstract val live_null (a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem)  (* TODO: make a wrapper for default preorders *)
  :Lemma (live h (null #a #rrel #rel))
let live_null a #_ #_ h = ()

let live_is_null (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true))
         (ensures (live h b))
         [SMTPat (live h b)]
  = null_unique b;
    live_null a #rrel #rel h


/// A live buffer has already been allocated.

abstract val live_not_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h))
         (ensures False)
let live_not_unused_in #_ #_ #_ _ _ = ()

(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
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

abstract val frameOf (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :Tot HS.rid
let frameOf #_ #_ #_ b = if Null? b then HS.root else HS.frameOf (Buffer?.content b)


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

abstract val as_addr (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot nat
let as_addr #_ #_ #_  b = if g_is_null b then 0 else HS.as_addr (Buffer?.content b)


/// A buffer is unused if, and only if, its address is unused.

abstract val unused_in_equiv (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (unused_in b h <==>
          (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b))))
let unused_in_equiv #_ #_ #_ b h =
  if g_is_null b then Heap.not_addr_unused_in_nullptr (Map.sel (HS.get_hmap h) HS.root) else ()


/// If a buffer is live, then so is its region.

abstract val live_region_frameOf (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b))
         (ensures (HS.live_region h (frameOf b)))
         [SMTPatOr [
	   [SMTPat (live h b)];
           [SMTPat (HS.live_region h (frameOf b))];
         ]]
let live_region_frameOf #_ #_ #_ _ _ = ()


/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

abstract val len (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot U32.t
let len #_ #_ #_ b =
  match b with
  | Null -> 0ul
  | Buffer _ _ _ len _ -> len

let length (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot nat = U32.v (len b)


/// The null pointer has length 0.

abstract val len_null (a:Type0) (#rrel:srel a) (#rel:srel a)  (* TODO: add a wrapper for default preorder *)
  :Lemma (len (null #a #rrel #rel) == 0ul)
let len_null a #_ #_ = ()

let length_null_1 (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (length b =!= 0)) (ensures (g_is_null b == false))
         [SMTPat (length b)]
  = len_null a #rrel #rel;
    null_unique b

let length_null_2 (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true)) (ensures (length b == 0))
         [SMTPat (g_is_null b)]
  = len_null a #rrel #rel;
    null_unique b


/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

(* TODO: why not return a lseq and remove length_as_seq lemma? *)
abstract val as_seq (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel) :GTot (Seq.seq a)
let as_seq #_ #_ #_ h b =
  match b with
  | Null -> Seq.empty
  | Buffer max_len content idx len _ ->
    Seq.slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len)

/// The contents of a buffer ``b`` has the same length as ``b`` itself.

abstract val length_as_seq (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (Seq.length (as_seq h b) == length b)
         [SMTPat (Seq.length (as_seq h b))]
let length_as_seq #_ #_ #_ _ _ = ()


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.

let get (#a:Type0) (#rrel:srel a) (#rel:srel a) (h:HS.mem) (p:mbuffer a rrel rel) (i:nat)
  :Ghost a (requires (i < length p)) (ensures (fun _ -> True))
  = Seq.index (as_seq h p) i


/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// Clients can provide a preorder at which they want to take the subbuffer
/// But they have to prove compatibility
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

unfold let compatible_sub
  (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t{U32.v i + U32.v len <= length b}) (sub_rel:srel a)
  = compatible_sub_preorder (length b) rel (U32.v i) (U32.v len) sub_rel

(*
 * TODO: candidate for writing a wrapper
 *       also now there is a compatibility query for each of the gsub operation
 *       would it be worth writing a wrapper for each of those functions?
 *)
abstract val gsub (#a:Type0) (#rrel:srel a) (#rel:srel a) 
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  : Ghost (mbuffer a rrel sub_rel)
          (requires (U32.v i + U32.v len <= length b /\
	             compatible_sub b i len sub_rel))
	  (ensures (fun _ -> True))
let gsub #a #rrel #rel b i len sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content idx length () ->
    lemma_sub_compatibility_is_transitive (U32.v max_len) rrel
                                          (U32.v idx) (U32.v length) rel
					  (U32.v i) (U32.v len) sub_rel;
    Buffer max_len content (U32.add idx i) len ()

// goffset

/// A buffer is live exactly at the same time as all of its sub-buffers.

abstract val live_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures  (live h (gsub b i len sub_rel) <==> live h b))
         [SMTPatOr [
             [SMTPat (live h (gsub b i len sub_rel))];
             [SMTPat (live h b); SMTPat (gsub b i len sub_rel);]
         ]]
let live_gsub #_ #_ #_ _ _ _ _ _ = ()

abstract val gsub_is_null (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (g_is_null (gsub b i len sub_rel) <==> g_is_null b))
         [SMTPat (g_is_null (gsub b i len sub_rel))]
let gsub_is_null #_ #_ #_ _ _ _ _ = ()


/// The length of a sub-buffer is exactly the one provided at ``gsub``.

abstract val len_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len':U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len' <= length b /\ compatible_sub b i len' sub_rel))
         (ensures (len (gsub b i len' sub_rel) == len'))
         [SMTPatOr [
             [SMTPat (len (gsub b i len' sub_rel))];
             [SMTPat (length (gsub b i len' sub_rel))];
         ]]
let len_gsub #_ #_ #_ _ _ _ _ = ()

abstract val frameOf_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (frameOf (gsub b i len sub_rel) == frameOf b))
  [SMTPat (frameOf (gsub b i len sub_rel))]
let frameOf_gsub #_ #_ #_ _ _ _ _ = ()

abstract val as_addr_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (as_addr (gsub b i len sub_rel) == as_addr b))
         [SMTPat (as_addr (gsub b i len sub_rel))]
let as_addr_gsub #_ #_ #_ _ _ _ _ = ()

(* TODO: candidate for writing a wrapper *)
abstract val gsub_inj (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b1 b2:mbuffer a rrel rel)
  (i1 i2:U32.t)
  (len1 len2:U32.t)
  (sub_rel1 sub_rel2:srel a)
  :Lemma (requires (U32.v i1 + U32.v len1 <= length b1 /\ compatible_sub b1 i1 len1 sub_rel1 /\
                    U32.v i2 + U32.v len2 <= length b2 /\ compatible_sub b2 i2 len2 sub_rel2 /\
		    gsub b1 i1 len1 sub_rel1 === gsub b2 i2 len2 sub_rel2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))
let gsub_inj #_ #_ #_ _ _ _ _ _ _ _ _ = ()


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

abstract val gsub_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:U32.t) (len1:U32.t) (sub_rel1:srel a)
  (i2: U32.t) (len2: U32.t) (sub_rel2:srel a)
  :Lemma (requires (U32.v i1 + U32.v len1 <= length b /\ compatible_sub b i1 len1 sub_rel1 /\
                    U32.v i2 + U32.v len2 <= U32.v len1 /\ compatible_sub (gsub b i1 len1 sub_rel1) i2 len2 sub_rel2))
         (ensures  (compatible_sub b (U32.add i1 i2) len2 sub_rel2 /\
                    gsub (gsub b i1 len1 sub_rel1) i2 len2 sub_rel2 == gsub b (U32.add i1 i2) len2 sub_rel2))
         [SMTPat (gsub (gsub b i1 len1 sub_rel1) i2 len2 sub_rel2)]
let gsub_gsub #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  lemma_sub_compatibility_is_transitive (length b) rel (U32.v i1) (U32.v len1) sub_rel1 (U32.v i2) (U32.v len2) sub_rel2


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

abstract val gsub_zero_length (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (compatible_sub b 0ul (len b) rel /\ b == gsub b 0ul (len b) rel)
let gsub_zero_length #_ #_ #rel b = lemma_sub_compatilibity_is_reflexive (length b) rel


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

abstract val as_seq_gsub (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (h:HS.mem) (b:mbuffer a rrel rel) (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :Lemma (requires (U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel))
         (ensures (as_seq h (gsub b i len sub_rel) == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len)))
         [SMTPat (as_seq h (gsub b i len sub_rel))]
let as_seq_gsub #_ #_ #_ h b i len _ =
  match b with
  | Null -> ()
  | Buffer _ content idx len0 _ ->
    Seq.slice_slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len0) (U32.v i) (U32.v i + U32.v len)
