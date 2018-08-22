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
let replace_subseq (#a:Type0)
  (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) (sub:Seq.lseq a len)
  :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 offset) (Seq.append sub (Seq.slice s (offset + len) (Seq.length s)))

let lemma_replace_subseq_elim (#a:Type0)
  (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) (sub:Seq.lseq a len)
  :Lemma (let s1 = replace_subseq s offset len sub in
          Seq.length s1 == Seq.length s /\
          Seq.equal (Seq.slice s1 0 offset) (Seq.slice s 0 offset) /\
	  Seq.equal (Seq.slice s1 offset (offset + len)) sub /\
	  Seq.equal (Seq.slice s1 (offset + len) (Seq.length s1)) (Seq.slice s (offset + len) (Seq.length s)))
	 [SMTPat (replace_subseq s offset len sub)]
  = ()

(*
 * Shorthand slice, that takes length as the second argument
 *)
private let mslice (#a:Type0) (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) :Tot (Seq.seq a) =
  Seq.slice s offset (offset + len)

(* Shorthand for preorder over sequences *)
type srel (a:Type0) = P.preorder (Seq.seq a)

private let srel_to_lsrel (#a:Type0) (len:nat) (pre:srel a) :P.preorder (Seq.lseq a len) = fun s1 s2 -> pre s1 s2

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
  = admit () (*
 * Key lemma to prove the transitivity of the compatibility relation (to come later)
 * The lemma says that replace_subseq commutes with slice
 * We can either
 *  (a) Replace a subsequence in s at (offset1 + offset2, offset1 + offset2 + len2) by s2, OR
 *  (b) Take the slice of s at (offset1, offset1 + len1),
        replace subsequence in the slice at (offset2, offset2 + len2),
	and then replace the subsequence in s at (offset1, offset1 + len1) with this updated slice
 * Both give us the same sequence
 *)
// private let lemma_replace_subseq_slice
//   (a:Type0) (len offset1 len1 offset2 len2:nat)
//   (s:Seq.lseq a len) (s2:Seq.lseq a len2)
//   :Lemma ((offset1 + len1 <= len /\ offset2 + len2 <= len1) ==>
// 	  (Seq.equal (replace_subseq s (offset1 + offset2) len2 s2)
// 	             (replace_subseq s offset1 len1 (replace_subseq (mslice s offset1 len1)
// 						                    offset2 len2 s2))))
//   = ()

 
  
//   Classical.forall_intro_2 (lemma_replace_subseq_slice a len offset1 len1 offset2 len2)

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

(* Untyped view of buffers, used only to implement the generic modifies clause. DO NOT USE in client code. *)

noeq
type ubuffer_
: Type0
= {
  b_max_length: nat;
  b_offset: nat;
  b_length: nat;
  b_is_mm: bool;
}

val ubuffer' (region: HS.rid) (addr: nat) : Tot Type0

let ubuffer' region addr = (x: ubuffer_ { x.b_offset + x.b_length <= x.b_max_length } )

let ubuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (ubuffer' region addr)

let ubuffer_of_buffer' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel)
  :Tot (ubuffer (frameOf b) (as_addr b))
  = if Null? b
    then
      Ghost.hide ({
        b_max_length = 0;
        b_offset = 0;
        b_length = 0;
        b_is_mm = false;
      })
    else
      Ghost.hide ({
        b_max_length = U32.v (Buffer?.max_length b);
        b_offset = U32.v (Buffer?.idx b);
        b_length = U32.v (Buffer?.length b);
       b_is_mm = HS.is_mm (Buffer?.content b);
    })

let ubuffer_preserved' 
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h h' : HS.mem)
: GTot Type0
= forall (t':Type0) (rrel rel:srel t') (b':mbuffer t' rrel rel) .
  (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b') ==>
  (live h' b' /\ Seq.equal (as_seq h' b') (as_seq h b'))

val ubuffer_preserved (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h h' : HS.mem) : GTot Type0

let ubuffer_preserved = ubuffer_preserved'

let ubuffer_preserved_intro
  (#r:HS.rid)
  (#a:nat)
  (b:ubuffer r a)
  (h h' :HS.mem)
  (f: (
    (t':Type0) ->
    (rrel:srel t') -> (rel:srel t') ->
    (b':mbuffer t' rrel rel) ->
    Lemma
    (requires (frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'))
    (ensures (live h' b' /\ as_seq h' b' == as_seq h b'))
  ))
: Lemma
  (ubuffer_preserved b h h')
= let g'
    (t':Type0) (rrel rel:srel t')
    (b':mbuffer t' rrel rel)
  : Lemma
    ((
      frameOf b' == r /\ as_addr b' == a /\ ubuffer_of_buffer' b' == b /\ live h b'
    ) ==> (
      live h' b' /\ as_seq h' b' == as_seq h b'
    ))
  = Classical.move_requires (f t' rrel rel) b'
  in
  Classical.forall_intro_4 g'

val ubuffer_preserved_refl (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h : HS.mem) : Lemma
  (ubuffer_preserved b h h)

let ubuffer_preserved_refl #r #a b h = ()

val ubuffer_preserved_trans (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h1 h2 h3 : HS.mem) : Lemma
  (requires (ubuffer_preserved b h1 h2 /\ ubuffer_preserved b h2 h3))
  (ensures (ubuffer_preserved b h1 h3))

let ubuffer_preserved_trans #r #a b h1 h2 h3 = ()

val same_mreference_ubuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
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
  (ubuffer_preserved b h1 h2)

let same_mreference_ubuffer_preserved #r #a b h1 h2 f =
  ubuffer_preserved_intro b h1 h2 (fun t' _ _ b' ->
    if Null? b'
    then ()
    else
      f _ _ (Buffer?.content b')
  )

val addr_unused_in_ubuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel (HS.get_hmap h1) r)))
  (ensures (ubuffer_preserved b h1 h2))

let addr_unused_in_ubuffer_preserved #r #a b h1 h2 = ()

val ubuffer_of_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :Tot (ubuffer (frameOf b) (as_addr b))

let ubuffer_of_buffer #_ #_ #_ b = ubuffer_of_buffer' b

val ubuffer_preserved_elim (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h h':HS.mem)
  :Lemma (requires (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h' /\ live h b))
         (ensures (live h' b /\ as_seq h b == as_seq h' b))

let ubuffer_preserved_elim #_ #_ #_ _ _ _ = ()

let unused_in_ubuffer_preserved (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h h':HS.mem)
  : Lemma (requires (b `unused_in` h))
          (ensures (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'))
  = Classical.move_requires (fun b -> live_not_unused_in h b) b;
    live_null a #rrel #rel h;
    null_unique b;
    unused_in_equiv b h;
    addr_unused_in_ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'

let ubuffer_includes' (larger smaller: ubuffer_) : GTot Type0 =
  larger.b_is_mm == smaller.b_is_mm /\
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

let ubuffer_includes0 (#r1 #r2:HS.rid) (#a1 #a2:nat) (larger:ubuffer r1 a1) (smaller:ubuffer r2 a2) =
  r1 == r2 /\ a1 == a2 /\ ubuffer_includes' (G.reveal larger) (G.reveal smaller)

val ubuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) : GTot Type0

let ubuffer_includes #r #a larger smaller = ubuffer_includes0 larger smaller
  

val ubuffer_includes_refl (#r: HS.rid) (#a: nat) (b: ubuffer r a) : Lemma
  (b `ubuffer_includes` b)

let ubuffer_includes_refl #r #a b = ()

val ubuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: ubuffer r a) : Lemma
  (requires (b1 `ubuffer_includes` b2 /\ b2 `ubuffer_includes` b3))
  (ensures (b1 `ubuffer_includes` b3))

let ubuffer_includes_trans #r #a b1 b2 b3 = ()

(*
 * TODO: not sure how to make this lemma work with preorders
 *       it creates a buffer larger' in the proof
 *       we need a compatible preorder for that
 *       may be take that as an argument?
 *)
(*val ubuffer_includes_ubuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: ubuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (larger `ubuffer_includes` smaller /\ ubuffer_preserved larger h1 h2))
  (ensures (ubuffer_preserved smaller h1 h2))
let ubuffer_includes_ubuffer_preserved #r #a larger smaller h1 h2 =
  ubuffer_preserved_intro smaller h1 h2 (fun t' b' ->
    if Null? b'
    then ()
    else
      let (Buffer max_len content idx' len') = b' in
      let idx = U32.uint_to_t (G.reveal larger).b_offset in
      let len = U32.uint_to_t (G.reveal larger).b_length in
      let larger' = Buffer max_len content idx len in
      assert (b' == gsub larger' (U32.sub idx' idx) len');
      ubuffer_preserved_elim larger' h1 h2
  )*)

let ubuffer_disjoint' (x1 x2: ubuffer_) : GTot Type0 =
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

let ubuffer_disjoint0 (#r1 #r2:HS.rid) (#a1 #a2:nat) (b1:ubuffer r1 a1) (b2:ubuffer r2 a2) =
  r1 == r2 /\ a1 == a2 /\
  ubuffer_disjoint' (G.reveal b1) (G.reveal b2)

val ubuffer_disjoint (#r:HS.rid) (#a:nat) (b1 b2:ubuffer r a) :GTot Type0
let ubuffer_disjoint #r #a b1 b2 = ubuffer_disjoint0 b1 b2

val ubuffer_disjoint_sym (#r:HS.rid) (#a: nat) (b1 b2:ubuffer r a)
  :Lemma (ubuffer_disjoint b1 b2 <==> ubuffer_disjoint b2 b1)
let ubuffer_disjoint_sym #_ #_ b1 b2 = ()

val ubuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: ubuffer r a) (smaller1 smaller2: ubuffer r a) : Lemma
  (requires (ubuffer_disjoint larger1 larger2 /\ larger1 `ubuffer_includes` smaller1 /\ larger2 `ubuffer_includes` smaller2))
  (ensures (ubuffer_disjoint smaller1 smaller2))

let ubuffer_disjoint_includes #r #a larger1 larger2 smaller1 smaller2 = ()

val liveness_preservation_intro (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (h h':HS.mem) (b:mbuffer a rrel rel)
  (f: (
    (t':Type0) ->
    (pre: Preorder.preorder t') ->
    (r: HS.mreference t' pre) ->
    Lemma
    (requires (HS.frameOf r == frameOf b /\ HS.as_addr r == as_addr b /\ h `HS.contains` r))
    (ensures (h' `HS.contains` r))
  ))
  :Lemma (requires (live h b)) (ensures (live h' b))

let liveness_preservation_intro #_ #_ #_ _ _ b f =
  if Null? b
  then ()
  else f _ _ (Buffer?.content b)

(* Basic, non-compositional modifies clauses, used only to implement the generic modifies clause. DO NOT USE in client code *)

let modifies_0_preserves_mreferences (h1 h2: HS.mem) : GTot Type0 =
  forall (a: Type) (pre: Preorder.preorder a) (r: HS.mreference a pre) .
  h1 `HS.contains` r ==> (h2 `HS.contains` r /\ HS.sel h1 r == HS.sel h2 r)

let modifies_0_preserves_regions (h1 h2: HS.mem) : GTot Type0 =
  forall (r: HS.rid) . HS.live_region h1 r ==> HS.live_region h2 r

let modifies_0_preserves_not_unused_in (h1 h2: HS.mem) : GTot Type0 =
  forall (r: HS.rid) (n: nat) . (
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)  
  ) ==> (
    n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
  )

let modifies_0' (h1 h2: HS.mem) : GTot Type0 =
  modifies_0_preserves_mreferences h1 h2 /\
  modifies_0_preserves_regions h1 h2 /\
  modifies_0_preserves_not_unused_in h1 h2

val modifies_0 (h1 h2: HS.mem) : GTot Type0

let modifies_0 = modifies_0'

val modifies_0_live_region (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_0 h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

let modifies_0_live_region h1 h2 r = ()

val modifies_0_mreference (#a: Type) (#pre: Preorder.preorder a) (h1 h2: HS.mem) (r: HS.mreference a pre) : Lemma
  (requires (modifies_0 h1 h2 /\ h1 `HS.contains` r))
  (ensures (h2 `HS.contains` r /\ h1 `HS.sel` r == h2 `HS.sel` r))

let modifies_0_mreference #a #pre h1 h2 r = ()

let modifies_0_ubuffer
  (#r: HS.rid)
  (#a: nat)
  (b: ubuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (ubuffer_preserved b h1 h2))
= same_mreference_ubuffer_preserved b h1 h2 (fun a' pre r' -> modifies_0_mreference h1 h2 r')

val modifies_0_unused_in
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_0 h1 h2 /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

let modifies_0_unused_in h1 h2 r n = ()

let modifies_1_preserves_mreferences (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :GTot Type0
  = forall (a':Type) (pre:Preorder.preorder a') (r':HS.mreference  a' pre).
      ((frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r') ==>
      (h2 `HS.contains` r' /\ HS.sel h1 r' == HS.sel h2 r')

let modifies_1_preserves_ubuffers (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = forall (b':ubuffer (frameOf b) (as_addr b)).
      (ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b') ==> ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2

let modifies_1_preserves_livenesses (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = forall (a':Type) (pre:Preorder.preorder a') (r':HS.mreference  a' pre). h1 `HS.contains` r' ==> h2 `HS.contains` r'

let modifies_1' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : GTot Type0
  = modifies_0_preserves_regions h1 h2 /\
    modifies_1_preserves_mreferences b h1 h2 /\
    modifies_1_preserves_livenesses b h1 h2 /\
    modifies_0_preserves_not_unused_in h1 h2 /\
    modifies_1_preserves_ubuffers b h1 h2

val modifies_1 (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0

let modifies_1 = modifies_1'

val modifies_1_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r)) (ensures (HS.live_region h2 r))

let modifies_1_live_region #_ #_ #_ _ _ _ _ = ()

val modifies_1_liveness
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  :Lemma (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r')) (ensures (h2 `HS.contains` r'))

let modifies_1_liveness #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_1_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  :Lemma (requires (modifies_1 b h1 h2 /\
                    HS.live_region h1 r /\ HS.live_region h2 r /\
                    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
         (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
let modifies_1_unused_in #_ #_ #_ _ _ _ _ _ = ()

val modifies_1_mreference
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r': HS.mreference a' pre)
  : Lemma (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
let modifies_1_mreference #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_1_ubuffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (b':ubuffer (frameOf b) (as_addr b))
  : Lemma (requires (modifies_1 b h1 h2 /\ ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b'))
          (ensures  (ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))
let modifies_1_ubuffer #_ #_ #_ _ _ _ _ = ()

val modifies_1_null (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  : Lemma (requires (modifies_1 b h1 h2 /\ g_is_null b))
          (ensures  (modifies_0 h1 h2))
let modifies_1_null #_ #_ #_ _ _ _ = ()

let modifies_addr_of_preserves_not_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :GTot Type0
  = forall (r: HS.rid) (n: nat) .
      ((r <> frameOf b \/ n <> as_addr b) /\
       HS.live_region h1 r /\ HS.live_region h2 r /\
       n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)) ==>
      (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r))

let modifies_addr_of' (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0 =
  modifies_0_preserves_regions h1 h2 /\
  modifies_1_preserves_mreferences b h1 h2 /\
  modifies_addr_of_preserves_not_unused_in b h1 h2

val modifies_addr_of (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) :GTot Type0
let modifies_addr_of = modifies_addr_of'

val modifies_addr_of_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_addr_of b h1 h2 /\ HS.live_region h1 r))
         (ensures (HS.live_region h2 r))
let modifies_addr_of_live_region #_ #_ #_ _ _ _ _ = ()

val modifies_addr_of_mreference (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  : Lemma (requires (modifies_addr_of b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
let modifies_addr_of_mreference #_ #_ #_ _ _ _ #_ #_ _ = ()

val modifies_addr_of_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  : Lemma (requires (modifies_addr_of b h1 h2 /\
                     (r <> frameOf b \/ n <> as_addr b) /\
                     HS.live_region h1 r /\ HS.live_region h2 r /\
                     n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
          (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
let modifies_addr_of_unused_in #_ #_ #_ _ _ _ _ _ = ()

module MG = FStar.ModifiesGen

let cls : MG.cls ubuffer = MG.Cls #ubuffer
  ubuffer_includes
  (fun #r #a x -> ubuffer_includes_refl x)
  (fun #r #a x1 x2 x3 -> ubuffer_includes_trans x1 x2 x3)
  ubuffer_disjoint
  (fun #r #a x1 x2 -> ubuffer_disjoint_sym x1 x2)
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ubuffer_disjoint_includes larger1 larger2 smaller1 smaller2)
  ubuffer_preserved
  (fun #r #a x h -> ubuffer_preserved_refl x h)
  (fun #r #a x h1 h2 h3 -> ubuffer_preserved_trans x h1 h2 h3)
  (fun #r #a b h1 h2 f -> same_mreference_ubuffer_preserved b h1 h2 f)

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

abstract val loc :Type0
let loc = MG.loc cls

abstract val loc_none :loc
let loc_none = MG.loc_none

abstract val loc_union (s1 s2: loc) :GTot loc
let loc_union = MG.loc_union

abstract val loc_union_idem (s:loc) :Lemma (loc_union s s == s)
                                           [SMTPat (loc_union s s)]
let loc_union_idem = MG.loc_union_idem

abstract val loc_union_comm (s1 s2:loc) :Lemma (loc_union s1 s2 == loc_union s2 s1)
                                               [SMTPat (loc_union s1 s2)]
let loc_union_comm = MG.loc_union_comm

abstract val loc_union_assoc (s1 s2 s3:loc) :Lemma (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)
let loc_union_assoc = MG.loc_union_assoc

let loc_union_idem_1 (s1 s2:loc)
  :Lemma (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
         [SMTPat (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)]
  = loc_union_assoc s1 s1 s2

let loc_union_idem_2 (s1 s2:loc)
  :Lemma (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
         [SMTPat (loc_union (loc_union s1 s2) s2)]
  = loc_union_assoc s1 s2 s2

abstract val loc_union_loc_none_l (s:loc) :Lemma (loc_union loc_none s == s)
                                                 [SMTPat (loc_union loc_none s)]
let loc_union_loc_none_l = MG.loc_union_loc_none_l

abstract val loc_union_loc_none_r (s:loc) :Lemma (loc_union s loc_none == s)
                                                 [SMTPat (loc_union s loc_none)]
let loc_union_loc_none_r = MG.loc_union_loc_none_r


/// ``loc_buffer b`` is the set of memory locations associated to a buffer ``b``.

abstract val loc_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot loc
let loc_buffer #_ #_ #_ b =
  if g_is_null b then MG.loc_none
  else MG.loc_of_aloc #_ #_ #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

abstract val loc_buffer_null (a:Type0) (rrel:srel a) (rel:srel a)  (* TODO: candidate for wrapper *)
  :Lemma (loc_buffer (null #a #rrel #rel) == loc_none)
         [SMTPat (loc_buffer (null #a #rrel #rel))]
let loc_buffer_null _ _ _ = ()


/// ``loc_addresses r n`` is the set of memory locations associated to a
/// set of addresses ``n`` in a given region ``r``.

abstract val loc_addresses (preserve_liveness:bool) (r:HS.rid) (n:Set.set nat) :GTot loc
let loc_addresses = MG.loc_addresses

unfold let loc_addr_of_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) :GTot loc =
  loc_addresses false (frameOf b) (Set.singleton (as_addr b))


/// ``loc_regions r`` is the set of memory locations associated to a set
/// ``r`` of regions.

abstract val loc_regions (preserve_liveness:bool) (r:Set.set HS.rid) :GTot loc
let loc_regions = MG.loc_regions


/// ``loc_mreference b`` is the set of memory locations associated to a
/// reference ``b``, which is actually the set of memory locations
/// associated to the address of ``b``.

unfold let loc_mreference (#a:Type0) (#p:Preorder.preorder a) (b:HS.mreference a p) :GTot loc
  = loc_addresses true (HS.frameOf b) (Set.singleton (HS.as_addr b))

unfold
let loc_freed_mreference (#a:Type0) (#p:Preorder.preorder a) (b:HS.mreference a p) :GTot loc
  = loc_addresses false (HS.frameOf b) (Set.singleton (HS.as_addr b))


/// ``loc_region_only r`` is the set of memory locations associated to a
/// region ``r`` but not any region ``r'`` that extends ``r`` (in the sense
/// of ``FStar.HyperStack.extends``.)

unfold
let loc_region_only (preserve_liveness:bool) (r:HS.rid) :GTot loc
  = loc_regions preserve_liveness (Set.singleton r)


/// ``loc_all_regions_from r`` is the set of all memory locations
/// associated to a region ``r`` and any region ``r'`` that transitively
/// extends ``r`` (in the sense of ``FStar.HyperStack.extends``,
/// e.g. nested stack frames.)

unfold
let loc_all_regions_from (preserve_liveness:bool) (r:HS.rid) :GTot loc
  = loc_regions preserve_liveness (HS.mod_set (Set.singleton r))


/// We equip the ``loc`` monoid of sets of memory locations with an
/// inclusion relation, ``loc_includes``, which is a preorder compatible
/// with ``loc_union``. Although we consider sets of memory locations,
/// we do not specify them using any F* set library such as
/// ``FStar.Set``, ``FStar.TSet`` or ``FStar.GSet``, because ``loc_includes``
/// encompasses more than just set-theoretic inclusion.

abstract val loc_includes (s1 s2:loc) :GTot Type0
let loc_includes = MG.loc_includes

abstract val loc_includes_refl (s:loc)
  :Lemma (loc_includes s s)
         [SMTPat (loc_includes s s)]
let loc_includes_refl = MG.loc_includes_refl

abstract val loc_includes_trans (s1 s2 s3:loc)
  :Lemma (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
         (ensures (loc_includes s1 s3))
let loc_includes_trans = MG.loc_includes_trans

let loc_includes_trans_backwards (s1 s2 s3:loc)
  :Lemma (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
         (ensures  (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]
  = loc_includes_trans s1 s2 s3

abstract val loc_includes_union_r (s s1 s2:loc)
  :Lemma (requires (loc_includes s s1 /\ loc_includes s s2))
         (ensures (loc_includes s (loc_union s1 s2)))
let loc_includes_union_r = MG.loc_includes_union_r

abstract val loc_includes_union_l (s1 s2 s:loc)
  :Lemma (requires (loc_includes s1 s \/ loc_includes s2 s))
         (ensures (loc_includes (loc_union s1 s2) s))
let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_union_r' (s s1 s2:loc)
  :Lemma (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
         [SMTPat (loc_includes s (loc_union s1 s2))]
  = Classical.move_requires (loc_includes_union_r s s1) s2;
    Classical.move_requires (loc_includes_union_l s1 s2) s1;
    Classical.move_requires (loc_includes_union_l s1 s2) s2;
    Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s1;
    Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s2

abstract val loc_includes_none (s:loc)
  :Lemma (loc_includes s loc_none)
         [SMTPat (loc_includes s loc_none)]
let loc_includes_none = MG.loc_includes_none

private abstract val loc_includes_buffer (#a:Type0) (#rrel1:srel a) (#rrel2:srel a) (#rel1:srel a) (#rel2:srel a)
  (b1:mbuffer a rrel1 rel1) (b2:mbuffer a rrel2 rel2)
  :Lemma (requires (frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2 /\
                    ubuffer_includes0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures  (loc_includes (loc_buffer b1) (loc_buffer b2)))

let loc_includes_buffer #t #_ #_ #_ #_ b1 b2 =
  let t1 = ubuffer (frameOf b1) (as_addr b1) in
  MG.loc_includes_aloc #_ #cls #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2 <: t1)

/// If a buffer ``b1`` includes a buffer ``b2`` in the sense of the buffer
/// theory (see ``LowStar.Buffer.includes``), then so are their
/// corresponding sets of memory locations.

abstract val loc_includes_gsub_buffer_r
  (l:loc)
  (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt32.t) (len:UInt32.t) (sub_rel:srel a)
: Lemma (requires (UInt32.v i + UInt32.v len <= (length b) /\
                   compatible_sub b i len sub_rel /\
                   loc_includes l (loc_buffer b)))
        (ensures  (loc_includes l (loc_buffer (gsub b i len sub_rel))))
        [SMTPat (loc_includes l (loc_buffer (gsub b i len sub_rel)))]
let loc_includes_gsub_buffer_r l #_ #_ #_ b i len sub_rel =
  let b' = gsub b i len sub_rel in
  loc_includes_buffer b b';
  loc_includes_trans l (loc_buffer b) (loc_buffer b')

let loc_includes_gsub_buffer_r' (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt32.t) (len:UInt32.t) (sub_rel:srel a)
  :Lemma (requires (UInt32.v i + UInt32.v len <= (length b) /\ compatible_sub b i len sub_rel))
         (ensures  (loc_includes (loc_buffer b) (loc_buffer (gsub b i len sub_rel))))
         [SMTPat (gsub b i len sub_rel)]
  = ()

val loc_includes_gsub_buffer_l (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (i1:UInt32.t) (len1:UInt32.t) (sub_rel1:srel a)
  (i2:UInt32.t) (len2:UInt32.t) (sub_rel2:srel a)
  :Lemma (requires (UInt32.v i1 + UInt32.v len1 <= (length b) /\
                    UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\
		    compatible_sub b i1 len1 sub_rel1 /\ compatible_sub b i2 len2 sub_rel2))
         (ensures  (loc_includes (loc_buffer (gsub b i1 len1 sub_rel1)) (loc_buffer (gsub b i2 len2 sub_rel2))))
         [SMTPat (gsub b i1 len1 sub_rel1); SMTPat (gsub b i2 len2 sub_rel2)]
let loc_includes_gsub_buffer_l #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  let b1 = gsub b i1 len1 sub_rel1 in
  let b2 = gsub b i2 len2 sub_rel2 in
  //lemma_sub_compatibility_is_transitive1 (length b) rel (U32.v i1) (U32.v len1) sub_rel1 (U32.v i2) (U32.v len2) sub_rel2;
  //let b2 = gsub b1 (U32.sub i2 i1) len2 sub_rel2 in
  loc_includes_buffer b1 b2

/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val loc_includes_as_seq (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (h1 h2:HS.mem) (larger:mbuffer a rrel1 rel1) (smaller:mbuffer a rrel2 rel2)
  :Lemma (requires (loc_includes (loc_buffer larger) (loc_buffer smaller) /\
                    as_seq h1 larger == as_seq h2 larger /\
		    (live h1 larger \/ live h1 smaller) /\ (live h2 larger \/ live h2 smaller)))
         (ensures  (as_seq h1 smaller == as_seq h2 smaller))
#push-options "--z3rlimit 20"
let loc_includes_as_seq #_ #rrel1 #rrel2 #_ #_ h1 h2 larger smaller =
  if Null? smaller then () else
  if Null? larger then begin
    MG.loc_includes_none_elim (loc_buffer smaller);
    MG.loc_of_aloc_not_none #_ #cls #(frameOf smaller) #(as_addr smaller) (ubuffer_of_buffer smaller)
  end else begin
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller);
    assume (rrel1 == rrel2);  //TODO: we should be able to prove this somehow in HS?
    let ul = Ghost.reveal (ubuffer_of_buffer larger) in
    let us = Ghost.reveal (ubuffer_of_buffer smaller) in
    assert (as_seq h1 smaller == Seq.slice (as_seq h1 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller));
    assert (as_seq h2 smaller == Seq.slice (as_seq h2 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller))
  end
#pop-options


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
let loc_includes_addresses_buffer #_ #_ #_ preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(as_addr p) (ubuffer_of_buffer p)

let loc_includes_addresses_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_addresses true (frameOf b) (Set.singleton (as_addr b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()

/// The set of memory locations corresponding to a buffer is included
/// in the set of memory locations corresponding to its region.

val loc_includes_region_buffer (#a:Type0) (#rrel #rel:srel a)
  (preserve_liveness:bool) (s:Set.set HS.rid) (b:mbuffer a rrel rel)
  :Lemma (requires (Set.mem (frameOf b) s))
         (ensures (loc_includes (loc_regions preserve_liveness s) (loc_buffer b)))
         [SMTPat (loc_includes (loc_regions preserve_liveness s) (loc_buffer b))]
let loc_includes_region_buffer #_ #_ #_ preserve_liveness s b =
  MG.loc_includes_region_aloc #_ #cls preserve_liveness s #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_includes_region_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_regions true (Set.singleton (frameOf b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()


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
let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_addresses'
  (preserve_liveness: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (loc_includes (loc_regions true (Set.singleton r)) (loc_addresses preserve_liveness r a))
  [SMTPat (loc_addresses preserve_liveness r a)]
= ()

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
let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_region'
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions false s) (loc_regions preserve_liveness s))
  [SMTPat (loc_regions preserve_liveness s)]
= ()

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
let loc_includes_region_union_l = MG.loc_includes_region_union_l


/// If a set of addresses ``s1`` includes a set of addresses ``s2``,
/// then so are their corresponding memory locations
val loc_includes_addresses_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r s1) (loc_addresses preserve_liveness2 r s2)))
let loc_includes_addresses_addresses = MG.loc_includes_addresses_addresses cls

let loc_includes_addresses_addresses_1
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires (r1 == r2 /\ (preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2)))
  [SMTPat (loc_includes (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2))]
= loc_includes_addresses_addresses preserve_liveness1 preserve_liveness2 r1 s1 s2

let loc_includes_addresses_addresses_2
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
: Lemma
  (loc_includes (loc_addresses false r s) (loc_addresses preserve_liveness r s))
  [SMTPat (loc_addresses preserve_liveness r s)]
= ()

/// Patterns with loc_includes, union on the left

let loc_includes_union_l_buffer
  (s1 s2:loc)
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  :Lemma (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
         (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
         [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]
  = loc_includes_union_l s1 s2 (loc_buffer b)

let loc_includes_union_l_addresses
  (s1 s2: loc)
  (prf: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (loc_includes s1 (loc_addresses prf r a) \/ loc_includes s2 (loc_addresses prf r a)))
  (ensures (loc_includes (loc_union s1 s2) (loc_addresses prf r a)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_addresses prf r a))]
= loc_includes_union_l s1 s2 (loc_addresses prf r a)

let loc_includes_union_l_regions
  (s1 s2: loc)
  (prf: bool)
  (r: Set.set HS.rid)
: Lemma
  (requires (loc_includes s1 (loc_regions prf r) \/ loc_includes s2 (loc_regions prf r)))
  (ensures (loc_includes (loc_union s1 s2) (loc_regions prf r)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_regions prf r))]
= loc_includes_union_l s1 s2 (loc_regions prf r)

/// Since inclusion encompasses more than just set-theoretic
/// inclusion, we also need to specify disjointness accordingly, as a
/// symmetric relation compatible with union.

val loc_disjoint
  (s1 s2: loc)
: GTot Type0
let loc_disjoint = MG.loc_disjoint

[@"opaque_to_smt"]
private let rec loc_disjoint_from_list (l:loc) (ls:list loc) :Type0 =
  match ls with
  | []    -> True
  | hd::tl -> loc_disjoint l hd /\ loc_disjoint_from_list l tl

[@"opaque_to_smt"]
private let rec loc_pairwise_disjoint_aux (l:list loc) :Type0 =
  match l with
  | []    -> True
  | hd::tl -> loc_disjoint_from_list hd tl /\ loc_pairwise_disjoint_aux tl

(*
 * Use this to state pairwise disjointness for the locations in l
 * It is unfolded to conjunction of loc_disjoint for all pairs of locations in l
 *)
[@"opaque_to_smt"]
unfold let loc_pairwise_disjoint (l:list loc) :Type0 =
  norm [iota; zeta; delta; delta_only ["LowStar.Buffer.loc_disjoint_from_list";
                                       "LowStar.Buffer.loc_pairwise_disjoint_aux"]] (loc_pairwise_disjoint_aux l)

val loc_disjoint_sym
  (s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]
= Classical.move_requires (loc_disjoint_sym s1) s2;
  Classical.move_requires (loc_disjoint_sym s2) s1

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]
let loc_disjoint_none_r = MG.loc_disjoint_none_r

val loc_disjoint_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))
let loc_disjoint_union_r = MG.loc_disjoint_union_r


/// If two sets of memory locations are disjoint, then so are any two
/// included sets of memory locations.

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))
let loc_disjoint_includes = MG.loc_disjoint_includes

let loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]
= Classical.move_requires (loc_disjoint_union_r s s1) s2;
  loc_includes_union_l s1 s2 s1;
  loc_includes_union_l s1 s2 s2;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s1;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s2

let loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]
= loc_disjoint_includes b1 b2 b1 b2'

val loc_disjoint_buffer (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires ((frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2) ==>
                    ubuffer_disjoint0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))
let loc_disjoint_buffer #_ #_ #_ #_ #_ #_ b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

val loc_disjoint_gsub_buffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel)
  (i1:UInt32.t) (len1:UInt32.t) (sub_rel1:srel a)
  (i2:UInt32.t) (len2:UInt32.t) (sub_rel2:srel a)
  :Lemma (requires (UInt32.v i1 + UInt32.v len1 <= (length b) /\
                    UInt32.v i2 + UInt32.v len2 <= (length b) /\
		    compatible_sub b i1 len1 sub_rel1 /\ compatible_sub b i2 len2 sub_rel2 /\
		    (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
                     UInt32.v i2 + UInt32.v len2 <= UInt32.v i1)))
         (ensures  (loc_disjoint (loc_buffer (gsub b i1 len1 sub_rel1)) (loc_buffer (gsub b i2 len2 sub_rel2))))
         [SMTPat (gsub b i1 len1 sub_rel1); SMTPat (gsub b i2 len2 sub_rel2)]
let loc_disjoint_gsub_buffer #_ #_ #_ b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  loc_disjoint_buffer (gsub b i1 len1 sub_rel1) (gsub b i2 len2 sub_rel2)


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
let loc_disjoint_addresses = MG.loc_disjoint_addresses_intro #_ #cls


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
let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

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
let modifies = MG.modifies


/// If a region ``r`` is disjoint from a set ``s`` of memory locations
/// which is modified, then its liveness is preserved.

val modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
let modifies_live_region = MG.modifies_live_region

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
let modifies_mreference_elim = MG.modifies_mreference_elim

/// If a buffer ``b`` is disjoint from a set ``p`` of
/// memory locations which is modified, then its liveness and contents
/// are preserved.

val modifies_buffer_elim (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (p:loc) (h h':HS.mem)
  :Lemma (requires (loc_disjoint (loc_buffer b) p /\ live h b /\ modifies p h h'))
         (ensures  (live h' b /\ (as_seq h b == as_seq h' b)))
let modifies_buffer_elim #_ #_ #_ b p h h' =
  if g_is_null b
  then
    assert (as_seq h b `Seq.equal` as_seq h' b)
  else begin
    MG.modifies_aloc_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) p h h' ;
    ubuffer_preserved_elim b h h'
  end

/// If the memory state does not change, then any memory location is
/// modified (and, in particular, the empty set, ``loc_none``.)

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]
let modifies_refl = MG.modifies_refl

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
let modifies_loc_includes = MG.modifies_loc_includes

/// Some memory locations are tagged as liveness-insensitive: the
/// liveness preservation of a memory location only depends on its
/// disjointness from the liveness-sensitive memory locations of a
/// modifies clause.

val address_liveness_insensitive_locs: loc
let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _

val region_liveness_insensitive_locs: loc
let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

val address_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))
         [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))]
let address_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

val address_liveness_insensitive_addresses (r: HS.rid) (a: Set.set nat) : Lemma
  (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))
  [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))]
let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

val region_liveness_insensitive_buffer (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))
         [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))]
let region_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

val region_liveness_insensitive_addresses (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))]
let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

val region_liveness_insensitive_regions (rs: Set.set HS.rid) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))]
let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

val region_liveness_insensitive_address_liveness_insensitive:
  squash (region_liveness_insensitive_locs `loc_includes` address_liveness_insensitive_locs)
let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

val modifies_liveness_insensitive_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ address_liveness_insensitive_locs `loc_includes` l2 /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  (* TODO: pattern *)
let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

val modifies_liveness_insensitive_buffer
  (l1 l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_buffer x) /\ address_liveness_insensitive_locs `loc_includes` l2 /\ live h x))
         (ensures  (live h' x))
  (* TODO: pattern *)
let modifies_liveness_insensitive_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x
  then ()
  else
    liveness_preservation_intro h h' x (fun t' pre r ->
      MG.modifies_preserves_liveness_strong l1 l2 h h' r (ubuffer_of_buffer x)
    )

let modifies_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
= modifies_liveness_insensitive_mreference loc_none l h h' x

let modifies_liveness_insensitive_buffer_weak
  (l:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ live h x))
         (ensures  (live h' x))
  = modifies_liveness_insensitive_buffer loc_none l h h' x

val modifies_liveness_insensitive_region
  (l1 l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_region_only false x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  (* TODO: pattern *)
let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

val modifies_liveness_insensitive_region_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  (* TODO: pattern *)
let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

val modifies_liveness_insensitive_region_buffer
  (l1 l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_buffer x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
  (* TODO: pattern *)
let modifies_liveness_insensitive_region_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x
  then ()
  else
    MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(frameOf x) #(as_addr x) (ubuffer_of_buffer x)

let modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
= modifies_liveness_insensitive_region loc_none l2 h h' x

let modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
= modifies_liveness_insensitive_region_mreference loc_none l2 h h' x

let modifies_liveness_insensitive_region_buffer_weak
  (l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
  = modifies_liveness_insensitive_region_buffer loc_none l2 h h' x


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
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]
let modifies_trans = MG.modifies_trans

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
let modifies_only_live_regions = MG.modifies_only_live_regions

/// As a consequence, fresh regions can be removed from modifies
/// clauses.

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]
let no_upd_fresh_region = MG.no_upd_fresh_region

val fresh_frame_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies loc_none h0 h1))
let fresh_frame_modifies = MG.fresh_frame_modifies #_ cls

val new_region_modifies (m0: HS.mem) (r0: HS.rid) (col: option int) : Lemma
  (requires (HST.is_eternal_region r0 /\ HS.live_region m0 r0 /\ (None? col \/ HS.is_eternal_color (Some?.v col))))
  (ensures (
    let (_, m1) = HS.new_eternal_region m0 r0 col in
    modifies loc_none m0 m1
  ))
  [SMTPat (HS.new_eternal_region m0 r0 col)]
let new_region_modifies = MG.new_region_modifies #_ cls

val popped_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies (loc_region_only false (HS.get_tip h0)) h0 h1))
let popped_modifies = MG.popped_modifies #_ cls

/// Stack discipline: any stack frame (and all its transitively
/// extending regions) that is pushed, modified and popped can be
/// removed from a modifies clause.

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
  [SMTPat (HS.fresh_frame h0 h1); SMTPat (HS.popped h2 h3); SMTPat (modifies s h0 h3)]
let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped


/// Compatibility lemmas to rescue modifies clauses specified in the
/// standard F* HyperStack library.

val modifies_loc_regions_intro
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions true rs) h1 h2))
let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

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
let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro #_ #cls

/// Modifies clauses for allocating a reference: nothing is
/// modified. (In particular, a modifies clause does not track
/// memory locations that are created.)

val modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.ralloc_post i init h x h')]
let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

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
let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

/// Modifies clause for freeing a reference: the address is modified.

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference r) m (HS.free r m))
  [SMTPat (HS.free r m)]
let modifies_free = MG.modifies_free #_ #cls

/// Another compatibility lemma

val modifies_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))
  [SMTPat (HST.modifies_none h1 h2)]
let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

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
let modifies_upd = MG.modifies_upd #_ #cls

val modifies_0_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (modifies loc_none h1 h2))

let modifies_0_modifies h1 h2 =
  MG.modifies_none_intro #_ #cls h1 h2
    (fun r -> modifies_0_live_region h1 h2 r)
    (fun t pre b -> modifies_0_mreference #t #pre h1 h2 b)
    (fun r n -> modifies_0_unused_in h1 h2 r n)

val modifies_1_modifies
  (#a:Type0)(#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :Lemma (requires (modifies_1 b h1 h2))
         (ensures  (modifies (loc_buffer b) h1 h2))
let modifies_1_modifies #t #_ #_ b h1 h2 =
  if g_is_null b
  then begin
    modifies_1_null b h1 h2;
    modifies_0_modifies h1 h2
  end else
   MG.modifies_intro (loc_buffer b) h1 h2
    (fun r -> modifies_1_live_region b h1 h2 r)
    (fun t pre p ->
      loc_disjoint_sym (loc_mreference p) (loc_buffer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) true (HS.frameOf p) (Set.singleton (HS.as_addr p));
      modifies_1_mreference b h1 h2 p
    )
    (fun t pre p ->
      modifies_1_liveness b h1 h2 p
    )
    (fun r n ->
      modifies_1_unused_in b h1 h2 r n
    )
    (fun r' a' b' ->
      loc_disjoint_sym (MG.loc_of_aloc b') (loc_buffer b);
      MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b) #(as_addr b)  #r' #a' (ubuffer_of_buffer b)  b';
      if frameOf b = r' && as_addr b = a'
      then
        modifies_1_ubuffer #t b h1 h2 b'
      else
        same_mreference_ubuffer_preserved #r' #a' b' h1 h2
          (fun a_ pre_ r_ -> modifies_1_mreference b h1 h2 r_)
    )

val modifies_addr_of_modifies
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  :Lemma (requires (modifies_addr_of b h1 h2))
         (ensures  (modifies (loc_addr_of_buffer b) h1 h2))
let modifies_addr_of_modifies #t #_ #_ b h1 h2 =
  MG.modifies_address_intro #_ #cls (frameOf b) (as_addr b) h1 h2
    (fun r -> modifies_addr_of_live_region b h1 h2 r)
    (fun t pre p ->
      modifies_addr_of_mreference b h1 h2 p
    )
    (fun r n ->
      modifies_addr_of_unused_in b h1 h2 r n
    )


///  A memory ``h`` does not contain address ``a`` in region ``r``, denoted
///  ``does_not_contain_addr h (r, a)``, only if, either region ``r`` is
///  not live, or address ``a`` is unused in region ``r``.

(* BEGIN TODO: move to FStar.Monotonic.HyperStack *)

val does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: GTot Type0
let does_not_contain_addr = MG.does_not_contain_addr

val not_live_region_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (~ (HS.live_region h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))
let not_live_region_does_not_contain_addr = MG.not_live_region_does_not_contain_addr

val unused_in_does_not_contain_addr
  (h: HS.mem)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (h `does_not_contain_addr` (HS.frameOf r, HS.as_addr r)))
let unused_in_does_not_contain_addr = MG.unused_in_does_not_contain_addr

val addr_unused_in_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (fst ra))))
  (ensures (h `does_not_contain_addr` ra))
let addr_unused_in_does_not_contain_addr = MG.addr_unused_in_does_not_contain_addr

val free_does_not_contain_addr
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
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
let free_does_not_contain_addr = MG.free_does_not_contain_addr

val does_not_contain_addr_elim
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
: Lemma
  (requires (
    m `does_not_contain_addr` x /\
    HS.frameOf r == fst x /\
    HS.as_addr r == snd x
  ))
  (ensures (~ (m `HS.contains` r)))
let does_not_contain_addr_elim = MG.does_not_contain_addr_elim

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
let modifies_only_live_addresses = MG.modifies_only_live_addresses


(* Generic way to ensure that a buffer just allocated is disjoint from
   any other object, however the latter's liveness is defined. *)

val loc_not_unused_in (h: HS.mem) : GTot loc
let loc_not_unused_in = MG.loc_not_unused_in _

val loc_unused_in (h: HS.mem) : GTot loc
let loc_unused_in = MG.loc_unused_in _

val loc_unused_in_not_unused_in_disjoint (h: HS.mem) : Lemma
  (loc_disjoint (loc_unused_in h) (loc_not_unused_in h))
let loc_unused_in_not_unused_in_disjoint =
  MG.loc_unused_in_not_unused_in_disjoint cls

val not_live_region_loc_not_unused_in_disjoint
  (h0: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (~ (HS.live_region h0 r)))
  (ensures (loc_disjoint (loc_region_only false r) (loc_not_unused_in h0)))
let not_live_region_loc_not_unused_in_disjoint = MG.not_live_region_loc_not_unused_in_disjoint cls

let fresh_frame_loc_not_unused_in_disjoint
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (loc_disjoint (loc_region_only false (HS.get_tip h1)) (loc_not_unused_in h0)))
  [SMTPat (HS.fresh_frame h0 h1)]
= not_live_region_loc_not_unused_in_disjoint h0 (HS.get_tip h1)

val live_loc_not_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b))
         (ensures  (loc_not_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (live h b)]
let live_loc_not_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.does_not_contain_addr_addr_unused_in h) (frameOf b, as_addr b);
  MG.loc_addresses_not_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

val unused_in_loc_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (unused_in b h))
         (ensures  (loc_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (unused_in b h)]
let unused_in_loc_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.addr_unused_in_does_not_contain_addr h) (frameOf b, as_addr b);
  MG.loc_addresses_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

val modifies_address_liveness_insensitive_unused_in
  (h h' : HS.mem)
: Lemma
  (requires (modifies (address_liveness_insensitive_locs) h h'))
  (ensures (loc_not_unused_in h' `loc_includes` loc_not_unused_in h /\ loc_unused_in h `loc_includes` loc_unused_in h'))
let modifies_address_liveness_insensitive_unused_in =
  MG.modifies_address_liveness_insensitive_unused_in cls

/// Addresses that have not been allocated yet can be removed from
/// modifies clauses.

val modifies_only_not_unused_in
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_union (loc_unused_in h) l) h h'))
  (ensures (modifies l h h'))
let modifies_only_not_unused_in = MG.modifies_only_not_unused_in

val mreference_live_loc_not_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in h `loc_includes` loc_mreference r))
  [SMTPat (HS.contains h r)]
let mreference_live_loc_not_unused_in =
  MG.mreference_live_loc_not_unused_in cls

val mreference_unused_in_loc_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in h `loc_includes` loc_freed_mreference r /\ loc_unused_in h `loc_includes` loc_mreference r))
  [SMTPat (HS.unused_in r h)]
let mreference_unused_in_loc_unused_in =
  MG.mreference_unused_in_loc_unused_in cls


let unused_in_not_unused_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_not_unused_in h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2)]
= loc_includes_trans (loc_unused_in h) l1 l1' ;
  loc_includes_trans (loc_not_unused_in h) l2 l2'  ;
  loc_unused_in_not_unused_in_disjoint h ;
  loc_disjoint_includes (loc_unused_in h) (loc_not_unused_in h) l1' l2' 


(* Duplicate the modifies clause to cope with cases that must not be used with transitivity *)

val modifies_inert
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
let modifies_inert = modifies

val modifies_inert_intro
  (s: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies s h1 h2))
  (ensures (modifies_inert s h1 h2))
  [SMTPat (modifies s h1 h2)]
let modifies_inert_intro s h1 h2 = ()

val modifies_inert_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies_inert s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]
let modifies_inert_live_region = modifies_live_region

val modifies_inert_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies_inert p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h' b) ]
  ] ]
let modifies_inert_mreference_elim = modifies_mreference_elim

val modifies_inert_buffer_elim (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (p:loc)
  (h h':HS.mem)
  :Lemma (requires (loc_disjoint (loc_buffer b) p /\
                    live h b /\
                    modifies_inert p h h'))
         (ensures  (live h' b /\ (as_seq h b == as_seq h' b)))
         [SMTPatOr [
             [ SMTPat (modifies_inert p h h'); SMTPat (as_seq h b) ] ;
             [ SMTPat (modifies_inert p h h'); SMTPat (live h b) ];
             [ SMTPat (modifies_inert p h h'); SMTPat (as_seq h' b) ] ;
             [ SMTPat (modifies_inert p h h'); SMTPat (live h' b) ]
         ] ]
let modifies_inert_buffer_elim = modifies_buffer_elim

val modifies_inert_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies_inert l h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies_inert l h h');];
  ]]
let modifies_inert_liveness_insensitive_mreference_weak = modifies_liveness_insensitive_mreference_weak

val modifies_inert_liveness_insensitive_buffer_weak
  (l:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ live h x))
         (ensures (live h' x))
         [SMTPatOr [
             [SMTPat (live h x); SMTPat (modifies_inert l h h');];
             [SMTPat (live h' x); SMTPat (modifies_inert l h h');];
         ]]
let modifies_inert_liveness_insensitive_buffer_weak = modifies_liveness_insensitive_buffer_weak

val modifies_inert_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' x)];
  ]]
let modifies_inert_liveness_insensitive_region_weak = modifies_liveness_insensitive_region_weak

val modifies_inert_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]
let modifies_inert_liveness_insensitive_region_mreference_weak = modifies_liveness_insensitive_region_mreference_weak

val modifies_inert_liveness_insensitive_region_buffer_weak
  (l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
         [SMTPatOr [
             [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (frameOf x))];
             [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (frameOf x))];
         ]]
let modifies_inert_liveness_insensitive_region_buffer_weak = modifies_liveness_insensitive_region_buffer_weak

val fresh_frame_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies_inert loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]
let fresh_frame_modifies_inert = fresh_frame_modifies

val popped_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies_inert (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]
let popped_modifies_inert = popped_modifies

val modifies_inert_loc_unused_in
  (l: loc)
  (h1 h2: HS.mem)
  (l' : loc)
: Lemma
  (requires (
    modifies_inert l h1 h2 /\
    address_liveness_insensitive_locs `loc_includes` l /\
    loc_unused_in h2 `loc_includes` l'
  ))
  (ensures (loc_unused_in h1 `loc_includes` l'))
  [SMTPat (modifies_inert l h1 h2); SMTPat (loc_unused_in h2 `loc_includes` l')]
let modifies_inert_loc_unused_in l h1 h2 l' =
  modifies_loc_includes address_liveness_insensitive_locs h1 h2 l;
  modifies_address_liveness_insensitive_unused_in h1 h2;
  loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'

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
let disjoint_neq #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()

/// The liveness of a sub-buffer is exactly equivalent to the liveness
/// of its enclosing buffer.

val includes_live (#a:Type0) (#rrel #rel1 #rel2:srel a)
  (h:HS.mem) (larger:mbuffer a rrel rel1) (smaller:mbuffer a rrel rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures  (live h larger <==> live h smaller))
         [SMTPatOr [
             [SMTPat (includes larger smaller); SMTPat (live h larger)];
             [SMTPat (includes larger smaller); SMTPat (live h smaller)];
         ]]
let includes_live #a #rrel #rel1 #rel2 h larger smaller =
  if Null? larger || Null? smaller
  then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

val includes_frameOf_as_addr (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
         [SMTPat (larger `includes` smaller)]
let includes_frameOf_as_addr #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller
  then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)


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
let pointer_distinct_sel_disjoint #a #_ #_ #_ #_ b1 b2 h =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then begin
    HS.mreference_distinct_sel_disjoint h (Buffer?.content b1) (Buffer?.content b2);
    loc_disjoint_buffer b1 b2
  end
  else
    loc_disjoint_buffer b1 b2
	 
/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// The nullity test, ``is_null b``, which KreMLin compiles to C as ``b == NULL``.

val is_null (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack bool (requires (fun h -> live h b))
                  (ensures  (fun h y h' -> h == h' /\ y == g_is_null b))
let is_null #_ #_ #_ b = Null? b

/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KreMLin extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val sub (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (i:U32.t) (len:U32.t) (sub_rel:srel a)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U32.v i + U32.v len <= length b /\ compatible_sub b i len sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i len sub_rel))
let sub #a #rrel #rel b i len sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len0 () ->
    lemma_sub_compatibility_is_transitive (U32.v max_len) rrel (U32.v i0) (U32.v len0) rel (U32.v i) (U32.v len) sub_rel;
    Buffer max_len content (U32.add i0 i) len ()

/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U32.sub (len b) i``. KreMLin compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val offset (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (i:U32.t) (sub_rel:srel a)
  :HST.Stack (mbuffer a rrel sub_rel)
             (requires (fun h -> U32.v i <= length b /\ compatible_sub b i (U32.sub (len b) i) sub_rel /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (len b) i) sub_rel))
let offset #a #rrel #rel b i sub_rel =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len () ->
    lemma_sub_compatibility_is_transitive (U32.v max_len) rrel (U32.v i0) (U32.v len) rel (U32.v i) (U32.v (U32.sub len i)) sub_rel;
    Buffer max_len content (U32.add i0 i) (U32.sub len i) ()

/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KreMLin compiles it as b[i].
val index (#a:Type0)(#rrel #rel:srel a) (b:mbuffer a rrel rel) (i:U32.t)
  :HST.Stack a (requires (fun h -> live h b /\ U32.v i < length b))
               (ensures  (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))
let index #_ #_ #_ b i =
  let open HST in
  let s = ! (Buffer?.content b) in
  Seq.index s (U32.v (Buffer?.idx b) + U32.v i)

/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

/// ``g_upd_seq b s h`` updates the entire buffer `b`'s contents in
/// heap `h` to correspond to the sequence `s`
val g_upd_seq (#a:Type0) (#rrel #rel:srel a)
              (b:mbuffer a rrel rel) (s:Seq.lseq a (length b))
	      (h:HS.mem{live h b /\ rel (as_seq h b) s})
  :GTot HS.mem
let g_upd_seq #_ #_ #_ b s h =
  if Seq.length s = 0 then h
  else
    let s0 = HS.sel h (Buffer?.content b) in
    HS.upd h (Buffer?.content b) (replace_subseq s0 (U32.v (Buffer?.idx b)) (length b) s)

/// A lemma specifying `g_upd_seq` in terms of its effect on the
/// buffer's underlying sequence
val g_upd_seq_as_seq (#a:Type0) (#rrel #rel:srel a)
                     (b:mbuffer a rrel rel)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b /\ rel (as_seq h b) s})
  : Lemma (let h' = g_upd_seq b s h in
           (Seq.length s > 0 ==> not (g_is_null b)) /\
           modifies (loc_buffer b) h h' /\
           live h' b /\
           as_seq h' b == s)
#push-options "--z3rlimit 32"
let g_upd_seq_as_seq #_ #_ #_ b s h =
  let h' = g_upd_seq b s h in
  if g_is_null b then assert (Seq.equal s Seq.empty)
  else begin
    assert (Seq.equal (as_seq h' b) s);
    // prove modifies_1_preserves_ubuffers
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Seq.lemma_equal_instances_implies_equal_types ();
    modifies_1_modifies b h h'
  end
#pop-options


/// ``g_upd b i v h`` updates the buffer `b` in heap `h` at location
/// `i` writing ``v`` there. This is the spec analog of the stateful
/// update `upd` below.
let g_upd (#a:Type0) (#rrel #rel:srel a)
          (b:mbuffer a rrel rel)
          (i:nat{i < length b})
          (v:a)
          (h:HS.mem{live h b /\ rel (as_seq h b) (Seq.upd (as_seq h b) i v)})
  : GTot HS.mem
  = g_upd_seq b (Seq.upd (as_seq h b) i v) h

/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KreMLin compiles it as ``b[i] = v``.

val upd'
  (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel)
  (i:U32.t)
  (v:a)
  :HST.Stack unit (requires (fun h -> live h b /\ U32.v i < length b /\
                                   rel (as_seq h b) (Seq.upd (as_seq h b) (U32.v i) v)))
                  (ensures  (fun h _ h' -> h' == g_upd b (U32.v i) v h))
let upd' #_ #_ #_ b i v =
  let open HST in
  let Buffer max_length content idx len () = b in
  let s0 = !content in
  let sb0 = Seq.slice s0 (U32.v idx) (U32.v idx + U32.v len) in
  Buffer?.content b := replace_subseq s0 (U32.v idx) (U32.v len) (Seq.upd sb0 (U32.v i) v)

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

val recallable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0
let recallable' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0 =
  (not (g_is_null b)) ==> (
    HST.is_eternal_region (frameOf b) /\
    not (HS.is_mm (Buffer?.content b))
  )

let recallable = recallable'

(* TODO: candidate for wrapper *)
val recallable_null (#a:Type0) (#rrel #rel:srel a)
  :Lemma (recallable (null #a #rrel #rel)) [SMTPat (recallable (null #a #rrel #rel))]
let recallable_null #_ #_ #_ = ()

val recallable_includes (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (larger:mbuffer a1 rrel1 rel1) (smaller:mbuffer a2 rrel2 rel2)
  :Lemma (requires (larger `includes` smaller))
         (ensures (recallable larger <==> recallable smaller))
         [SMTPatOr [
             [SMTPat (recallable larger); SMTPat (recallable smaller);];
             [SMTPat (larger `includes` smaller)];
         ]]
let recallable_includes #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

val recall (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.Stack unit (requires (fun _ -> recallable b))
                  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))
let recall #_ #_ #_ b =
  if Null? b then ()
  else HST.recall (Buffer?.content b)


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0
let freeable' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) =
  (not (g_is_null b)) /\
  HS.is_mm (Buffer?.content b) /\
  HST.is_eternal_region (frameOf b) /\
  U32.v (Buffer?.max_length b) > 0 /\
  Buffer?.idx b == 0ul /\
  Buffer?.length b == Buffer?.max_length b
let freeable = freeable'

val free (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :HST.ST unit (requires (fun h0 -> live h0 b /\ freeable b))
               (ensures  (fun h0 _ h1 -> (not (g_is_null b)) /\
                                      Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
                                      (HS.get_tip h1) == (HS.get_tip h0) /\
                                      modifies (loc_addr_of_buffer b) h0 h1 /\
                                      HS.live_region h1 (frameOf b)))
let free #_ #_ #_ b = HST.rfree (Buffer?.content b)

val freeable_length (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (requires (freeable b)) (ensures (length b > 0))
         [SMTPat (freeable b)]
let freeable_length #_ #_ #_ b = ()

val freeable_disjoint (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))
let freeable_disjoint #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()

let freeable_disjoint' (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (loc_disjoint (loc_addr_of_buffer b1) (loc_addr_of_buffer b2)))
         [SMTPat (freeable b1); SMTPat (disjoint b1 b2)]
  = freeable_disjoint b1 b2


/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

unfold
let alloc_post_static (#a:Type0) (#rrel #rel:srel a)
  (r:HS.rid) (len:nat) (b:mbuffer a rrel rel)
  = (not (g_is_null b)) /\
    frameOf b == r /\
    length b == len

unfold
let alloc_post_common (#a:Type0) (#rrel #rel:srel a)
  (r:HS.rid) (len:nat) (b:mbuffer a rrel rel) (h0 h1:HS.mem)
  = alloc_post_static r len b /\
    b `unused_in` h0 /\
    live h1 b /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies loc_none h0 h1

let alloc_common (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t) (mm:bool)
  :HST.ST (mbuffer a rrel rrel)
          (requires (fun h0 -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures (fun h0 b h1 -> alloc_post_common r (U32.v len) b h0 h1 /\
                                 as_seq h1 b == Seq.create (U32.v len) init /\
                                 HS.is_mm (Buffer?.content b) == mm /\
                                 Buffer?.idx b == 0ul /\
                                 Buffer?.length b == Buffer?.max_length b))
  = let s = Seq.create (U32.v len) init in
    lemma_sub_compatilibity_is_reflexive (U32.v len) rrel;
    let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
      if mm then HST.ralloc_mm r s else HST.ralloc r s
    in
    let b = Buffer len content 0ul len () in
    b

/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

(* TODO: add a wrapper AND any reason that some post is in the refinement of the return type? *)
val gcmalloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:mbuffer a rrel rrel{recallable b /\ alloc_post_static r (U32.v len) b})
          (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures  (fun h b h' -> alloc_post_common r (U32.v len) b h h' /\
                                 as_seq h' b == Seq.create (U32.v len) init))
let gcmalloc #_ #_ r init len = alloc_common r init len false


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

val malloc (#a:Type0) (#rrel:srel a)
  (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (mbuffer a rrel rrel)
          (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures (fun h b h' -> alloc_post_common r (U32.v len) b h h' /\
                                as_seq h' b == Seq.create (U32.v len) init /\     
                                freeable b))
let malloc #_ #_ r init len = alloc_common r init len true


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

val alloca (#a:Type0) (#rrel:srel a)
  (init:a) (len:U32.t)
  :HST.StackInline (mbuffer a rrel rrel)
                   (requires (fun h -> U32.v len > 0))
                   (ensures (fun h b h' -> alloc_post_common (HS.get_tip h) (U32.v len) b h h' /\
                                         as_seq h' b == Seq.create (U32.v len) init))
let alloca #a #rrel init len =
  lemma_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc (Seq.create (U32.v len) init)
  in
  let b = Buffer len content 0ul len () in
  b


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloc_of_list_pre (#a:Type0) (init:list a) :GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

unfold let alloc_of_list_post (#a:Type0) (#rrel #rel:srel a) (len:nat) (buf:mbuffer a rrel rel) :GTot Type0 =
  normalize (length buf == len)

val alloca_of_list (#a:Type0) (#rrel:srel a) (init: list a)
  :HST.StackInline (mbuffer a rrel rrel) (requires (fun h -> alloc_of_list_pre #a init))
                                         (ensures (fun h b h' -> let len = FStar.List.Tot.length init in
                                                               alloc_post_common (HS.get_tip h) len b h h' /\
                                                               as_seq h' b == Seq.seq_of_list init /\
                                                               alloc_of_list_post #a len b))
let alloca_of_list #a #rrel init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc s
  in
  let b = Buffer len content 0ul len () in
  b

unfold let gcmalloc_of_list_pre (#a:Type0) (init:list a) :GTot Type0 =
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

(* TODO: Why is some of the post on the refinement? *)
val gcmalloc_of_list (#a:Type0) (#rrel:srel a) (r:HS.rid) (init:list a)
  :HST.ST (b:mbuffer a rrel rrel {
    let len = FStar.List.Tot.length init in
    recallable b /\
    alloc_post_static r len b /\
    alloc_of_list_post len b
  })
          (requires (fun h -> HST.is_eternal_region r /\ gcmalloc_of_list_pre #a init))
          (ensures  (fun h b h' -> let len = FStar.List.Tot.length init in
                                 alloc_post_common r len b h h' /\
                                 as_seq h' b == Seq.seq_of_list init))
let gcmalloc_of_list #a #rrel r init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc r s
  in
  let b = Buffer len content 0ul len () in
  b

/// Derived operations

val blit (#a:Type0) (#rrel1 #rrel2 #rel1 #rel2:srel a)
  (src:mbuffer a rrel1 rel1)
  (idx_src:U32.t)
  (dst:mbuffer a rrel2 rel2)
  (idx_dst:U32.t)
  (len:U32.t)
  :HST.Stack unit (requires (fun h -> live h src /\ live h dst /\ disjoint src dst /\
                                    U32.v idx_src + U32.v len <= length src /\
                                    U32.v idx_dst + U32.v len <= length dst /\
				    rel2 (as_seq h dst)
				         (replace_subseq (as_seq h dst) (U32.v idx_dst) (U32.v len)
					                 (mslice (as_seq h src) (U32.v idx_src) (U32.v len)))))
                  (ensures (fun h _ h' -> modifies (loc_buffer dst) h h' /\
                                        live h' dst /\
                                        Seq.slice (as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
                                        Seq.slice (as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len) /\
                                        Seq.slice (as_seq h' dst) 0 (U32.v idx_dst) ==
                                        Seq.slice (as_seq h dst) 0 (U32.v idx_dst) /\
                                        Seq.slice (as_seq h' dst) (U32.v idx_dst + U32.v len) (length dst) ==
                                        Seq.slice (as_seq h dst) (U32.v idx_dst + U32.v len) (length dst)))

#push-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let blit #a #rrel1 #rrel2 #rel1 #rel2 src idx_src dst idx_dst len =
  let open HST in
  if len = 0ul then ()
  else
    let h = get () in
    let Buffer _ content1 idx1 length1 () = src in
    let Buffer _ content2 idx2 length2 () = dst in
    let s_full1 = !content1 in
    let s_full2 = !content2 in
    let s1 = mslice s_full1 (U32.v idx1) (U32.v length1) in
    let s2 = mslice s_full2 (U32.v idx2) (U32.v length2) in
    let s_sub_src = mslice s1 (U32.v idx_src) (U32.v len) in
    let s2' = replace_subseq s2 (U32.v idx_dst) (U32.v len) s_sub_src in
    let s_full2' = replace_subseq s_full2 (U32.v idx2) (U32.v length2) s2' in
    content2 := s_full2';
    g_upd_seq_as_seq dst s2' h;
    lemma_replace_subseq_elim s2 (U32.v idx_dst) (U32.v len) s_sub_src
#pop-options

module L = FStar.List.Tot

unfold
let assign_list_t (#a:Type0) (#rrel #rel:srel a) (l:list a) =
  (b:mbuffer a rrel rel) ->
  HST.Stack unit (requires (fun h0 -> live h0 b /\
                                    length b = L.length l /\
				    rel (as_seq h0 b) (Seq.seq_of_list l)))
                 (ensures (fun h0 _ h1 -> live h1 b /\
                                        modifies (loc_buffer b) h0 h1 /\
                                        as_seq h1 b == Seq.seq_of_list l))

let assign_list (#a:Type0) (#rrel #rel:srel a) (l:list a) :assign_list_t #a #rrel #rel l
  = fun b ->
    let open HST in
    if L.length l > 0 then
      let h = get () in
      let Buffer _ content id len () = b in
      let s_full = !content in
      let s_full = replace_subseq s_full (U32.v id) (U32.v len) (Seq.seq_of_list l) in
      content := s_full;
      g_upd_seq_as_seq b (Seq.seq_of_list l) h  //for modifies clause

/// Type class instantiation for compositionality with other kinds of memory locations than regions, references or buffers (just in case).
/// No usage pattern has been found yet.

module MG = FStar.ModifiesGen

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0
let abuffer' = ubuffer'

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (abuffer' region addr)

let coerce (t2: Type) (#t1: Type) (x1: t1) : Pure t2 (requires (t1 == t2)) (ensures (fun y -> y == x1)) = x1

val cloc_cls: MG.cls abuffer
let cloc_cls =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.cls abuffer) cls

val cloc_of_loc (l: loc) : Tot (MG.loc cloc_cls)
let cloc_of_loc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.loc cloc_cls) l

val loc_of_cloc (l: MG.loc cloc_cls) : Tot loc
let loc_of_cloc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce loc l

val loc_of_cloc_of_loc (l: loc) : Lemma
  (loc_of_cloc (cloc_of_loc l) == l)
  [SMTPat (loc_of_cloc (cloc_of_loc l))]
let loc_of_cloc_of_loc l = ()

val cloc_of_loc_of_cloc (l: MG.loc cloc_cls) : Lemma
  (cloc_of_loc (loc_of_cloc l) == l)
  [SMTPat (cloc_of_loc (loc_of_cloc l))]
let cloc_of_loc_of_cloc l = ()

val cloc_of_loc_none: unit -> Lemma (cloc_of_loc loc_none == MG.loc_none)
let cloc_of_loc_none _ = ()

val cloc_of_loc_union (l1 l2: loc) : Lemma
  (cloc_of_loc (loc_union l1 l2) == MG.loc_union (cloc_of_loc l1) (cloc_of_loc l2))
let cloc_of_loc_union _ _ = ()

val cloc_of_loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (cloc_of_loc (loc_addresses preserve_liveness r n) == MG.loc_addresses preserve_liveness r n)
let cloc_of_loc_addresses _ _ _ = ()

val cloc_of_loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (cloc_of_loc (loc_regions preserve_liveness r) == MG.loc_regions preserve_liveness r)
let cloc_of_loc_regions _ _ = ()

val loc_includes_to_cloc (l1 l2: loc) : Lemma
  (loc_includes l1 l2 <==> MG.loc_includes (cloc_of_loc l1) (cloc_of_loc l2))
let loc_includes_to_cloc l1 l2 = ()

val loc_disjoint_to_cloc (l1 l2: loc) : Lemma
  (loc_disjoint l1 l2 <==> MG.loc_disjoint (cloc_of_loc l1) (cloc_of_loc l2))
let loc_disjoint_to_cloc l1 l2 = ()

val modifies_to_cloc (l: loc) (h1 h2: HS.mem) : Lemma
  (modifies l h1 h2 <==> MG.modifies (cloc_of_loc l) h1 h2)
let modifies_to_cloc l h1 h2 = ()
