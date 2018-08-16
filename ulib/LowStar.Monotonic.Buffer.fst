module LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
 * Abbreviation for preorders on sequences
 *)
type pre_t (a:Type0) = P.preorder (Seq.seq a)

(*
 * Replacing subsequence in s at (offset, offset + len) by sub
 *)
let replace_subseq
  (#a:Type0) (s:Seq.seq a)
  (offset:nat) (len:nat{offset + len <= Seq.length s})
  (sub:Seq.seq a{Seq.length sub == len})
  :Tot (Seq.seq a)
  = Seq.append (Seq.slice s 0 offset) (Seq.append sub (Seq.slice s (offset + len) (Seq.length s)))

(*
 * Shorthand slice, that takes length as the second argument
 *)
let mslice (#a:Type0) (s:Seq.seq a) (offset:nat) (len:nat{offset + len <= Seq.length s}) :Tot (Seq.seq a) =
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
let lemma_replace_subseq_slice
  (a:Type0) (parent_length offset1 len1 offset2 len2:nat)
  (s:Seq.seq a) (s2:Seq.seq a)
  :Lemma ((offset1 + len1 <= parent_length /\ offset2 + len2 <= len1 /\
           Seq.length s == parent_length /\ Seq.length s2 == len2) ==>
	  (Seq.equal (replace_subseq s (offset1 + offset2) len2 s2)
	             (replace_subseq s offset1 len1 (replace_subseq (mslice s offset1 len1)
						                    offset2 len2 s2))))
  = if (offset1 + len1 <= parent_length && offset2 + len2 <= len1 &&
        Seq.length s = parent_length && Seq.length s2 = len2) then begin

      //ss1 and ss2 are the two sequences we need to prove equal
      let ss1 = replace_subseq s (offset1 + offset2) len2 s2 in
      let ss2 = replace_subseq s offset1 len1 (replace_subseq (mslice s offset1 len1) offset2 len2 s2) in

      let ss11 = Seq.slice s 0 (offset1 + offset2) in
      let ss13 = Seq.slice s (offset1 + offset2 + len2) (Seq.length s) in
  
      //this is what ss1 unfolds to    
      assert (Seq.equal ss1 (Seq.append ss11 (Seq.append s2 ss13)));      

      let ss21 = Seq.slice s 0 offset1 in
      let ss22 = Seq.slice (Seq.slice s offset1 (offset1 + len1)) 0 offset2 in
      let ss24 = Seq.slice (Seq.slice s offset1 (offset1 + len1)) (offset2 + len2) len1 in
      let ss25 = Seq.slice s (offset1 + len1) (Seq.length s) in

      //this is what ss2 unfolds to
      assert (Seq.equal ss2 (Seq.append ss21 (Seq.append (Seq.append ss22 (Seq.append s2 ss24)) ss25)));

      //Z3 only needs to know the following and then it figures it out
      assert (Seq.equal (Seq.append ss21 ss22) ss11)
    end

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
let compatible_sub_preorder
  (#a:Type0) (parent_pre sub_pre:pre_t a)
  (parent_len:nat) (offset:nat) (len:nat{offset + len <= parent_len})
  = (forall (s1 s2:Seq.seq a). (Seq.length s1 == Seq.length s2 /\ Seq.length s1 == parent_len) ==>
                          (parent_pre s1 s2) ==>
		          (sub_pre (mslice s1 offset len) (mslice s2 offset len))) /\  //(a)
    (forall (s s2:Seq.seq a). (Seq.length s == parent_len /\ Seq.length s2 == len) ==>
                         (sub_pre (mslice s offset len) s2) ==>
  		         (parent_pre s (replace_subseq s offset len s2)))  //(b)

(*
 * Proof for transitivity of the compatibility relation
 *)
private let lemma_sub_compatibility_is_transitive
  (#a:Type0) (parent_pre:pre_t a) (parent_length:nat)
  (pre:pre_t a) (child_pre:pre_t a)
  (offset1 len1 offset2 len2:nat)
  :Lemma (requires (offset1 + len1 <= parent_length /\ offset2 + len2 <= len1 /\
                    compatible_sub_preorder parent_pre pre parent_length offset1 len1 /\
                    compatible_sub_preorder pre child_pre len1 offset2 len2))
	 (ensures  (compatible_sub_preorder parent_pre child_pre parent_length (offset1 + offset2) len2))
  = Classical.forall_intro_2 (lemma_replace_subseq_slice a parent_length offset1 len1 offset2 len2)
  
// abstract noeq type mbuffer (a:Type0) (rrel:pre_t a) (rel:pre_t a) =
//   | Null: mbuffer a rrel rel
//   | 
