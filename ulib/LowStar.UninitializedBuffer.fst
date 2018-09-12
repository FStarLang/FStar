module LowStar.UninitializedBuffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private let initialization_rel (a:Type0) :P.relation (Seq.seq (option a)) =
  fun s1 s2 -> Seq.length s1 == Seq.length s2 /\
            (forall (i:nat).{:pattern (Seq.index s2 i)}
	              i < Seq.length s1 ==> Some? (Seq.index s1 i) ==> Some? (Seq.index s2 i))

private let lemma_initialization_rel_is_transitive (a:Type0) (s1 s2 s3:Seq.seq (option a))
  :Lemma ((initialization_rel a s1 s2 /\ initialization_rel a s2 s3) ==> initialization_rel a s1 s3)
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (initialization_rel a s1 s2 /\ initialization_rel a s2 s3) then
    begin
      assert (forall (i:nat). i < Seq.length s1 ==> Some? (Seq.index s1 i) ==> Some? (Seq.index s2 i));
      assert (forall (i:nat). i < Seq.length s2 ==> Some? (Seq.index s2 i) ==> Some? (Seq.index s3 i))
    end

private let initialization_preorder (a:Type0) :srel (option a) =
  FStar.Classical.forall_intro_3 (lemma_initialization_rel_is_transitive a);
  initialization_rel a

type ubuffer (a:Type0) = b:mbuffer (option a) (initialization_preorder a) (initialization_preorder a){recallable b}

unfold let unull (#a:Type0) :ubuffer a = mnull #(option a) #(initialization_preorder a) #(initialization_preorder a)

unfold let gsub (#a:Type0) = mgsub #(option a) #(initialization_preorder a) #(initialization_preorder a) (initialization_preorder a)

unfold let gsub_inj (#a:Type0) = mgsub_inj #(option a) #(initialization_preorder a) #(initialization_preorder a) (initialization_preorder a) (initialization_preorder a)

inline_for_extraction
type pointer (a:Type0) = b:ubuffer a{length b == 1}

inline_for_extraction
type pointer_or_null (a:Type0) = b:ubuffer a{if g_is_null b then True else length b == 1}

inline_for_extraction let usub (#a:Type0) = msub #(option a) #(initialization_preorder a) #(initialization_preorder a) (initialization_preorder a)

inline_for_extraction let uoffset (#a:Type0) = moffset #(option a) #(initialization_preorder a) #(initialization_preorder a) (initialization_preorder a)


(****** main stateful API *****)

private let ipred (#a:Type0) (i:nat) :spred (option a) = fun s -> i < Seq.length s ==> Some? (Seq.index s i)
private let rpred (#a:Type0) (i:nat) (len:nat) :spred (option a) =
  fun s -> i + len <= Seq.length s ==> (forall (j:nat).{:pattern (Seq.index s j)} (j >= i /\ j < i + len) ==> Some? (Seq.index s j))

let initialized_at (#a:Type0) (b:ubuffer a) (i:nat) :Type0 = witnessed b (ipred i)
let initiailized_at_range (#a:Type0) (b:ubuffer a) (i:nat) (len:nat) :Type0 = witnessed b (rpred i len)

let uindex (#a:Type0) (b:ubuffer a) (i:U32.t)
  :HST.Stack a (requires (fun h -> live h b /\ U32.v i < length b /\ b `initialized_at` (U32.v i)))
               (ensures  (fun h y h' -> h == h' /\
	                             (let y_opt = Seq.index (as_seq h b) (U32.v i) in
				      Some? y_opt /\ y == Some?.v y_opt)))
  = let y_opt = index b i in
    recall_p b (ipred (U32.v i));
    Some?.v y_opt

let upd (#a:Type0) (b:ubuffer a) (i:U32.t) (v:a)
  :HST.Stack unit (requires (fun h0      -> live h0 b /\ U32.v i < length b))
                  (ensures  (fun h0 _ h1 -> (not (g_is_null b)) /\
		                         modifies (loc_buffer b) h0 h1 /\
					 live h1 b /\
					 as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) (Some v) /\
					 b `initialized_at` (U32.v i)))
  = upd b i (Some v);
    witness_p b (ipred (U32.v i))

let ugcmalloc (#a:Type0) (r:HS.rid) (len:U32.t)
  :HST.ST (b:ubuffer a{frameOf b == r}) (requires (fun h0      -> malloc_pre r len))
                                        (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) None)))
  = mgcmalloc r None len

let ublit (#a:Type0) (#rrel #rel:srel a)
  (src:mbuffer a rrel rel)
  (idx_src:U32.t)
  (dst:ubuffer a)
  (idx_dst:U32.t)
  (len:U32.t)
  :HST.Stack unit (requires (fun h -> live h src /\ live h dst /\ disjoint src dst /\
                                    U32.v idx_src + U32.v len <= length src /\
                                    U32.v idx_dst + U32.v len <= length dst))
                  (ensures (fun h _ h' -> modifies (loc_buffer dst) h h' /\
                                        live h' dst /\
					(forall (i:nat). (i < U32.v len) ==>
					           Seq.index (as_seq h' dst) (U32.v idx_dst + i) ==
						   Some (Seq.index (as_seq h src) (U32.v idx_src + i))) /\
                                        Seq.slice (as_seq h' dst) 0 (U32.v idx_dst) ==
                                        Seq.slice (as_seq h dst) 0 (U32.v idx_dst) /\
                                        Seq.slice (as_seq h' dst) (U32.v idx_dst + U32.v len) (length dst) ==
                                        Seq.slice (as_seq h dst) (U32.v idx_dst + U32.v len) (length dst) /\
					initiailized_at_range dst (U32.v idx_dst) (U32.v len)))
  = admit ()
