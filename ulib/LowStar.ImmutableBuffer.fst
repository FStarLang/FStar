module LowStar.ImmutableBuffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private let immutable_preorder (a:Type0) :srel a = fun s1 s2 -> Seq.equal s1 s2

type ibuffer (a:Type0) = mbuffer a (immutable_preorder a) (immutable_preorder a)

unfold let inull (#a:Type0) :ibuffer a = mnull #a #(immutable_preorder a) #(immutable_preorder a)

unfold let igsub (#a:Type0) = mgsub #a #(immutable_preorder a) #(immutable_preorder a) (immutable_preorder a)

unfold let igsub_inj (#a:Type0) = mgsub_inj #a #(immutable_preorder a) #(immutable_preorder a) (immutable_preorder a) (immutable_preorder a)

inline_for_extraction
type ipointer (a:Type0) = b:ibuffer a{length b == 1}

inline_for_extraction
type ipointer_or_null (a:Type0) = b:ibuffer a{if g_is_null b then True else length b == 1}

inline_for_extraction let isub (#a:Type0) = msub #a #(immutable_preorder a) #(immutable_preorder a) (immutable_preorder a)

inline_for_extraction let ioffset (#a:Type0) = moffset #a #(immutable_preorder a) #(immutable_preorder a) (immutable_preorder a)

unfold let libuffer (a:Type0) (len:nat) = lmbuffer a (immutable_preorder a) (immutable_preorder a) len

private let cpred (#a:Type0) (s:Seq.seq a) :spred a = fun s1 -> Seq.equal s s1

let igcmalloc (#a:Type0) (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:libuffer a (U32.v len){frameOf b == r /\ recallable b /\
                                    witnessed b (cpred (Seq.create (U32.v len) init))})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))
  = let b = mgcmalloc r init len in
    witness_p b (cpred (Seq.create (U32.v len) init));
    b

let igcmalloc_of_list (#a:Type0) (r:HS.rid) (init:list a)
  :HST.ST (b:libuffer a (normalize_term (List.Tot.length init)){frameOf b == r /\ recallable b /\
                                                                witnessed b (cpred (Seq.seq_of_list init))})
          (requires (fun _       -> gcmalloc_of_list_pre r init))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init)))
  = let b = mgcmalloc_of_list r init in
    witness_p b (cpred (Seq.seq_of_list init));
    b

let witness_contents (#a:Type0) (b:ibuffer a) (s:Seq.seq a)
  :HST.ST unit (requires (fun h0      -> recallable b /\ Seq.equal (as_seq h0 b) s))
                 (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed b (cpred s)))
  = witness_p b (cpred s)

let recall_contents (#a:Type0) (b:ibuffer a) (s:Seq.seq a)
  :HST.ST unit (requires (fun _       -> recallable b /\ witnessed b (cpred s)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ as_seq h0 b == s))
  = recall b; recall_p b (cpred s)
