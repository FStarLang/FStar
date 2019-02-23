module LowStar.FreezableBuffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

type u8 = U8.t
type u32 = U32.t

abstract let freezable_preorder : P.preorder (Seq.seq u8) =
  fun s1 s2 ->
  Seq.length s1 == Seq.length s2 /\
  (let len = Seq.length s1 in
   (len > 0 ==>
    (let w1 = U8.v (Seq.index s1 0) in
     let w2 = U8.v (Seq.index s2 0) in
     ((w1 >= 1 /\ w1 <= len) ==>
      (w2 <= len /\ w1 <= w2 /\
       (forall (i:nat).{:pattern Seq.index s2 i} (i >= 1 /\ i < w1) ==> Seq.index s1 i == Seq.index s2 i)))))) 

abstract let freezable_preorder_equiv (s1 s2: Seq.seq u8) : Lemma
  (freezable_preorder s1 s2 <==> (
  Seq.length s1 == Seq.length s2 /\
  (let len = Seq.length s1 in
   (len > 0 ==>
    (let w1 = U8.v (Seq.index s1 0) in
     let w2 = U8.v (Seq.index s2 0) in
     ((w1 >= 1 /\ w1 <= len) ==>
      (w2 <= len /\ w1 <= w2 /\
       (forall (i:nat).{:pattern Seq.index s2 i} (i >= 1 /\ i < w1) ==> Seq.index s1 i == Seq.index s2 i)))))) 
  ))
= ()

let fbuffer = b:mbuffer u8 freezable_preorder freezable_preorder

let lfbuffer (len:nat) = b:fbuffer{length b == len}

let fgcmalloc (r:HS.rid) (len:u32{UInt.size (U32.v len + 1) 8})
  : HST.ST (b:lfbuffer (U32.v len + 1){frameOf b == r /\ recallable b})
           (requires (fun _       -> malloc_pre r len))
	   (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len + 1) (U8.uint_to_t 1))))
  = mgcmalloc #_ #freezable_preorder r (U8.uint_to_t 1) (U32.add len 1ul)

let fupd (b:fbuffer) (i:u32) (v:u8)
  : HST.Stack unit (requires (fun h0 -> 
                              live h0 b /\ U32.v i < length b /\
                              U32.v i >= U8.v (Seq.index (as_seq h0 b) 0)))
		   (ensures  (fun h0 _ h1 ->
		              (not (g_is_null b)) /\
			      modifies (loc_buffer b) h0 h1 /\
			      live h1 b /\
			      as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v))
  = upd b i v

let freeze (b:fbuffer) (i:u8)
  : HST.Stack unit (requires (fun h0 ->
                              live h0 b /\ U8.v i < length b /\ U8.v i >= U8.v (Seq.index (as_seq h0 b) 0)))
		   (ensures  (fun h0 _ h1 ->
		              (not (g_is_null b)) /\
			      modifies (loc_buffer b) h0 h1 /\
			      live h1 b /\
			      as_seq h1 b == Seq.upd (as_seq h0 b) 0 i))
  = upd b 0ul i

let fpred (i j:u32) (snap:G.erased (Seq.seq u8)) : spred u8 =
  fun s ->
  let len = Seq.length s in
   len > 0 /\
   (let w = U8.v (Seq.index s 0) in
    let i = U32.v i in
    let j = U32.v j in
    let snap = G.reveal snap in
    (i > 0 /\ i <= j /\ j <= w /\ w <= len /\ Seq.length snap == j - i /\ Seq.equal (Seq.slice s i j) snap))

let witness_slice (b:fbuffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : HST.Stack unit (requires (fun h0      -> fpred i j snap (as_seq h0 b)))
                   (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed b (fpred i j snap)))
  = witness_p b (fpred i j snap)

let recall_slice (b:fbuffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : HST.Stack unit (requires (fun h0      -> (recallable b \/ live h0 b) /\ witnessed b (fpred i j snap)))
                   (ensures  (fun h0 _ h1 ->
		              h0 == h1 /\ live h1 b /\ 
		              (let i = U32.v i in
			       let j = U32.v j in
			       let s = as_seq h1 b in
			       let snap = G.reveal snap in
			       i > 0 /\ i <= j /\ j <= length b /\ Seq.length snap == j - i /\
			       Seq.equal (Seq.slice s i j) snap)))
  = recall_p b (fpred i j snap)
