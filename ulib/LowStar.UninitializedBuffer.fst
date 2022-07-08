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
module LowStar.UninitializedBuffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
 * Uninitialized buffers
 *
 * Modeled as: seq (option a) with a preorder that an index once set remains set
 *)
private let initialization_preorder (a:Type0) :srel (option a) =
  fun s1 s2 -> Seq.length s1 == Seq.length s2 /\
            (forall (i:nat).{:pattern (Seq.index s2 i)} i < Seq.length s1 ==> Some? (Seq.index s1 i) ==> Some? (Seq.index s2 i))

type ubuffer (a:Type0) =
  mbuffer (option a) (initialization_preorder a) (initialization_preorder a)

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

(*
 * b `initialized_at` i: is a stable predicate that witnesses the initialization of an index i in ubuffer b
 *)
private let ipred (#a:Type0) (i:nat) :spred (option a) = fun s -> i < Seq.length s ==> Some? (Seq.index s i)
let initialized_at (#a:Type0) (b:ubuffer a) (i:nat) :Type0 = witnessed b (ipred i)

(*
 * Clients need to prove that b is initialized_at i
 *)
let uindex (#a:Type0) (b:ubuffer a) (i:U32.t)
  :HST.Stack a (requires (fun h0      -> live h0 b /\ U32.v i < length b /\ b `initialized_at` (U32.v i)))
               (ensures  (fun h0 y h1 -> let y_opt = Seq.index (as_seq h0 b) (U32.v i) in
				      Some? y_opt /\ y == Some?.v y_opt /\ h0 == h1))
  = let y_opt = index b i in
    recall_p b (ipred (U32.v i));
    Some?.v y_opt

(*
 * b `initialized_at` i is a postcondition
 *)
let uupd (#a:Type0) (b:ubuffer a) (i:U32.t) (v:a)
  :HST.Stack unit (requires (fun h0      -> live h0 b /\ U32.v i < length b))
                  (ensures  (fun h0 _ h1 -> modifies (loc_buffer b) h0 h1 /\
					 live h1 b /\
					 as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) (Some v) /\
					 b `initialized_at` (U32.v i)))
  = upd b i (Some v);
    witness_p b (ipred (U32.v i))

unfold let lubuffer (a:Type0) (len:nat) = b:ubuffer a{length b == len}

unfold let lubuffer_or_null (a:Type0) (len:nat) (r:HS.rid) =
  b:ubuffer a{(not (g_is_null b)) ==> (length b == len /\ frameOf b == r)}

(*
 * No initializer
 *)
let ugcmalloc (#a:Type0) (r:HS.rid) (len:U32.t)
  :HST.ST (b:lubuffer a (U32.v len){frameOf b == r /\ recallable b})
          (requires (fun h0      -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) None)))
  = mgcmalloc r None len

inline_for_extraction
let ugcmalloc_partial (#a:Type0) (r:HS.rid) (len:U32.t)
  :HST.ST (b:lubuffer_or_null a (U32.v len) r{recallable b})
          (requires (fun h0      -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U32.v len) None)))
  = mgcmalloc r None len

let umalloc (#a:Type0) (r:HS.rid) (len:U32.t)
  :HST.ST (b:lubuffer a (U32.v len){frameOf b == r /\ freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) None)))
  = mmalloc r None len

inline_for_extraction
let umalloc_partial (#a:Type0) (r:HS.rid) (len:U32.t)
  :HST.ST (b:lubuffer_or_null a (U32.v len) r{(not (g_is_null b)) ==> freeable b})
          (requires (fun _       -> malloc_pre r len))
          (ensures  (fun h0 b h1 -> alloc_partial_post_mem_common b h0 h1 (Seq.create (U32.v len) None)))
  = mmalloc r None len

let ualloca (#a:Type0) (len:U32.t)
  :HST.StackInline (lubuffer a (U32.v len))
                   (requires (fun _       -> alloca_pre len))
                   (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) None) /\
		                          frameOf b == HS.get_tip h0))
  = malloca None len

(*
 * blit functionality, where src is a regular buffer
 *)
[@@"opaque_to_smt"]
unfold let valid_j_for_blit
  (#a:Type0) (#rrel #rel:srel a) (src:mbuffer a rrel rel) (idx_src:U32.t)
  (dst:ubuffer a) (idx_dst:U32.t) (j:U32.t)
  = U32.v idx_src + U32.v j <= length src /\
    U32.v idx_dst + U32.v j <= length dst

(*
 * postcondition of blit
 *)
[@@"opaque_to_smt"]
unfold private let ublit_post_j
  (#a:Type0) (#rrel #rel:srel a) (src:mbuffer a rrel rel) (idx_src:U32.t)
  (dst:ubuffer a) (idx_dst:U32.t) (j:U32.t{valid_j_for_blit src idx_src dst idx_dst j})
  (h0 h1:HS.mem)
  = modifies (loc_buffer dst) h0 h1 /\ live h1 dst /\
    (forall (i:nat).{:pattern (Seq.index (as_seq h1 dst) i)} (i >= U32.v idx_dst /\ i < U32.v idx_dst + U32.v j ==>
                                                       Seq.index (as_seq h1 dst) i ==
                                                       Some (Seq.index (as_seq h0 src) (U32.v idx_src + i - U32.v idx_dst)))
    ) /\
    Seq.slice (as_seq h1 dst) 0 (U32.v idx_dst) == Seq.slice (as_seq h0 dst) 0 (U32.v idx_dst) /\
    Seq.slice (as_seq h1 dst) (U32.v idx_dst + U32.v j) (length dst) == Seq.slice (as_seq h0 dst) (U32.v idx_dst + U32.v j) (length dst) /\
    (forall (i:nat).{:pattern (dst `initialized_at` i)} (i >= U32.v idx_dst /\ i < U32.v idx_dst + U32.v j) ==>
					          dst `initialized_at` i)

let ublit (#a:Type0) (#rrel #rel:srel a)
  (src:mbuffer a rrel rel) (idx_src:U32.t)
  (dst:ubuffer a{disjoint src dst}) (idx_dst:U32.t)
  (len:U32.t{valid_j_for_blit src idx_src dst idx_dst len})
  :HST.Stack unit (requires (fun h0     -> live h0 src /\ live h0 dst))
                  (ensures (fun h0 _ h1 -> ublit_post_j src idx_src dst idx_dst len h0 h1))
  = let rec aux (j:U32.t{valid_j_for_blit src idx_src dst idx_dst j})
      :HST.Stack unit
       (requires (fun h0     -> live h0 src /\ live h0 dst /\ ublit_post_j src idx_src dst idx_dst j h0 h0))
       (ensures (fun h0 _ h1 -> ublit_post_j src idx_src dst idx_dst len h0 h1))
      = let open FStar.UInt32 in
        if j = len then ()
        else if j <^ len then begin
          uupd dst (idx_dst +^ j) (index src (idx_src +^ j));
	  aux (j +^ 1ul)
	end
    in
    aux 0ul

let witness_initialized (#a:Type0) (b:ubuffer a) (i:nat)
  :HST.ST unit (fun h0      -> i < length b /\ Some? (Seq.index (as_seq h0 b) i))
               (fun h0 _ h1 -> h0 == h1 /\ b `initialized_at` i)
  = witness_p b (ipred i)

let recall_initialized (#a:Type0) (b:ubuffer a) (i:nat)
  :HST.ST unit (fun h0      -> (recallable b \/ live h0 b) /\ b `initialized_at` i)
               (fun h0 _ h1 -> h0 == h1 /\ live h0 b /\ (i < length b ==> Some? (Seq.index (as_seq h0 b) i)))
  = recall_p b (ipred i)

let buffer_immutable_buffer_disjoint
  (#ti:Type) (#t:Type0)
  (bi:LowStar.ImmutableBuffer.ibuffer ti)
  (b:ubuffer t)
  (h: HS.mem)
: Lemma
  (requires (
    live h b /\
    live h bi /\
    (exists (x:t). True ) // If the type is not inhabited, the initialization and immutable preorders are effectively identical
  ))
  (ensures (
    disjoint b bi
  ))
= if length b = 0
    then empty_disjoint b bi
  else if length bi = 0
    then empty_disjoint bi b
  else begin
    let open LowStar.ImmutableBuffer in
    let s = as_seq h b in
    let s0 = Seq.upd s 0 None in
    let s1 = Seq.upd s 0 (Some (FStar.IndefiniteDescription.indefinite_description_ghost t (fun _ -> True))) in
    assert(initialization_preorder _ s0 s1 /\
           Seq.index s0 0 =!= Seq.index s1 0 /\
           ~( immutable_preorder _ s0 s1 <==> initialization_preorder _ s0 s1));
    live_same_addresses_equal_types_and_preorders b bi h
  end
