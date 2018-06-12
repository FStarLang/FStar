module LowStar.BufferCompat
include LowStar.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

unfold
let rcreate_post_common
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
  (h0 h1: HS.mem)
= alloc_post_common r len b h0 h1

inline_for_extraction
let rfree
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
= free b

inline_for_extraction
let rcreate
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    rcreate_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    recallable b
  ))
= let b = gcmalloc r init len in
  b

inline_for_extraction
let rcreate_mm
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    rcreate_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    freeable b
  ))
= malloc r init len

inline_for_extraction
let create
  (#a: Type)
  (init: a)
  (len: U32.t)
: HST.StackInline (buffer a)
  (requires (fun h -> U32.v len > 0))
  (ensures (fun h b h' ->
    rcreate_post_common (HS.get_tip h) (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))
= alloca init len

unfold let createL_pre (#a: Type0) (init: list a) : GTot Type0 =
  alloc_of_list_pre init

unfold let createL_post (#a: Type) (len: nat) (buf: buffer a) : GTot Type0 =
  alloc_of_list_post len buf

let createL
  (#a: Type0)
  (init: list a)
: HST.StackInline (buffer a)
  (requires (fun h -> createL_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    rcreate_post_common (HS.get_tip h) len b h h' /\
    as_seq h' b == Seq.of_list init /\
    createL_post #a len b
  ))
= alloca_of_list init
