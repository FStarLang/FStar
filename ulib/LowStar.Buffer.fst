module LowStar.Buffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let trivial_preorder (a:Type0) :srel a = fun _ _ -> True

type buffer (a:Type0) = mbuffer a (trivial_preorder a) (trivial_preorder a)

let null (#a:Type0) :buffer a = mnull #a #(trivial_preorder a) #(trivial_preorder a)

let gsub (#a:Type0) (b:buffer a) (i:U32.t) (len:U32.t)
  :Ghost (buffer a) (requires (U32.v i + U32.v len <= length b)) (ensures (fun _ -> True))
  = mgsub b i len (trivial_preorder a)

let gsub_inj (#a:Type0) (b1 b2:buffer a) (i1 i2:U32.t) (len1 len2:U32.t)
  :Lemma (requires (U32.v i1 + U32.v len1 <= length b1 /\ U32.v i2 + U32.v len2 <= length b2 /\
		    gsub b1 i1 len1 === gsub b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))
  = mgsub_inj b1 b2 i1 i2 len1 len2 (trivial_preorder a) (trivial_preorder a)

inline_for_extraction
type pointer (a:Type0) = b:buffer a{length b == 1}

inline_for_extraction
type pointer_or_null (a:Type0) = b:buffer a{if g_is_null b then True else length b == 1}

(*
 * TODO: these are good candidates for letting F* infer WP,
 *       since their specs are just copied from their Monotonic.Buffer counterparts
 *)
let sub (#a:Type0) (b:buffer a) (i:U32.t) (len:U32.t)
  :HST.Stack (buffer a)
             (requires (fun h -> U32.v i + U32.v len <= length b /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i len))
  = msub b i len (trivial_preorder a)

let offset (#a:Type0) (b:buffer a) (i:U32.t)
  :HST.Stack (buffer a)
             (requires (fun h -> U32.v i <= length b /\ live h b))
             (ensures  (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (len b) i)))
  = moffset b i (trivial_preorder a)


unfold let lbuffer (a:Type0) (len:nat)
  = b:buffer a{length b == len /\ not (g_is_null b)}

let gcmalloc (#a:Type0) (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lbuffer a (U32.v len){frameOf b == r /\ recallable b})
          (requires (fun _       -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))
  = mgcmalloc r init len

let malloc (#a:Type0) (r:HS.rid) (init:a) (len:U32.t)
  :HST.ST (b:lbuffer a (U32.v len){frameOf b == r /\ freeable b})
          (requires (fun _       -> HST.is_eternal_region r /\ U32.v len > 0))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init)))
  = mmalloc r init len

let alloca (#a:Type0) (init:a) (len:U32.t)
  :HST.StackInline (lbuffer a (U32.v len))
                   (requires (fun _       -> U32.v len > 0))
                   (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init) /\
		                          frameOf b == HS.get_tip h0))
  = malloca init len

let alloca_of_list (#a:Type0) (init: list a)
  :HST.StackInline (lbuffer a (normalize_term (List.Tot.length init)))
                   (requires (fun _      -> alloca_of_list_pre init))
                   (ensures (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init) /\
		                         frameOf b == HS.get_tip h0))
  = malloca_of_list init

let gcmalloc_of_list (#a:Type0) (r:HS.rid) (init:list a)
  :HST.ST (b:lbuffer a (normalize_term (List.Tot.length init)){
    frameOf b == r /\ 
    recallable b})
          (requires (fun _       -> HST.is_eternal_region r /\ gcmalloc_of_list_pre init))
          (ensures  (fun h0 b h1 -> alloc_post_mem_common b h0 h1 (Seq.seq_of_list init)))
  = mgcmalloc_of_list r init

module L = FStar.List.Tot

unfold
let assign_list_t #a (l: list a) = (b: buffer a) -> HST.Stack unit
  (requires (fun h0 ->
    live h0 b /\
    length b = L.length l))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (modifies (loc_buffer b) h0 h1) /\
    as_seq h1 b == Seq.seq_of_list l))

let rec assign_list #a (l: list a): assign_list_t l
= fun b ->
  match l with
  | [] ->
      let h = HST.get () in
      assert (length b = 0);
      assert (Seq.length (as_seq h b) = 0);
      assert (Seq.equal (as_seq h b) (Seq.empty #a));
      assert (Seq.seq_of_list [] `Seq.equal` Seq.empty #a)
  | hd :: tl ->
      let b_hd = sub b 0ul 1ul in
      let b_tl = offset b 1ul in
      let h = HST.get () in
      upd b_hd 0ul hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      assert (as_seq h1 b_hd == as_seq h0 b_hd);
      assert (get h1 b_hd 0 == hd);
      assert (as_seq h1 b_tl == Seq.seq_of_list tl);
      assert (Seq.equal (as_seq h1 b) (Seq.append (as_seq h1 b_hd) (as_seq h1 b_tl)));
      assert ((Seq.seq_of_list l) == (Seq.cons hd (Seq.seq_of_list tl)))
