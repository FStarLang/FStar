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
module LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

private let srel_to_lsrel (#a:Type0) (len:nat) (pre:srel a) :P.preorder (Seq.lseq a len) = pre

(*
 * Counterpart of compatible_sub from the fsti but using sequences
 *
 * The patterns are guarded tightly, the proof of transitivity gets quite flaky otherwise
 * The cost is that we have to additional asserts as triggers
 *)
let compatible_sub_preorder (#a:Type0)
  (len:nat) (rel:srel a) (i:nat) (j:nat{i <= j /\ j <= len}) (sub_rel:srel a)
  = compatible_subseq_preorder len rel i j sub_rel

(*
 * Reflexivity of the compatibility relation
 *)
let lemma_seq_sub_compatilibity_is_reflexive (#a:Type0) (len:nat) (rel:srel a)
  :Lemma (compatible_sub_preorder len rel 0 len rel)
  = assert (forall (s1 s2:Seq.seq a). Seq.length s1 == Seq.length s2 ==>
                                 Seq.equal (Seq.replace_subseq s1 0 (Seq.length s1) s2) s2)

(*
 * Transitivity of the compatibility relation
 *
 * i2 and j2 are relative offsets within [i1, j1) (i.e. assuming i1 = 0)
 *)
let lemma_seq_sub_compatibility_is_transitive (#a:Type0)
  (len:nat) (rel:srel a) (i1 j1:nat) (rel1:srel a) (i2 j2:nat) (rel2:srel a)
  :Lemma (requires (i1 <= j1 /\ j1 <= len /\ i2 <= j2 /\ j2 <= j1 - i1 /\
                    compatible_sub_preorder len rel i1 j1 rel1 /\
                    compatible_sub_preorder (j1 - i1) rel1 i2 j2 rel2))
	 (ensures  (compatible_sub_preorder len rel (i1 + i2) (i1 + j2) rel2))
  = let t1 (s1 s2:Seq.seq a) = Seq.length s1 == len /\ Seq.length s2 == len /\ rel s1 s2 in
    let t2 (s1 s2:Seq.seq a) = t1 s1 s2 /\ rel2 (Seq.slice s1 (i1 + i2) (i1 + j2)) (Seq.slice s2 (i1 + i2) (i1 + j2)) in

    let aux0 (s1 s2:Seq.seq a) :Lemma (t1 s1 s2 ==> t2 s1 s2)
      = Classical.arrow_to_impl #(t1 s1 s2) #(t2 s1 s2)
          (fun _ ->
           assert (rel1 (Seq.slice s1 i1 j1) (Seq.slice s2 i1 j1));
	   assert (rel2 (Seq.slice (Seq.slice s1 i1 j1) i2 j2) (Seq.slice (Seq.slice s2 i1 j1) i2 j2));
	   assert (Seq.equal (Seq.slice (Seq.slice s1 i1 j1) i2 j2) (Seq.slice s1 (i1 + i2) (i1 + j2)));
	   assert (Seq.equal (Seq.slice (Seq.slice s2 i1 j1) i2 j2) (Seq.slice s2 (i1 + i2) (i1 + j2))))
    in


    let t1 (s s2:Seq.seq a) = Seq.length s == len /\ Seq.length s2 == j2 - i2 /\
                              rel2 (Seq.slice s (i1 + i2) (i1 + j2)) s2 in
    let t2 (s s2:Seq.seq a) = t1 s s2 /\ rel s (Seq.replace_subseq s (i1 + i2) (i1 + j2) s2) in
    let aux1 (s s2:Seq.seq a) :Lemma (t1 s s2 ==> t2 s s2)
      = Classical.arrow_to_impl #(t1 s s2) #(t2 s s2)
          (fun _ ->
           assert (Seq.equal (Seq.slice s (i1 + i2) (i1 + j2)) (Seq.slice (Seq.slice s i1 j1) i2 j2));
           assert (rel1 (Seq.slice s i1 j1) (Seq.replace_subseq (Seq.slice s i1 j1) i2 j2 s2));
	   assert (rel s (Seq.replace_subseq s i1 j1 (Seq.replace_subseq (Seq.slice s i1 j1) i2 j2 s2)));
	   assert (Seq.equal (Seq.replace_subseq s i1 j1 (Seq.replace_subseq (Seq.slice s i1 j1) i2 j2 s2))
	                     (Seq.replace_subseq s (i1 + i2) (i1 + j2) s2)))
    in

    Classical.forall_intro_2 aux0; Classical.forall_intro_2 aux1

noeq type mbuffer (a:Type0) (rrel:srel a) (rel:srel a) :Type0 =
  | Null
  | Buffer:
    max_length:U32.t ->
    content:HST.mreference (Seq.lseq a (U32.v max_length)) (srel_to_lsrel (U32.v max_length) rrel) ->
    idx:U32.t ->
    length:Ghost.erased U32.t{U32.v idx + U32.v (Ghost.reveal length) <= U32.v max_length} ->
    mbuffer a rrel rel

let g_is_null #_ #_ #_ b = Null? b

let mnull #_ #_ #_ = Null

let null_unique #_ #_ #_ _ = ()

let unused_in #_ #_ #_ b h =
  match b with
  | Null -> False
  | Buffer _ content _ _ -> content `HS.unused_in` h

let buffer_compatible (#t: Type) (#rrel #rel: srel t) (b: mbuffer t rrel rel) : GTot Type0 =
  match b with
  | Null -> True
  | Buffer max_length content idx length ->
      compatible_sub_preorder (U32.v max_length) rrel
        (U32.v idx) (U32.v idx + U32.v length) rel  //proof of compatibility

let live #_ #rrel #rel h b =
  match b with
  | Null -> True
  | Buffer max_length content idx length ->
      h `HS.contains` content /\
      buffer_compatible b

let live_null _ _ _ _ = ()

let live_is_null (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (g_is_null b == true))
         (ensures (live h b))
         [SMTPat (live h b)]
  = null_unique b;
    live_null a rrel rel h

let live_not_unused_in #_ #_ #_ _ _ = ()

let lemma_live_equal_mem_domains #_ #_ #_ _ _ _ = ()

let live_not_unused_in' (#a:Type0) (#rrel #rel:srel a) (h:HS.mem) (b:mbuffer a rrel rel)
  :Lemma (requires (live h b /\ b `unused_in` h))
         (ensures False)
         [SMTPat (live h b); SMTPat (b `unused_in` h)]
  = live_not_unused_in h b



let frameOf #_ #_ #_ b = if Null? b then HS.root else HS.frameOf (Buffer?.content b)

let as_addr #_ #_ #_  b = if g_is_null b then 0 else HS.as_addr (Buffer?.content b)

let unused_in_equiv #_ #_ #_ b h =
  if g_is_null b then Heap.not_addr_unused_in_nullptr (Map.sel (HS.get_hmap h) HS.root) else ()

let live_region_frameOf #_ #_ #_ _ _ = ()

let len #_ #_ #_ b =
  match b with
  | Null -> 0ul
  | Buffer _ _ _ len -> len

let len_null a _ _ = ()

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

let as_seq #_ #_ #_ h b =
  match b with
  | Null -> Seq.empty
  | Buffer max_len content idx len ->
    Seq.slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len)

let length_as_seq #_ #_ #_ _ _ = ()

let mbuffer_injectivity_in_first_preorder () = ()

let mgsub #a #rrel #rel sub_rel b i len =
  match b with
  | Null -> Null
  | Buffer max_len content idx length ->
    Buffer max_len content (U32.add idx i) (Ghost.hide len)

let live_gsub #_ #rrel #rel _ b i len sub_rel =
  match b with
  | Null -> ()
  | Buffer max_len content idx length ->
    let prf () : Lemma
      (requires (buffer_compatible b))
      (ensures (buffer_compatible (mgsub sub_rel b i len)))
    =
    lemma_seq_sub_compatibility_is_transitive (U32.v max_len) rrel
                                              (U32.v idx) (U32.v idx + U32.v length) rel
		         	              (U32.v i) (U32.v i + U32.v len) sub_rel
    in
    Classical.move_requires prf ()

let gsub_is_null #_ #_ #_ _ _ _ _ = ()

let len_gsub #_ #_ #_ _ _ _ _ = ()

let frameOf_gsub #_ #_ #_ _ _ _ _ = ()

let as_addr_gsub #_ #_ #_ _ _ _ _ = ()

let mgsub_inj #_ #_ #_ _ _ _ _ _ _ _ _ = ()

#push-options "--z3rlimit 20"
let gsub_gsub #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  let prf () : Lemma
    (requires (compatible_sub b i1 len1 sub_rel1 /\  compatible_sub (mgsub sub_rel1 b i1 len1) i2 len2 sub_rel2))
    (ensures (compatible_sub b (U32.add i1 i2) len2 sub_rel2))
  =
  lemma_seq_sub_compatibility_is_transitive (length b) rel (U32.v i1) (U32.v i1 + U32.v len1) sub_rel1
                                            (U32.v i2) (U32.v i2 + U32.v len2) sub_rel2
  in
  Classical.move_requires prf ()
#pop-options

/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

let gsub_zero_length #_ #_ #rel b = lemma_seq_sub_compatilibity_is_reflexive (length b) rel

let as_seq_gsub #_ #_ #_ h b i len _ =
  match b with
  | Null -> ()
  | Buffer _ content idx len0 ->
    Seq.slice_slice (HS.sel h content) (U32.v idx) (U32.v idx + U32.v len0) (U32.v i) (U32.v i + U32.v len)

let lemma_equal_instances_implies_equal_types (a:Type) (b:Type) (s1:Seq.seq a) (s2:Seq.seq b)
  : Lemma (requires s1 === s2)
          (ensures a == b)
  = Seq.lemma_equal_instances_implies_equal_types ()

let s_lemma_equal_instances_implies_equal_types (_:unit)
  : Lemma (forall (a:Type) (b:Type) (s1:Seq.seq a) (s2:Seq.seq b).
          {:pattern (has_type s1 (Seq.seq a));
                    (has_type s2 (Seq.seq b)) }
          s1 === s2 ==> a == b)
  = Seq.lemma_equal_instances_implies_equal_types()
  
let live_same_addresses_equal_types_and_preorders'
  (#a1 #a2: Type0)
  (#rrel1 #rel1: srel a1)
  (#rrel2 #rel2: srel a2)
  (b1: mbuffer a1 rrel1 rel1)
  (b2: mbuffer a2 rrel2 rel2)
  (h: HS.mem)
: Lemma
  (requires 
    frameOf b1 == frameOf b2 /\
    as_addr b1 == as_addr b2 /\
    live h b1 /\
    live h b2 /\
    (~ (g_is_null b1 /\ g_is_null b2)))
  (ensures 
    a1 == a2 /\
    rrel1 == rrel2)
=   Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    let s1 : Seq.seq a1 = as_seq h b1 in
    assert (Seq.seq a1 == Seq.seq a2);
    let s1' : Seq.seq a2 = coerce_eq _ s1 in
    assert (s1 === s1');
    lemma_equal_instances_implies_equal_types a1 a2 s1 s1'

let live_same_addresses_equal_types_and_preorders
  #_ #_ #_ #_ #_ #_ b1 b2 h
= Classical.move_requires (live_same_addresses_equal_types_and_preorders' b1 b2) h

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
  ((frameOf b' == r /\ as_addr b' == a) ==> (
    (live h b' ==> live h' b') /\ (
    ((live h b' /\ live h' b' /\ Buffer? b') ==> (
    let ({ b_max_length = bmax; b_offset = boff; b_length = blen }) = Ghost.reveal b in
    let Buffer max _ idx len = b' in (
      U32.v max == bmax /\
      U32.v idx <= boff /\
      boff + blen <= U32.v idx + U32.v len
    ) ==>
    Seq.equal (Seq.slice (as_seq h b') (boff - U32.v idx) (boff - U32.v idx + blen)) (Seq.slice (as_seq h' b') (boff - U32.v idx) (boff - U32.v idx + blen))
  )))))

val ubuffer_preserved (#r: HS.rid) (#a: nat) (b: ubuffer r a) (h h' : HS.mem) : GTot Type0

let ubuffer_preserved = ubuffer_preserved'

let ubuffer_preserved_intro
  (#r:HS.rid)
  (#a:nat)
  (b:ubuffer r a)
  (h h' :HS.mem)
  (f0: (
    (t':Type0) ->
    (rrel:srel t') -> (rel:srel t') ->
    (b':mbuffer t' rrel rel) ->
    Lemma
    (requires (frameOf b' == r /\ as_addr b' == a /\ live h b'))
    (ensures (live h' b'))
  ))
  (f: (
    (t':Type0) ->
    (rrel:srel t') -> (rel:srel t') ->
    (b':mbuffer t' rrel rel) ->
    Lemma
    (requires (
      frameOf b' == r /\ as_addr b' == a /\
      live h b' /\ live h' b' /\
      Buffer? b' /\ (
      let ({ b_max_length = bmax; b_offset = boff; b_length = blen }) = Ghost.reveal b in
      let Buffer max _ idx len = b' in (
        U32.v max == bmax /\
        U32.v idx <= boff /\
        boff + blen <= U32.v idx + U32.v len
    ))))
    (ensures (
      Buffer? b' /\ (
      let ({ b_max_length = bmax; b_offset = boff; b_length = blen }) = Ghost.reveal b in
      let Buffer max _ idx len = b' in
        U32.v max == bmax /\
        U32.v idx <= boff /\
        boff + blen <= U32.v idx + U32.v len /\
      Seq.equal (Seq.slice (as_seq h b') (boff - U32.v idx) (boff - U32.v idx + blen)) (Seq.slice (as_seq h' b') (boff - U32.v idx) (boff - U32.v idx + blen))
    )))
  ))
: Lemma
  (ubuffer_preserved b h h')
= let g'
    (t':Type0) (rrel rel:srel t')
    (b':mbuffer t' rrel rel)
  : Lemma
  ((frameOf b' == r /\ as_addr b' == a) ==> (
    (live h b' ==> live h' b') /\ (
    ((live h b' /\ live h' b' /\ Buffer? b') ==> (
    let ({ b_max_length = bmax; b_offset = boff; b_length = blen }) = Ghost.reveal b in
    let Buffer max _ idx len = b' in (
      U32.v max == bmax /\
      U32.v idx <= boff /\
      boff + blen <= U32.v idx + U32.v len
    ) ==>
    Seq.equal (Seq.slice (as_seq h b') (boff - U32.v idx) (boff - U32.v idx + blen)) (Seq.slice (as_seq h' b') (boff - U32.v idx) (boff - U32.v idx + blen))
  )))))
  = Classical.move_requires (f0 t' rrel rel) b';
    Classical.move_requires (f t' rrel rel) b'
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
  ubuffer_preserved_intro b h1 h2
  (fun t' _ _ b' ->
    if Null? b'
    then ()
    else
      f _ _ (Buffer?.content b')
  )
  (fun t' _ _ b' ->
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

let ubuffer_of_buffer_from_to_none_cond
  #a #rrel #rel (b: mbuffer a rrel rel) from to
: GTot bool
= g_is_null b || U32.v to < U32.v from || U32.v from > length b

let ubuffer_of_buffer_from_to
  #a #rrel #rel (b: mbuffer a rrel rel) from to
: GTot (ubuffer (frameOf b) (as_addr b))
= if  ubuffer_of_buffer_from_to_none_cond b from to
  then
      Ghost.hide ({
        b_max_length = 0;
        b_offset = 0;
        b_length = 0;
        b_is_mm = false;
      })
  else
    let to' = if U32.v to > length b then length b else U32.v to in
    let b1 = ubuffer_of_buffer b in
    Ghost.hide ({ Ghost.reveal b1 with b_offset = (Ghost.reveal b1).b_offset + U32.v from; b_length = to' - U32.v from })

val ubuffer_preserved_elim (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h h':HS.mem)
  :Lemma (requires (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h' /\ live h b))
         (ensures (live h' b /\ as_seq h b == as_seq h' b))

let ubuffer_preserved_elim #_ #_ #_ _ _ _ = ()

val ubuffer_preserved_from_to_elim (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h h' : HS.mem)
  :Lemma (requires (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to) h h' /\ live h b))
         (ensures (live h' b /\ ((U32.v from <= U32.v to /\ U32.v to <= length b) ==> Seq.slice (as_seq h b) (U32.v from) (U32.v to) == Seq.slice (as_seq h' b) (U32.v from) (U32.v to))))

let ubuffer_preserved_from_to_elim #_ #_ #_ _ _ _ _ _ = ()

let unused_in_ubuffer_preserved (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h h':HS.mem)
  : Lemma (requires (b `unused_in` h))
          (ensures (ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'))
  = Classical.move_requires (fun b -> live_not_unused_in h b) b;
    live_null a rrel rel h;
    null_unique b;
    unused_in_equiv b h;
    addr_unused_in_ubuffer_preserved #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) h h'

let ubuffer_includes' (larger smaller: ubuffer_) : GTot Type0 =
  larger.b_is_mm == smaller.b_is_mm /\
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

(* TODO: added this because of #606, now that it is fixed, we may not need it anymore *)
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
  if x1.b_length = 0 || x2.b_length = 0
  then True
  else
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

(* TODO: added this because of #606, now that it is fixed, we may not need it anymore *)
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

let modifies_1_from_to_preserves_ubuffers (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem)
  : GTot Type0
  = forall (b':ubuffer (frameOf b) (as_addr b)).
      (ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to) b') ==> ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2

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

let modifies_1_from_to (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem)
  : GTot Type0
  = if ubuffer_of_buffer_from_to_none_cond b from to
    then modifies_0 h1 h2
    else
      modifies_0_preserves_regions h1 h2 /\
      modifies_1_preserves_mreferences b h1 h2 /\
      modifies_1_preserves_livenesses b h1 h2 /\
      modifies_0_preserves_not_unused_in h1 h2 /\
      modifies_1_from_to_preserves_ubuffers b from to h1 h2

val modifies_1_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r)) (ensures (HS.live_region h2 r))

let modifies_1_live_region #_ #_ #_ _ _ _ _ = ()

let modifies_1_from_to_live_region (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem) (r:HS.rid)
  :Lemma (requires (modifies_1_from_to b from to h1 h2 /\ HS.live_region h1 r)) (ensures (HS.live_region h2 r))
= ()

val modifies_1_liveness
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  :Lemma (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r')) (ensures (h2 `HS.contains` r'))

let modifies_1_liveness #_ #_ #_ _ _ _ #_ #_ _ = ()

let modifies_1_from_to_liveness
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r':HS.mreference a' pre)
  :Lemma (requires (modifies_1_from_to b from to h1 h2 /\ h1 `HS.contains` r')) (ensures (h2 `HS.contains` r'))
= ()

val modifies_1_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  :Lemma (requires (modifies_1 b h1 h2 /\
                    HS.live_region h1 r /\ HS.live_region h2 r /\
                    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
         (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
let modifies_1_unused_in #_ #_ #_ _ _ _ _ _ = ()

let modifies_1_from_to_unused_in (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem) (r:HS.rid) (n:nat)
  :Lemma (requires (modifies_1_from_to b from to h1 h2 /\
                    HS.live_region h1 r /\ HS.live_region h2 r /\
                    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)))
         (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
= ()

val modifies_1_mreference
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r': HS.mreference a' pre)
  : Lemma (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
let modifies_1_mreference #_ #_ #_ _ _ _ #_ #_ _ = ()

let modifies_1_from_to_mreference
  (#a:Type0) (#rrel:srel a) (#rel:srel a) (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem)
  (#a':Type0) (#pre:Preorder.preorder a') (r': HS.mreference a' pre)
  : Lemma (requires (modifies_1_from_to b from to h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
          (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
= ()

val modifies_1_ubuffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (h1 h2:HS.mem) (b':ubuffer (frameOf b) (as_addr b))
  : Lemma (requires (modifies_1 b h1 h2 /\ ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) b'))
          (ensures  (ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))
let modifies_1_ubuffer #_ #_ #_ _ _ _ _ = ()

let modifies_1_from_to_ubuffer (#a:Type0) (#rrel:srel a) (#rel:srel a)
  (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem) (b':ubuffer (frameOf b) (as_addr b))
  : Lemma (requires (modifies_1_from_to b from to h1 h2 /\ ubuffer_disjoint #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to) b'))
          (ensures  (ubuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))
= ()

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

let loc = MG.loc cls
let _ = intro_ambient loc

let loc_none = MG.loc_none
let _ = intro_ambient loc_none

let loc_union = MG.loc_union
let _ = intro_ambient loc_union

let loc_union_idem = MG.loc_union_idem

let loc_union_comm = MG.loc_union_comm

let loc_union_assoc = MG.loc_union_assoc

let loc_union_idem_1
  (s1 s2: loc)
: Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2))]
= loc_union_assoc s1 s1 s2

let loc_union_idem_2
  (s1 s2: loc)
: Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]
= loc_union_assoc s1 s2 s2

let loc_union_loc_none_l = MG.loc_union_loc_none_l

let loc_union_loc_none_r = MG.loc_union_loc_none_r

let loc_buffer_from_to #a #rrel #rel b from to =
  if ubuffer_of_buffer_from_to_none_cond b from to
  then MG.loc_none
  else
    MG.loc_of_aloc #_ #_ #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to)

let loc_buffer #_ #_ #_ b =
  if g_is_null b then MG.loc_none
  else MG.loc_of_aloc #_ #_ #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_buffer_eq #_ #_ #_ _ = ()

let loc_buffer_from_to_high #_ #_ #_ _ _ _ = ()

let loc_buffer_from_to_none #_ #_ #_ _ _ _ = ()

let loc_buffer_from_to_mgsub #_ #_ #_ _ _ _ _ _ _ = ()

let loc_buffer_mgsub_eq #_ #_ #_ _ _ _ _ = ()

let loc_buffer_null _ _ _ = ()

let loc_buffer_from_to_eq #_ #_ #_ _ _ _ = ()

let loc_buffer_mgsub_rel_eq #_ #_ #_ _ _ _ _ _ = ()

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_trans_backwards
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]
= loc_includes_trans s1 s2 s3


let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_union_l'
  (s1 s2 s: loc)
  : Lemma
      (requires (loc_includes s1 s \/ loc_includes s2 s))
      (ensures (loc_includes (loc_union s1 s2) s))
      [SMTPat (loc_includes (loc_union s1 s2) s)]
  = loc_includes_union_l s1 s2 s

let loc_includes_union_r'
  (s s1 s2: loc)
: Lemma
  (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
  [SMTPat (loc_includes s (loc_union s1 s2))]
= Classical.move_requires (loc_includes_union_r s s1) s2;
  Classical.move_requires (loc_includes_union_l s1 s2) s1;
  Classical.move_requires (loc_includes_union_l s1 s2) s2;
  Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s1;
  Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s2

let loc_includes_none = MG.loc_includes_none

val loc_includes_buffer (#a:Type0) (#rrel1:srel a) (#rrel2:srel a) (#rel1:srel a) (#rel2:srel a)
  (b1:mbuffer a rrel1 rel1) (b2:mbuffer a rrel2 rel2)
  :Lemma (requires (frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2 /\
                    ubuffer_includes0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures  (loc_includes (loc_buffer b1) (loc_buffer b2)))
let loc_includes_buffer #t #_ #_ #_ #_ b1 b2 =
  let t1 = ubuffer (frameOf b1) (as_addr b1) in
  MG.loc_includes_aloc #_ #cls #(frameOf b1) #(as_addr b1) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let loc_includes_gsub_buffer_r l #_ #_ #_ b i len sub_rel =
  let b' = mgsub sub_rel b i len in
  loc_includes_buffer b b';
  loc_includes_trans l (loc_buffer b) (loc_buffer b')

let loc_includes_gsub_buffer_r' (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (i:UInt32.t) (len:UInt32.t) (sub_rel:srel a)
  :Lemma (requires (UInt32.v i + UInt32.v len <= (length b)))
         (ensures  (loc_includes (loc_buffer b) (loc_buffer (mgsub sub_rel b i len))))
         [SMTPat (mgsub sub_rel b i len)]
  = ()

let loc_includes_gsub_buffer_l #_ #_ #rel b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  let b1 = mgsub sub_rel1 b i1 len1 in
  let b2 = mgsub sub_rel2 b i2 len2 in
  loc_includes_buffer b1 b2

let loc_includes_loc_buffer_loc_buffer_from_to #_ #_ #_ b from to =
  if ubuffer_of_buffer_from_to_none_cond b from to
  then ()
  else MG.loc_includes_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) (ubuffer_of_buffer_from_to b from to)

let loc_includes_loc_buffer_from_to #_ #_ #_ b from1 to1 from2 to2 =
  if ubuffer_of_buffer_from_to_none_cond b from1 to1 || ubuffer_of_buffer_from_to_none_cond b from2 to2
  then ()
  else MG.loc_includes_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from1 to1) (ubuffer_of_buffer_from_to b from2 to2)

#push-options "--z3rlimit 20"
let loc_includes_as_seq #_ #rrel #_ #_ h1 h2 larger smaller =
  if Null? smaller then () else
  if Null? larger then begin
    MG.loc_includes_none_elim (loc_buffer smaller);
    MG.loc_of_aloc_not_none #_ #cls #(frameOf smaller) #(as_addr smaller) (ubuffer_of_buffer smaller)
  end else begin
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller);
    let ul = Ghost.reveal (ubuffer_of_buffer larger) in
    let us = Ghost.reveal (ubuffer_of_buffer smaller) in
    assert (as_seq h1 smaller == Seq.slice (as_seq h1 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller));
    assert (as_seq h2 smaller == Seq.slice (as_seq h2 larger) (us.b_offset - ul.b_offset) (us.b_offset - ul.b_offset + length smaller))
  end
#pop-options

let loc_includes_addresses_buffer #a #rrel #srel preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(as_addr p) (ubuffer_of_buffer p)

let loc_includes_addresses_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_addresses true (frameOf b) (Set.singleton (as_addr b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()

let loc_includes_region_buffer #_ #_ #_ preserve_liveness s b =
  MG.loc_includes_region_aloc #_ #cls preserve_liveness s #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let loc_includes_region_buffer' (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  :Lemma (loc_includes (loc_regions true (Set.singleton (frameOf b))) (loc_buffer b))
         [SMTPat (loc_buffer b)]
  = ()

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_addresses'
  (preserve_liveness: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (loc_includes (loc_regions true (Set.singleton r)) (loc_addresses preserve_liveness r a))
  [SMTPat (loc_addresses preserve_liveness r a)]
= ()

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_region'
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions false s) (loc_regions preserve_liveness s))
  [SMTPat (loc_regions preserve_liveness s)]
= ()

let loc_includes_region_union_l = MG.loc_includes_region_union_l

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

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]
= Classical.move_requires (loc_disjoint_sym s1) s2;
  Classical.move_requires (loc_disjoint_sym s2) s1

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

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

val loc_disjoint_buffer (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires ((frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2) ==>
                    ubuffer_disjoint0 #(frameOf b1) #(frameOf b2) #(as_addr b1) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)))
         (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))
let loc_disjoint_buffer #_ #_ #_ #_ #_ #_ b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]
  = loc_disjoint_includes b1 b2 b1 b2'

let loc_disjoint_gsub_buffer #_ #_ #_ b i1 len1 sub_rel1 i2 len2 sub_rel2 =
  loc_disjoint_buffer (mgsub sub_rel1 b i1 len1) (mgsub sub_rel2 b i2 len2)

let loc_disjoint_loc_buffer_from_to #_ #_ #_ b from1 to1 from2 to2 =
  if ubuffer_of_buffer_from_to_none_cond b from1 to1 || ubuffer_of_buffer_from_to_none_cond b from2 to2
  then ()
  else MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b) #(as_addr b) #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from1 to1) (ubuffer_of_buffer_from_to b from2 to2)

let loc_disjoint_addresses = MG.loc_disjoint_addresses_intro #_ #cls

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_live_region = MG.modifies_live_region

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #_ #_ #_ b p h h' =
  if g_is_null b
  then
    assert (as_seq h b `Seq.equal` as_seq h' b)
  else begin
    MG.modifies_aloc_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b) p h h' ;
    ubuffer_preserved_elim b h h'
  end

let modifies_buffer_from_to_elim #_ #_ #_ b from to p h h' =
  if g_is_null b
  then ()
  else begin
    MG.modifies_aloc_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to) p h h' ;
    ubuffer_preserved_from_to_elim b from to h h'
  end

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _

let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

let region_liveness_insensitive_buffer #_ #_ #_ b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer b)

let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

let modifies_liveness_insensitive_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x then ()
  else
    liveness_preservation_intro h h' x (fun t' pre r ->
      MG.modifies_preserves_liveness_strong l1 l2 h h' r (ubuffer_of_buffer x))

let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

let modifies_liveness_insensitive_region_buffer l1 l2 h h' #_ #_ #_ x =
  if g_is_null x then ()
  else MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(frameOf x) #(as_addr x) (ubuffer_of_buffer x)

let modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' x)];
  ]]
= modifies_liveness_insensitive_region loc_none l2 h h' x

let modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
  : Lemma (requires (modifies l2 h h' /\
                     region_liveness_insensitive_locs `loc_includes` l2 /\
		     HS.live_region h (HS.frameOf x)))
          (ensures (HS.live_region h' (HS.frameOf x)))
          [SMTPatOr [
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
          ]]
  = modifies_liveness_insensitive_region_mreference loc_none l2 h h' x

let modifies_liveness_insensitive_region_buffer_weak
  (l2:loc)
  (h h':HS.mem)
  (#a:Type0) (#rrel #rel:srel a)
  (x:mbuffer a rrel rel)
  :Lemma (requires (modifies l2 h h' /\
                    region_liveness_insensitive_locs `loc_includes` l2 /\
		    HS.live_region h (frameOf x)))
         (ensures  (HS.live_region h' (frameOf x)))
         [SMTPatOr [
           [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (frameOf x))];
           [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (frameOf x))];
         ]]
  = modifies_liveness_insensitive_region_buffer loc_none l2 h h' x

let modifies_trans = MG.modifies_trans

let modifies_trans_linear (l l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies l h1 h2 /\ modifies l_goal h2 h3 /\ l_goal `loc_includes` l))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (modifies l h1 h2); SMTPat (modifies l_goal h1 h3)]
  = modifies_trans l h1 h2 l_goal h3

let modifies_only_live_regions = MG.modifies_only_live_regions

let no_upd_fresh_region = MG.no_upd_fresh_region

let new_region_modifies = MG.new_region_modifies #_ cls

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro #_ #cls

let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

let modifies_free = MG.modifies_free #_ #cls

let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

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

val modifies_1_from_to_modifies
  (#a:Type0)(#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (from to: U32.t) (h1 h2:HS.mem)
  :Lemma (requires (modifies_1_from_to b from to h1 h2))
         (ensures  (modifies (loc_buffer_from_to b from to) h1 h2))
let modifies_1_from_to_modifies #t #_ #_ b from to h1 h2 =
  if ubuffer_of_buffer_from_to_none_cond b from to
  then begin
    modifies_0_modifies h1 h2
  end else
   MG.modifies_intro (loc_buffer_from_to b from to) h1 h2
    (fun r -> modifies_1_from_to_live_region b from to h1 h2 r)
    (fun t pre p ->
      loc_disjoint_sym (loc_mreference p) (loc_buffer_from_to b from to);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(frameOf b) #(as_addr b) (ubuffer_of_buffer_from_to b from to) true (HS.frameOf p) (Set.singleton (HS.as_addr p));
      modifies_1_from_to_mreference b from to h1 h2 p
    )
    (fun t pre p ->
      modifies_1_from_to_liveness b from to h1 h2 p
    )
    (fun r n ->
      modifies_1_from_to_unused_in b from to h1 h2 r n
    )
    (fun r' a' b' ->
      loc_disjoint_sym (MG.loc_of_aloc b') (loc_buffer_from_to b from to);
      MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b) #(as_addr b)  #r' #a' (ubuffer_of_buffer_from_to b from to)  b';
      if frameOf b = r' && as_addr b = a'
      then
        modifies_1_from_to_ubuffer #t b from to h1 h2 b'
      else
        same_mreference_ubuffer_preserved #r' #a' b' h1 h2
          (fun a_ pre_ r_ -> modifies_1_from_to_mreference b from to h1 h2 r_)
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

val modifies_loc_buffer_from_to_intro'
  (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel)
  (from to: U32.t)
  (l: loc) (h h' : HS.mem)
: Lemma
  (requires (
    let s = as_seq h b in
    let s' = as_seq h' b in
    not (g_is_null b) /\
    live h b /\
    modifies (loc_union l (loc_buffer b)) h h' /\
    U32.v from <= U32.v to /\
    U32.v to <= length b /\
    Seq.slice s 0 (U32.v from) `Seq.equal` Seq.slice s' 0 (U32.v from) /\
    Seq.slice s (U32.v to) (length b) `Seq.equal` Seq.slice s' (U32.v to) (length b)
  ))
  (ensures (modifies (loc_union l (loc_buffer_from_to b from to)) h h'))

#push-options "--z3rlimit 16"

let modifies_loc_buffer_from_to_intro' #a #rrel #rel b from to l h h' =
  let r0 = frameOf b in
  let a0 = as_addr b in
  let bb : ubuffer r0 a0 = ubuffer_of_buffer b in
  modifies_loc_includes (loc_union l (loc_addresses true r0 (Set.singleton a0))) h h' (loc_union l (loc_buffer b));
  MG.modifies_strengthen l #r0 #a0 (ubuffer_of_buffer_from_to b from to) h h' (fun f (x: ubuffer r0 a0) ->
    ubuffer_preserved_intro x h h'
      (fun t' rrel' rel' b' -> f _ _ (Buffer?.content b'))
      (fun t' rrel' rel' b' ->
        // prove that the types, rrels, rels are equal
        Heap.lemma_distinct_addrs_distinct_preorders ();
        Heap.lemma_distinct_addrs_distinct_mm ();
        assert (Seq.seq t' == Seq.seq a);
        let _s0 : Seq.seq a = as_seq h b in
        let _s1 : Seq.seq t' = coerce_eq _ _s0 in
        lemma_equal_instances_implies_equal_types a t' _s0 _s1;
        let boff = U32.v (Buffer?.idx b) in
        let from_ = boff + U32.v from in
        let to_ = boff + U32.v to in
        let ({ b_max_length = ml; b_offset = xoff; b_length = xlen; b_is_mm = is_mm }) = Ghost.reveal x in
        let ({ b_max_length = _; b_offset = b'off; b_length = b'len }) = Ghost.reveal (ubuffer_of_buffer b') in
        let bh = as_seq h b in
        let bh' = as_seq h' b in
        let xh = Seq.slice (as_seq h b') (xoff - b'off) (xoff - b'off + xlen) in
        let xh' = Seq.slice (as_seq h' b') (xoff - b'off) (xoff - b'off + xlen) in
        let prf (i: nat) : Lemma
          (requires (i < xlen))
          (ensures (i < xlen /\ Seq.index xh i == Seq.index xh' i))
        = let xi = xoff + i in
          let bi : ubuffer r0 a0 =
            Ghost.hide ({ b_max_length = ml; b_offset = xi; b_length = 1; b_is_mm = is_mm; })
          in
          assert (Seq.index xh i == Seq.index (Seq.slice (as_seq h b') (xi - b'off) (xi - b'off + 1)) 0);
          assert (Seq.index xh' i == Seq.index (Seq.slice (as_seq h' b') (xi - b'off) (xi - b'off + 1)) 0);
          let li = MG.loc_of_aloc bi in
          MG.loc_includes_aloc #_ #cls x bi;
          loc_disjoint_includes l (MG.loc_of_aloc x) l li;
          if xi < boff || boff + length b <= xi
          then begin
            MG.loc_disjoint_aloc_intro #_ #cls bb bi;
            assert (loc_disjoint (loc_union l (loc_buffer b)) li);
            MG.modifies_aloc_elim bi (loc_union l (loc_buffer b)) h h'
          end else
          if xi < from_
          then begin
            assert (Seq.index xh i == Seq.index (Seq.slice bh 0 (U32.v from)) (xi - boff));
            assert (Seq.index xh' i == Seq.index (Seq.slice bh' 0 (U32.v from)) (xi - boff))
          end else begin
            assert (to_ <= xi);
            assert (Seq.index xh i == Seq.index (Seq.slice bh (U32.v to) (length b)) (xi - to_));
            assert (Seq.index xh' i == Seq.index (Seq.slice bh' (U32.v to) (length b)) (xi - to_))
          end
        in
        Classical.forall_intro (Classical.move_requires prf);
        assert (xh `Seq.equal` xh')
      )
  )

#pop-options

let modifies_loc_buffer_from_to_intro #a #rrel #rel b from to l h h' =
  if g_is_null b
  then ()
  else modifies_loc_buffer_from_to_intro' b from to l h h'

let does_not_contain_addr = MG.does_not_contain_addr

let not_live_region_does_not_contain_addr = MG.not_live_region_does_not_contain_addr

let unused_in_does_not_contain_addr = MG.unused_in_does_not_contain_addr

let addr_unused_in_does_not_contain_addr = MG.addr_unused_in_does_not_contain_addr

let free_does_not_contain_addr = MG.free_does_not_contain_addr

let does_not_contain_addr_elim = MG.does_not_contain_addr_elim

let modifies_only_live_addresses = MG.modifies_only_live_addresses

let loc_not_unused_in = MG.loc_not_unused_in _

let loc_unused_in = MG.loc_unused_in _

let loc_regions_unused_in = MG.loc_regions_unused_in cls

let loc_unused_in_not_unused_in_disjoint =
  MG.loc_unused_in_not_unused_in_disjoint cls

let not_live_region_loc_not_unused_in_disjoint = MG.not_live_region_loc_not_unused_in_disjoint cls

let fresh_frame_loc_not_unused_in_disjoint
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (loc_disjoint (loc_region_only false (HS.get_tip h1)) (loc_not_unused_in h0)))
  [SMTPat (HS.fresh_frame h0 h1)]
= not_live_region_loc_not_unused_in_disjoint h0 (HS.get_tip h1)

let live_loc_not_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.does_not_contain_addr_addr_unused_in h) (frameOf b, as_addr b);
  MG.loc_addresses_not_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let unused_in_loc_unused_in #_ #_ #_ b h =
  unused_in_equiv b h;
  Classical.move_requires (MG.addr_unused_in_does_not_contain_addr h) (frameOf b, as_addr b);
  MG.loc_addresses_unused_in cls (frameOf b) (Set.singleton (as_addr b)) h;
  ()

let modifies_address_liveness_insensitive_unused_in =
  MG.modifies_address_liveness_insensitive_unused_in cls

let modifies_only_not_unused_in = MG.modifies_only_not_unused_in

let mreference_live_loc_not_unused_in =
  MG.mreference_live_loc_not_unused_in cls

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

let modifies_loc_unused_in l h1 h2 l' =
  modifies_loc_includes address_liveness_insensitive_locs h1 h2 l;
  modifies_address_liveness_insensitive_unused_in h1 h2;
  loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'

let ralloc_post_fresh_loc (#a:Type) (#rel:Preorder.preorder a) (i: HS.rid) (init:a) (m0: HS.mem)
                       (x: HST.mreference a rel{HST.is_eternal_region (HS.frameOf x)}) (m1: HS.mem) : Lemma
    (requires (HST.ralloc_post i init m0 x m1))
    (ensures (fresh_loc (loc_freed_mreference x) m0 m1))
    [SMTPat (HST.ralloc_post i init m0 x m1)]
=  ()

let fresh_frame_modifies h0 h1 = MG.fresh_frame_modifies #_ cls h0 h1

let popped_modifies = MG.popped_modifies #_ cls

let modifies_remove_new_locs l_fresh l_aux l_goal h1 h2 h3 =
  modifies_only_not_unused_in l_goal h1 h3

let modifies_remove_fresh_frame (h1 h2 h3:HS.mem) (l:loc)
  : Lemma (requires (HS.fresh_frame h1 h2 /\
                     modifies (loc_union (loc_all_regions_from false (HS.get_tip h2)) l) h2 h3))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies l h1 h3); SMTPat (HS.fresh_frame h1 h2)]
  = loc_regions_unused_in h1 (HS.mod_set (Set.singleton (HS.get_tip h2)));
    modifies_only_not_unused_in l h1 h3

let disjoint_neq #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2 then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()

let empty_disjoint
  #t1 #t2 #rrel1 #rel1 #rrel2 #rel2 b1 b2
= let r = frameOf b1 in
  let a = as_addr b1 in
  if r = frameOf b2 && a = as_addr b2 then
    MG.loc_disjoint_aloc_intro #_ #cls #r #a #r #a (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)
  else ()

(*
let includes_live #a #rrel #rel1 #rel2 h larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)
*)

let includes_frameOf_as_addr #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)

let pointer_distinct_sel_disjoint #a #_ #_ #_ #_ b1 b2 h =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2
  then begin
    HS.mreference_distinct_sel_disjoint h (Buffer?.content b1) (Buffer?.content b2);
    loc_disjoint_buffer b1 b2
  end
  else
    loc_disjoint_buffer b1 b2

let is_null #_ #_ #_ b = Null? b

let msub #a #rrel #rel sub_rel b i len =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len0 ->
    Buffer max_len content (U32.add i0 i) len

let moffset #a #rrel #rel sub_rel b i =
  match b with
  | Null -> Null
  | Buffer max_len content i0 len ->
    Buffer max_len content (U32.add i0 i) (Ghost.hide ((U32.sub (Ghost.reveal len) i)))

let index #_ #_ #_ b i =
  let open HST in
  let s = ! (Buffer?.content b) in
  Seq.index s (U32.v (Buffer?.idx b) + U32.v i)

let g_upd_seq #_ #_ #_ b s h =
  if Seq.length s = 0 then h
  else
    let s0 = HS.sel h (Buffer?.content b) in
    let Buffer _ content idx length = b in
    HS.upd h (Buffer?.content b) (Seq.replace_subseq s0 (U32.v idx) (U32.v idx + U32.v length) s)

let lemma_g_upd_with_same_seq #_ #_ #_ b h =
  if Null? b then ()
  else
    let open FStar.UInt32 in
    let Buffer _ content idx length = b in
    let s = HS.sel h content in
    assert (Seq.equal (Seq.replace_subseq s (v idx) (v idx + v length) (Seq.slice s (v idx) (v idx + v length))) s);
    HS.lemma_heap_equality_upd_with_sel h (Buffer?.content b)

#push-options "--z3rlimit 48"
let g_upd_seq_as_seq #a #_ #_ b s h =
  let h' = g_upd_seq b s h in
  if g_is_null b then assert (Seq.equal s Seq.empty)
  else begin
    assert (Seq.equal (as_seq h' b) s);
    // prove modifies_1_preserves_ubuffers
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    s_lemma_equal_instances_implies_equal_types ();
    modifies_1_modifies b h h'
  end

let g_upd_modifies_strong #_ #_ #_ b i v h =
  let h' = g_upd b i v h in
    // prove modifies_1_from_to_preserves_ubuffers
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    s_lemma_equal_instances_implies_equal_types ();
    modifies_1_from_to_modifies b (U32.uint_to_t i) (U32.uint_to_t (i + 1)) h h'
#pop-options

let upd' #_ #_ #_ b i v =
  let open HST in
  let h = get() in
  let Buffer max_length content idx len = b in
  let s0 = !content in
  let sb0 = Seq.slice s0 (U32.v idx) (U32.v max_length) in
  let s_upd = Seq.upd sb0 (U32.v i) v in
  let sf = Seq.replace_subseq s0 (U32.v idx) (U32.v max_length) s_upd in
  assert (sf `Seq.equal`
    Seq.replace_subseq s0 (U32.v idx) (U32.v idx + U32.v len) (Seq.upd (as_seq h b) (U32.v i) v));
  content := sf

let recallable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) :GTot Type0 =
  (not (g_is_null b)) ==> (
    HST.is_eternal_region (frameOf b) /\
    not (HS.is_mm (Buffer?.content b)) /\
    buffer_compatible b
  )

let region_lifetime_buf #_ #_ #_ b =
  (not (g_is_null b)) ==> (
    HS.is_heap_color (HS.color (frameOf b)) /\
    not (HS.is_mm (Buffer?.content b)) /\
    buffer_compatible b
  )

let region_lifetime_sub #a #rrel #rel #subrel b0 b1 =
  match b1 with
  | Null -> ()
  | Buffer max_len content idx length ->
    assert (forall (len:nat) (i:nat) (j:nat{i <= j /\ j <= len}). compatible_sub_preorder len rrel i j subrel)

let recallable_null #_ #_ #_ = ()

let recallable_mgsub #_ #rrel #rel b i len sub_rel =
  match b with
  | Null -> ()
  | Buffer max_len content idx length ->
    lemma_seq_sub_compatibility_is_transitive (U32.v max_len) rrel
                                              (U32.v idx) (U32.v idx + U32.v length) rel
		         	              (U32.v i) (U32.v i + U32.v len) sub_rel

(*
let recallable_includes #_ #_ #_ #_ #_ #_ larger smaller =
  if Null? larger || Null? smaller then ()
  else
    MG.loc_includes_aloc_elim #_ #cls #(frameOf larger) #(frameOf smaller) #(as_addr larger) #(as_addr smaller) (ubuffer_of_buffer larger) (ubuffer_of_buffer smaller)
*)

let recall #_ #_ #_ b = if Null? b then () else HST.recall (Buffer?.content b)

private let spred_as_mempred (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (p:spred a)
  :HST.mem_predicate
  = fun h ->
    buffer_compatible b ==>
    p (as_seq h b)

let witnessed #_ #rrel #rel b p =
  match b with
  | Null -> p Seq.empty
  | Buffer max_length content idx length ->
    HST.token_p content (spred_as_mempred b p)

private let lemma_stable_on_rel_is_stable_on_rrel (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (p:spred a)
  :Lemma (requires (Buffer? b /\ stable_on p rel))
         (ensures  (HST.stable_on (spred_as_mempred b p) (Buffer?.content b)))
  = let Buffer max_length content idx length = b in
    let mp = spred_as_mempred b p in
    let aux (h0 h1:HS.mem) :Lemma ((mp h0 /\ rrel (HS.sel h0 content) (HS.sel h1 content)) ==> mp h1)
      = Classical.arrow_to_impl #(mp h0 /\ rrel (HS.sel h0 content) (HS.sel h1 content) /\ buffer_compatible b) #(mp h1)
          (fun _ -> assert (rel (as_seq h0 b) (as_seq h1 b)))
    in
    Classical.forall_intro_2 aux

let witness_p #a #rrel #rel b p =
  match b with
  | Null -> ()
  | Buffer _ content _ _ ->
    lemma_stable_on_rel_is_stable_on_rrel b p;
    //AR: TODO: the proof doesn't go through without this assertion, which should follow directly from the lemma call
    assert (HST.stable_on #(Seq.lseq a (U32.v (Buffer?.max_length b))) #(srel_to_lsrel (U32.v (Buffer?.max_length b)) rrel) (spred_as_mempred b p) (Buffer?.content b));
    HST.witness_p content (spred_as_mempred b p)

let recall_p #_ #_ #_ b p =
  match b with
  | Null -> ()
  | Buffer _ content _ _ -> HST.recall_p content (spred_as_mempred b p)

let witnessed_functorial #a #rrel #rel1 #rel2 b1 b2 i len s1 s2 =
  match b1, b2 with
  | Null, Null -> assert (as_seq HS.empty_mem b1 == Seq.empty)
  | Buffer _ content _ _, _ ->
    assert (forall (len:nat) (i:nat) (j:nat{i <= j /\ j <= len}). compatible_sub_preorder len rrel i j rel1);
    HST.token_functoriality content (spred_as_mempred b1 s1) (spred_as_mempred b2 s2)

let witnessed_functorial_st #a #rrel #rel1 #rel2 b1 b2 i len s1 s2 =
  match b1, b2 with
  | Null, Null -> ()
  | Buffer _ content _ _, _ ->
    HST.token_functoriality content (spred_as_mempred b1 s1) (spred_as_mempred b2 s2)

let freeable (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) =
  (not (g_is_null b)) /\
  HS.is_mm (Buffer?.content b) /\
  HS.is_heap_color (HS.color (frameOf b)) /\
  U32.v (Buffer?.max_length b) > 0 /\
  Buffer?.idx b == 0ul /\
  Ghost.reveal (Buffer?.length b) == Buffer?.max_length b

let free #_ #_ #_ b = HST.rfree (Buffer?.content b)

let freeable_length #_ #_ #_ b = ()

let freeable_disjoint #_ #_ #_ #_ #_ #_ b1 b2 =
  if frameOf b1 = frameOf b2 && as_addr b1 = as_addr b2 then
    MG.loc_disjoint_aloc_elim #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf b2) #(as_addr b2) (ubuffer_of_buffer b1) (ubuffer_of_buffer b2)

let freeable_disjoint' (#a1 #a2:Type0) (#rrel1 #rel1:srel a1) (#rrel2 #rel2:srel a2)
  (b1:mbuffer a1 rrel1 rel1) (b2:mbuffer a2 rrel2 rel2)
  :Lemma (requires (freeable b1 /\ length b2 > 0 /\ disjoint b1 b2))
         (ensures (loc_disjoint (loc_addr_of_buffer b1) (loc_addr_of_buffer b2)))
         [SMTPat (freeable b1); SMTPat (disjoint b1 b2)]
  = freeable_disjoint b1 b2

private let alloc_heap_common (#a:Type0) (#rrel:srel a)
  (r:HST.erid) (len:U32.t{U32.v len > 0}) (s:Seq.seq a{Seq.length s == U32.v len})
  (mm:bool)
  :HST.ST (lmbuffer a rrel rrel (U32.v len))
          (requires (fun _      -> True))
          (ensures (fun h0 b h1 -> alloc_post_mem_common b h0 h1 s /\
	                        frameOf b == r /\
                                HS.is_mm (Buffer?.content b) == mm /\
                                Buffer?.idx b == 0ul /\
                                Ghost.reveal (Buffer?.length b) == Buffer?.max_length b))
  = lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
    let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
      if mm then HST.ralloc_mm r s else HST.ralloc r s
    in
    let b = Buffer len content 0ul (Ghost.hide len) in
    b

let mgcmalloc #_ #_ r init len =
  alloc_heap_common r len (Seq.create (U32.v len) init) false

private let read_sub_buffer (#a:Type0) (#rrel #rel:srel a)
  (b:mbuffer a rrel rel) (idx len:U32.t)
  : HST.ST (Seq.seq a)
    (requires fun h0 ->
      live h0 b /\ U32.v len > 0 /\
      U32.v idx + U32.v len <= length b)
    (ensures fun h0 s h1 ->
      h0 == h1 /\
      s == Seq.slice (as_seq h0 b) (U32.v idx) (U32.v idx + U32.v len))
  = let open HST in
    let s = ! (Buffer?.content b) in  //the whole allocation unit
    let s = Seq.slice s (U32.v (Buffer?.idx b))
              (U32.v (Buffer?.max_length b)) in //b buffer
    Seq.slice s (U32.v idx) (U32.v idx + U32.v len)  //slice of b

let mgcmalloc_and_blit #_ #_ r #_ #_ src id_src len =
  alloc_heap_common r len (read_sub_buffer src id_src len) false

let mmalloc #_ #_ r init len =
  alloc_heap_common r len (Seq.create (U32.v len) init) true

let mmalloc_and_blit #_ #_ r #_ #_ src id_src len =
  alloc_heap_common r len (read_sub_buffer src id_src len) true

let malloca #a #rrel init len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc (Seq.create (U32.v len) init)
  in
  Buffer len content 0ul (Ghost.hide len)

let malloca_and_blit #a #rrel #_ #_ src id_src len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc (read_sub_buffer src id_src len)
  in
  Buffer len content 0ul (Ghost.hide len)

let malloca_of_list #a #rrel init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.salloc s
  in
  Buffer len content 0ul (Ghost.hide len)

let mgcmalloc_of_list #a #rrel r init =
  let len = U32.uint_to_t (FStar.List.Tot.length init) in
  let s = Seq.seq_of_list init in
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc r s
  in
  Buffer len content 0ul (Ghost.hide len)

let mmalloc_drgn #a #rrel d init len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content : HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc_drgn d (Seq.create (U32.v len) init)
  in
  Buffer len content 0ul len

let mmalloc_drgn_mm #a #rrel d init len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content : HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc_drgn_mm d (Seq.create (U32.v len) init)
  in
  Buffer len content 0ul len

let mmalloc_drgn_and_blit #a #rrel #_ #_ d src id_src len =
  lemma_seq_sub_compatilibity_is_reflexive (U32.v len) rrel;
  let content: HST.mreference (Seq.lseq a (U32.v len)) (srel_to_lsrel (U32.v len) rrel) =
    HST.ralloc_drgn d (read_sub_buffer src id_src len)
  in
  Buffer len content 0ul len

#push-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 128 --split_queries no"
#restart-solver
let blit #a #rrel1 #rrel2 #rel1 #rel2 src idx_src dst idx_dst len =
  let open HST in
  match src, dst with
  | Buffer _ _ _ _, Buffer _ _ _ _ ->
    if len = 0ul then ()
    else
      let h = get () in
      let Buffer max_length1 content1 idx1 length1 = src in
      let Buffer max_length2 content2 idx2 length2 = dst in
      let s_full1 = !content1 in
      let s_full2 = !content2 in
      let s1 = Seq.slice s_full1 (U32.v idx1) (U32.v max_length1) in
      let s2 = Seq.slice s_full2 (U32.v idx2) (U32.v max_length2) in
      let s_sub_src = Seq.slice s1 (U32.v idx_src) (U32.v idx_src + U32.v len) in
      let s2' = Seq.replace_subseq s2 (U32.v idx_dst) (U32.v idx_dst + U32.v len) s_sub_src in
      let s_full2' = Seq.replace_subseq s_full2 (U32.v idx2) (U32.v max_length2) s2' in

      assert (Seq.equal (Seq.slice s2' (U32.v idx_dst) (U32.v idx_dst + U32.v len)) s_sub_src);
      assert (Seq.equal (Seq.slice s2' 0 (U32.v idx_dst)) (Seq.slice s2 0 (U32.v idx_dst)));
      assert (Seq.equal (Seq.slice s2' (U32.v idx_dst + U32.v len) (length dst))
                        (Seq.slice s2 (U32.v idx_dst + U32.v len) (length dst)));

    // AF: Needed to trigger the preorder relation. A bit verbose because the second sequence
    // has a ghost computation (U32.v (Ghost.reveal length))
    assert (s_full2' `Seq.equal`
            Seq.replace_subseq s_full2
                               (U32.v idx2)
                               (U32.v idx2 + U32.v length2)
                               (Seq.replace_subseq (as_seq h dst)
                                                   (U32.v idx_dst)
                                                   (U32.v idx_dst + U32.v len)
			                           (Seq.slice (as_seq h src)
                                                              (U32.v idx_src)
                                                              (U32.v idx_src + U32.v len)
                                                   )
                               )
            );

      content2 := s_full2';

      let h1 = get () in
      assert (s_full2' `Seq.equal` Seq.replace_subseq s_full2 (U32.v idx2) (U32.v idx2 + U32.v length2) (Seq.slice s2' 0 (U32.v length2)));
      assert (h1 == g_upd_seq dst (Seq.slice s2' 0 (U32.v length2)) h);
      g_upd_seq_as_seq dst (Seq.slice s2' 0 (U32.v length2)) h  //for modifies clause
  | _, _ -> ()
#pop-options

#restart-solver
#push-options "--z3rlimit 256 --max_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3cliopt smt.qi.EAGER_THRESHOLD=4"
let fill' (#t:Type) (#rrel #rel: srel t)
  (b: mbuffer t rrel rel)
  (z:t)
  (len:U32.t)
: HST.Stack unit
  (requires (fun h ->
    live h b /\
    U32.v len <= length b /\
    rel (as_seq h b) (Seq.replace_subseq (as_seq h b) 0 (U32.v len) (Seq.create (U32.v len) z))
  ))
  (ensures  (fun h0 _ h1 ->
    modifies (loc_buffer b) h0 h1 /\
    live h1 b /\
    Seq.slice (as_seq h1 b) 0 (U32.v len) `Seq.equal` Seq.create (U32.v len) z /\
    Seq.slice (as_seq h1 b) (U32.v len) (length b) `Seq.equal` Seq.slice (as_seq h0 b) (U32.v len) (length b)
  ))
= let open HST in
  if len = 0ul then ()
  else begin
    let h = get () in
    let Buffer max_length content idx length = b in
    let s_full = !content in
    let s = Seq.slice s_full (U32.v idx) (U32.v max_length) in
    let s_src = Seq.create (U32.v len) z in
    let s' = Seq.replace_subseq s 0 (U32.v len) s_src in
    let s_full' = Seq.replace_subseq s_full (U32.v idx) (U32.v idx + U32.v len) s_src in
    // AF: Needed to trigger the preorder relation. A bit verbose because the second sequence
    // has a ghost computation (U32.v (Ghost.reveal length))
    assert (s_full' `Seq.equal` Seq.replace_subseq s_full (U32.v idx) (U32.v idx + U32.v length) (Seq.replace_subseq (Seq.slice s_full (U32.v idx) (U32.v idx + U32.v length)) 0 (U32.v len) s_src));
    content := s_full';
    let h' = HST.get () in
    assert (s_full' `Seq.equal` Seq.replace_subseq s_full (U32.v idx) (U32.v idx + U32.v length) (Seq.slice s' 0 (U32.v length)));
    assert (h' == g_upd_seq b (Seq.slice s' 0 (U32.v length)) h);
    g_upd_seq_as_seq b (Seq.slice s' 0 (U32.v length)) h  //for modifies clause
  end
#pop-options

let fill #t #rrel #rel b z len = fill' b z len

let abuffer' = ubuffer'

let coerce (t2: Type) (#t1: Type) (x1: t1) : Pure t2 (requires (t1 == t2)) (ensures (fun y -> y == x1)) = x1

let cloc_cls =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.cls abuffer) cls

let cloc_of_loc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce (MG.loc cloc_cls) l

let loc_of_cloc l =
  assert_norm (MG.cls abuffer == MG.cls ubuffer);
  coerce loc l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let cloc_of_loc_none _ = ()

let cloc_of_loc_union _ _ = ()

let cloc_of_loc_addresses _ _ _ = ()

let cloc_of_loc_regions _ _ = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
