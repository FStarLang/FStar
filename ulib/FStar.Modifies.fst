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
module FStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U32 = FStar.UInt32

noeq
type loc_aux : Type =
  | LocBuffer:
    (#t: Type) ->
    (b: B.buffer t) ->
    loc_aux

let loc_aux_in_addr
  (l: loc_aux)
  (r: HS.rid)
  (n: nat)
: GTot Type0
= match l with
  | LocBuffer b ->
    B.frameOf b == r /\
    B.as_addr b == n

let aloc (r: HS.rid) (n: nat) : Tot (Type u#1) =
  (l: loc_aux { loc_aux_in_addr l r n } )

let loc_aux_includes_buffer
  (#a: Type)
  (s: loc_aux)
  (b: B.buffer a)
: GTot Type0
= match s with
  | LocBuffer #a0 b0 -> a == a0 /\ b0 `B.includes` b

let loc_aux_includes
  (s1 s2: loc_aux)
: GTot Type0
  (decreases s2)
= match s2 with
  | LocBuffer b -> loc_aux_includes_buffer s1 b

let loc_aux_includes_refl
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
= ()

let loc_aux_includes_buffer_includes
  (#a: Type)
  (s: loc_aux)
  (b1 b2: B.buffer a)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `B.includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
= ()

let loc_aux_includes_loc_aux_includes_buffer
  (#a: Type)
  (s1 s2: loc_aux)
  (b: B.buffer a)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
= match s2 with
  | LocBuffer b2 -> loc_aux_includes_buffer_includes s1 b2 b

let loc_aux_includes_trans
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= match s3 with
  | LocBuffer b -> loc_aux_includes_loc_aux_includes_buffer s1 s2 b

(* the following is necessary because `decreases` messes up 2nd-order unification with `Classical.forall_intro_3` *)

let loc_aux_includes_trans'
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  ((loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3) ==> loc_aux_includes s1 s3)
= Classical.move_requires (loc_aux_includes_trans s1 s2) s3

let loc_aux_disjoint_buffer
  (l: loc_aux)
  (#t: Type)
  (p: B.buffer t)
: GTot Type0
= match l with
  | LocBuffer b -> B.disjoint b p

let loc_aux_disjoint
  (l1 l2: loc_aux)
: GTot Type0
= match l2 with
  | LocBuffer b ->
    loc_aux_disjoint_buffer l1 b

let loc_aux_disjoint_sym
  (l1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
= ()

let loc_aux_disjoint_buffer_includes
  (l: loc_aux)
  (#t: Type)
  (p1: B.buffer t)
  (p2: B.buffer t)
: Lemma
  (requires (loc_aux_disjoint_buffer l p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_disjoint_buffer l p2))
= ()

let loc_aux_disjoint_loc_aux_includes_buffer
  (l1 l2: loc_aux)
  (#t3: Type)
  (b3: B.buffer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_buffer l2 b3))
  (ensures (loc_aux_disjoint_buffer l1 b3))
= match l2 with
  | LocBuffer b2 -> loc_aux_disjoint_buffer_includes l1 b2 b3

let loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: loc_aux)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= match l3 with
  | LocBuffer b3 ->
    loc_aux_disjoint_loc_aux_includes_buffer l1 l2 b3

let loc_aux_preserved (l: loc_aux) (h1 h2: HS.mem) : GTot Type0
= match l with
  | LocBuffer b ->
    (
      B.live h1 b
    ) ==> (
      B.live h2 b /\
      B.as_seq h2 b == B.as_seq h1 b
    )

module MG = FStar.ModifiesGen

let cls : MG.cls aloc = MG.Cls #aloc
  (fun #r #a -> loc_aux_includes)
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  (fun #r #a -> loc_aux_disjoint)
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  (fun #r #a -> loc_aux_preserved)
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f ->
    match b with
    | LocBuffer b' ->
      let g () : Lemma
        (requires (B.live h1 b'))
        (ensures (loc_aux_preserved b h1 h2))
      = f _ _ (B.content b')
      in
      Classical.move_requires g ()
  )

let loc = MG.loc cls

let loc_none = MG.loc_none

let loc_union = MG.loc_union

let loc_union_idem = MG.loc_union_idem

let loc_union_comm = MG.loc_union_comm

let loc_union_assoc = MG.loc_union_assoc

let loc_union_loc_none_l = MG.loc_union_loc_none_l

let loc_union_loc_none_r = MG.loc_union_loc_none_r

let loc_buffer #t b =
  MG.loc_of_aloc #_ #cls #(B.frameOf b) #(B.as_addr b) (LocBuffer b)

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

let loc_includes_buffer #t b1 b2 =
  MG.loc_includes_aloc #_ #cls #(B.frameOf b1) #(B.as_addr b1) (LocBuffer b1) (LocBuffer b2)

let loc_includes_gsub_buffer_r l #t b i len =
  loc_includes_trans l (loc_buffer b) (loc_buffer (B.sub b i len))

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 = ()

let loc_includes_addresses_buffer #t preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(B.as_addr p) (LocBuffer p)

let loc_includes_region_buffer #t preserve_liveness s b =
  MG.loc_includes_region_aloc #_ #cls preserve_liveness s #(B.frameOf b) #(B.as_addr b) (LocBuffer b)

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_union_l = MG.loc_includes_region_union_l

let loc_includes_addresses_addresses = MG.loc_includes_addresses_addresses #_ cls

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

let loc_disjoint_includes = MG.loc_disjoint_includes

let loc_disjoint_buffer #t1 #t2 b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(B.frameOf b1) #(B.as_addr b1) #(B.frameOf b2) #(B.as_addr b2) (LocBuffer b1) (LocBuffer b2)

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_addresses = MG.loc_disjoint_addresses #_ #cls

let loc_disjoint_buffer_addresses #t p preserve_liveness r n =
  MG.loc_disjoint_aloc_addresses_intro #_ #cls #(B.frameOf p) #(B.as_addr p) (LocBuffer p) preserve_liveness r n

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #t1 b p h h' =
  MG.modifies_aloc_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (LocBuffer b) p h h'

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _

let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_buffer #t b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(B.frameOf b) #(B.as_addr b) (LocBuffer b)

let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

let region_liveness_insensitive_buffer #t b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(B.frameOf b) #(B.as_addr b) (LocBuffer b)

let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

let modifies_liveness_insensitive_buffer l1 l2 h h' #t x =
  MG.modifies_preserves_liveness_strong l1 l2 h h' (B.content x) (LocBuffer x)

let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

let modifies_liveness_insensitive_region_buffer l1 l2 h h' #t x =
  MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(B.frameOf x) #(B.as_addr x) (LocBuffer x)


let modifies_trans = MG.modifies_trans

let modifies_only_live_regions = MG.modifies_only_live_regions

let no_upd_fresh_region = MG.no_upd_fresh_region

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro

let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

let modifies_free = MG.modifies_free #_ #cls

let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

let modifies_buffer_none_modifies h1 h2 =
  MG.modifies_none_intro #_ #cls h1 h2
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())

let modifies_0_modifies h1 h2 =
  B.lemma_reveal_modifies_0 h1 h2;
  MG.modifies_none_intro #_ #cls h1 h2
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())

let modifies_1_modifies #a b h1 h2 =
  B.lemma_reveal_modifies_1 b h1 h2;
  MG.modifies_intro (loc_buffer b) h1 h2
    (fun _ -> ())
    (fun t' pre' b' ->
      MG.loc_disjoint_sym (loc_mreference b') (loc_buffer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (LocBuffer b) true (HS.frameOf b') (Set.singleton (HS.as_addr b'))
    )
    (fun t' pre' b' -> ())
    (fun r n -> ())
    (fun r' a' b' ->
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b) #(B.as_addr b) b' (LocBuffer b)
    )

let modifies_2_modifies #a1 #a2 b1 b2 h1 h2 =
  B.lemma_reveal_modifies_2 b1 b2 h1 h2;
  MG.modifies_intro (loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2
    (fun _ -> ())
    (fun t' pre' b' ->
      loc_disjoint_includes (loc_mreference b') (loc_union (loc_buffer b1) (loc_buffer b2)) (loc_mreference b') (loc_buffer b1);
      loc_disjoint_sym (loc_mreference b') (loc_buffer b1);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b1) #(B.as_addr b1) (LocBuffer b1) true (HS.frameOf b') (Set.singleton (HS.as_addr b'));
      loc_disjoint_includes (loc_mreference b') (loc_union (loc_buffer b1) (loc_buffer b2)) (loc_mreference b') (loc_buffer b2);
      loc_disjoint_sym (loc_mreference b') (loc_buffer b2);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b2) #(B.as_addr b2) (LocBuffer b2) true (HS.frameOf b') (Set.singleton (HS.as_addr b'))
    )
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r' a' b' ->
      loc_disjoint_includes (MG.loc_of_aloc b') (loc_union (loc_buffer b1) (loc_buffer b2)) (MG.loc_of_aloc b') (loc_buffer b1);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b1) #(B.as_addr b1) b' (LocBuffer b1);
      loc_disjoint_includes (MG.loc_of_aloc b') (loc_union (loc_buffer b1) (loc_buffer b2)) (MG.loc_of_aloc b') (loc_buffer b2);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b2) #(B.as_addr b2) b' (LocBuffer b2)
    )

#set-options "--z3rlimit 20"

let modifies_3_modifies #a1 #a2 #a3 b1 b2 b3 h1 h2 =
  B.lemma_reveal_modifies_3 b1 b2 b3 h1 h2;
  MG.modifies_intro (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) h1 h2
    (fun _ -> ())
    (fun t' pre' b' ->
      loc_disjoint_includes (loc_mreference b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (loc_mreference b') (loc_buffer b1);
      loc_disjoint_sym (loc_mreference b') (loc_buffer b1);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b1) #(B.as_addr b1) (LocBuffer b1) true (HS.frameOf b') (Set.singleton (HS.as_addr b'));
      loc_disjoint_includes (loc_mreference b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (loc_mreference b') (loc_buffer b2);
      loc_disjoint_sym (loc_mreference b') (loc_buffer b2);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b2) #(B.as_addr b2) (LocBuffer b2) true (HS.frameOf b') (Set.singleton (HS.as_addr b'));
      loc_disjoint_includes (loc_mreference b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (loc_mreference b') (loc_buffer b3);
      loc_disjoint_sym (loc_mreference b') (loc_buffer b3);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b3) #(B.as_addr b3) (LocBuffer b3) true (HS.frameOf b') (Set.singleton (HS.as_addr b'))
    )
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r' a' b' ->
      loc_disjoint_includes (MG.loc_of_aloc b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (MG.loc_of_aloc b') (loc_buffer b1);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b1) #(B.as_addr b1) b' (LocBuffer b1);
      loc_disjoint_includes (MG.loc_of_aloc b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (MG.loc_of_aloc b') (loc_buffer b2);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b2) #(B.as_addr b2) b' (LocBuffer b2);
      loc_disjoint_includes (MG.loc_of_aloc b') (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) (MG.loc_of_aloc b') (loc_buffer b3);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b3) #(B.as_addr b3) b' (LocBuffer b3)
    )

#reset-options

let modifies_buffer_rcreate_post_common #a r init len b h0 h1 =
  MG.modifies_none_intro #_ #cls h0 h1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())

let mreference_live_buffer_unused_in_disjoint #t1 #pre #t2 h b1 b2 =
  loc_disjoint_includes (loc_freed_mreference b1) (loc_freed_mreference (B.content b2)) (loc_freed_mreference b1) (loc_buffer b2)

let buffer_live_mreference_unused_in_disjoint #t1 #t2 #pre h b1 b2 =
  loc_disjoint_includes (loc_freed_mreference (B.content b1)) (loc_freed_mreference b2) (loc_buffer b1) (loc_freed_mreference b2)

let does_not_contain_addr = MG.does_not_contain_addr

let not_live_region_does_not_contain_addr = MG.not_live_region_does_not_contain_addr

let unused_in_does_not_contain_addr = MG.unused_in_does_not_contain_addr

let addr_unused_in_does_not_contain_addr = MG.addr_unused_in_does_not_contain_addr

let free_does_not_contain_addr = MG.free_does_not_contain_addr

let does_not_contain_addr_elim = MG.does_not_contain_addr_elim

let modifies_only_live_addresses = MG.modifies_only_live_addresses


(* Type class instance *)

let cloc_aloc = aloc

let cloc_cls = cls

let cloc_of_loc l = l

let loc_of_cloc l = l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let cloc_of_loc_none _ = ()

let cloc_of_loc_union _ _ = ()

let cloc_of_loc_addresses _ _ _ = ()

let cloc_of_loc_regions _ _ = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
