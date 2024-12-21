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
module FStar.ModifiesGen

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

[@@erasable]
type aloc_t = HS.rid -> nat -> Tot Type

[@@erasable]
noeq
type cls (aloc: aloc_t) : Type = | Cls:
  (aloc_includes: (
    (#r: HS.rid) ->
    (#a: nat) ->
    aloc r a ->
    aloc r a ->
    GTot Type0
  )) ->
  (aloc_includes_refl: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    Lemma
    (aloc_includes x x)
  )) ->
  (aloc_includes_trans: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    (x3: aloc r a) ->
    Lemma
    (requires (aloc_includes x1 x2 /\ aloc_includes x2 x3))
    (ensures (aloc_includes x1 x3))
  )) ->
  (aloc_disjoint: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    GTot Type0
  )) ->
  (aloc_disjoint_sym: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    Lemma
    (aloc_disjoint x1 x2 <==> aloc_disjoint x2 x1)
  )) ->
  (aloc_disjoint_includes: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (larger1: aloc r a) ->
    (larger2: aloc r a) ->
    (smaller1: aloc r a) ->
    (smaller2: aloc r a) ->
    Lemma
    (requires (aloc_disjoint larger1 larger2 /\ larger1 `aloc_includes` smaller1 /\ larger2 `aloc_includes` smaller2))
    (ensures (aloc_disjoint smaller1 smaller2))
  )) ->
  (aloc_preserved: (
    (#r: HS.rid) ->
    (#a: nat) ->
    aloc r a ->
    HS.mem ->
    HS.mem ->
    GTot Type0
  )) ->
  (aloc_preserved_refl: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    (h: HS.mem) ->
    Lemma
    (aloc_preserved x h h)
  )) ->
  (aloc_preserved_trans: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (h3: HS.mem) ->
    Lemma
    (requires (aloc_preserved x h1 h2 /\ aloc_preserved x h2 h3))
    (ensures (aloc_preserved x h1 h3))
  )) ->
  (* if any reference at this address is preserved, then any location at this address is preserved *)
  (same_mreference_aloc_preserved: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (b: aloc r a) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (f: (
      (a' : Type0) ->
      (pre: Preorder.preorder a') ->
      (r': HS.mreference a' pre) ->
      Lemma
      (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
      (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
    )) ->
    Lemma
    (aloc_preserved b h1 h2)
  )) ->
  cls aloc

[@@erasable]
val loc (#aloc: aloc_t u#x) (c: cls aloc) : Tot (Type u#x)

val loc_none (#aloc: aloc_t) (#c: cls aloc): Tot (loc c)

val loc_union
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot (loc c)

(** The following is useful to make Z3 cut matching loops with
modifies_trans and modifies_refl *)
val loc_union_idem
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s s == s)

val loc_union_comm
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)

val loc_union_assoc
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_loc_none_l
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union loc_none s == s)

val loc_union_loc_none_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s loc_none == s)


val loc_of_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#n: nat)
  (b: aloc r n)
: GTot (loc c)

val loc_of_aloc_not_none
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#n: nat)
  (b: aloc r n)
: Lemma (loc_of_aloc #_ #c b == loc_none ==> False)

val loc_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: GTot (loc c)

val loc_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: GTot (loc c)

let loc_mreference
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot (loc c)
= loc_addresses true (HS.frameOf b) (Set.singleton (HS.as_addr b))

let loc_freed_mreference
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot (loc c)
= loc_addresses false (HS.frameOf b) (Set.singleton (HS.as_addr b))

let loc_region_only
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot (loc c)
= loc_regions preserve_liveness (Set.singleton r)

let loc_all_regions_from
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot (loc c)
= loc_regions preserve_liveness (HS.mod_set (Set.singleton r))


(* Inclusion of memory locations *)

[@@erasable]
val loc_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot Type0

val loc_includes_refl
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s s)

val loc_includes_trans
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))

val loc_includes_union_l
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s: loc c)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))

val loc_includes_none
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s loc_none)

val loc_includes_none_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (requires (loc_includes loc_none s))
  (ensures (s == loc_none))


val loc_includes_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#n: nat)
  (b1 b2: aloc r n)
: Lemma
  (requires (c.aloc_includes b1 b2))
  (ensures (loc_includes (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_includes_aloc_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#r1 #r2: HS.rid)
  (#n1 #n2: nat)
  (b1: aloc r1 n1)
  (b2: aloc r2 n2)
: Lemma
  (requires (loc_includes (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))
  (ensures (r1 == r2 /\ n1 == n2 /\ c.aloc_includes b1 b2))

val loc_includes_addresses_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
  (#a: nat)
  (p: aloc r a)
: Lemma
  (requires (Set.mem a s))
  (ensures (loc_includes (loc_addresses preserve_liveness r s) (loc_of_aloc #_ #c p)))

val loc_includes_region_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
  (#r: HS.rid)
  (#a: nat)
  (b: aloc r a)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions preserve_liveness s) (loc_of_aloc #_ #c b)))

val loc_includes_region_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions #_ #c preserve_liveness1 s) (loc_addresses preserve_liveness2 r a)))

val loc_includes_region_region
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_regions #_ #c preserve_liveness1 s1) (loc_regions preserve_liveness2 s2)))

val loc_includes_region_union_l
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness: bool)
  (l: loc c)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2)))

val loc_includes_addresses_addresses
  (#aloc: aloc_t) (c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (r: HS.rid)
  (a1 a2: Set.set nat)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset a2 a1))
  (ensures (loc_includes #_ #c (loc_addresses preserve_liveness1 r a1) (loc_addresses preserve_liveness2 r a2)))


(* Disjointness of two memory locations *)

[@@erasable]
val loc_disjoint
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot Type0

val loc_disjoint_sym
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))

val loc_disjoint_none_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (ensures (loc_disjoint s loc_none))

val loc_disjoint_union_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))

val loc_disjoint_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (p1 p2 p1' p2' : loc c)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_aloc_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (#r1: HS.rid)
  (#a1: nat)
  (#r2: HS.rid)
  (#a2: nat)
  (b1: aloc r1 a1)
  (b2: aloc r2 a2)
: Lemma
  (requires ((r1 == r2 /\ a1 == a2) ==> c.aloc_disjoint b1 b2))
  (ensures (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_disjoint_aloc_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#r1: HS.rid)
  (#a1: nat)
  (#r2: HS.rid)
  (#a2: nat)
  (b1: aloc r1 a1)
  (b2: aloc r2 a2)
: Lemma
  (requires (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))
  (ensures ((r1 == r2 /\ a1 == a2) ==> c.aloc_disjoint b1 b2))

val loc_disjoint_addresses_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses #_ #c preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))

let loc_disjoint_addresses #aloc #c = loc_disjoint_addresses_intro #aloc #c

val loc_disjoint_addresses_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (loc_disjoint (loc_addresses #_ #c preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))
  (ensures (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))

val loc_disjoint_aloc_addresses_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (#r' : HS.rid)
  (#a' : nat)
  (p: aloc r' a')
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r == r' ==> (~ (Set.mem a' n))))
  (ensures (loc_disjoint (loc_of_aloc p) (loc_addresses #_ #c preserve_liveness r n)))

val loc_disjoint_aloc_addresses_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#r' : HS.rid)
  (#a' : nat)
  (p: aloc r' a')
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (loc_disjoint (loc_of_aloc p) (loc_addresses #_ #c preserve_liveness r n)))
  (ensures (r == r' ==> (~ (Set.mem a' n))))

val loc_disjoint_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (preserve_liveness1 preserve_liveness2: bool)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions #_ #c preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2)))


(** Liveness-insensitive memory locations *)

val address_liveness_insensitive_locs (#aloc: aloc_t) (c: cls aloc) : Tot (loc c)

val loc_includes_address_liveness_insensitive_locs_aloc (#aloc: aloc_t) (#c: cls aloc) (#r: HS.rid) (#n: nat) (a: aloc r n) : Lemma
  (loc_includes (address_liveness_insensitive_locs c) (loc_of_aloc a))

val loc_includes_address_liveness_insensitive_locs_addresses (#aloc: aloc_t) (c: cls aloc) (r: HS.rid) (a: Set.set nat) : Lemma
  (loc_includes (address_liveness_insensitive_locs c) (loc_addresses true r a))

val region_liveness_insensitive_locs (#al: aloc_t) (c: cls al) : Tot (loc c)

val loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs (#al: aloc_t) (c: cls al) : Lemma
  (loc_includes (region_liveness_insensitive_locs c) (address_liveness_insensitive_locs c))

val loc_includes_region_liveness_insensitive_locs_loc_regions
  (#al: aloc_t) (c: cls al) (r: Set.set HS.rid)
: Lemma
  (region_liveness_insensitive_locs c `loc_includes` loc_regions #_ #c true r)

val loc_includes_region_liveness_insensitive_locs_loc_addresses
  (#al: aloc_t) (c: cls al) (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat)
: Lemma
  (region_liveness_insensitive_locs c `loc_includes` loc_addresses #_ #c preserve_liveness r a)

val loc_includes_region_liveness_insensitive_locs_loc_of_aloc
  (#al: aloc_t) (c: cls al) (#r: HS.rid) (#a: nat) (x: al r a)
: Lemma
  (region_liveness_insensitive_locs c `loc_includes` loc_of_aloc #_ #c x)


(** The modifies clause proper *)

[@@erasable]
val modifies
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_intro
  (#al: aloc_t) (#c: cls al) (l: loc c) (h h' : HS.mem)
  (regions: (
    (r: HS.rid) ->
    Lemma
    (requires (HS.live_region h r))
    (ensures (HS.live_region h' r))
  ))
  (mrefs: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires ((loc_disjoint (loc_mreference b) l) /\ HS.contains h b))
    (ensures (HS.contains h' b /\ HS.sel h' b == HS.sel h b))
  ))
  (livenesses: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires (HS.contains h b))
    (ensures (HS.contains h' b))
  ))
  (addr_unused_in: (
    (r: HS.rid) ->
    (n: nat) ->
    Lemma
    (requires (
      HS.live_region h r /\
      HS.live_region h' r /\ n `Heap.addr_unused_in` (HS.get_hmap h' `Map.sel` r)
    ))
    (ensures (n `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` r)))
  ))
  (alocs: (
    (r: HS.rid) ->
    (a: nat) ->
    (x: al r a) ->
    Lemma
    (requires (loc_disjoint (loc_of_aloc x) l))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies l h h')

val modifies_none_intro
  (#al: aloc_t) (#c: cls al) (h h' : HS.mem)
  (regions: (
    (r: HS.rid) ->
    Lemma
    (requires (HS.live_region h r))
    (ensures (HS.live_region h' r))
  ))
  (mrefs: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires (HS.contains h b))
    (ensures (HS.contains h' b /\ HS.sel h' b == HS.sel h b))
  ))
  (addr_unused_in: (
    (r: HS.rid) ->
    (n: nat) ->
    Lemma
    (requires (HS.live_region h r /\ HS.live_region h' r /\ n `Heap.addr_unused_in` (HS.get_hmap h' `Map.sel` r)))
    (ensures (n `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` r)))
  ))
: Lemma
  (modifies (loc_none #_ #c) h h')

val modifies_address_intro
  (#al: aloc_t) (#c: cls al) (r: HS.rid) (n: nat) (h h' : HS.mem)
  (regions: (
    (r: HS.rid) ->
    Lemma
    (requires (HS.live_region h r))
    (ensures (HS.live_region h' r))
  ))
  (mrefs: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires ((r <> HS.frameOf b \/ n <> HS.as_addr b) /\ HS.contains h b))
    (ensures (HS.contains h' b /\ HS.sel h' b == HS.sel h b))
  ))
  (addr_unused_in: (
    (r': HS.rid) ->
    (n' : nat) ->
    Lemma
    (requires ((r' <> r \/ n' <> n) /\ HS.live_region h r' /\ HS.live_region h' r' /\ n' `Heap.addr_unused_in` (HS.get_hmap h' `Map.sel` r')))
    (ensures (n' `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` r')))
  ))
: Lemma
  (modifies (loc_addresses #_ #c false r (Set.singleton n)) h h')

val modifies_aloc_intro
  (#al: aloc_t) (#c: cls al) (#r: HS.rid) (#n: nat) (z: al r n) (h h' : HS.mem)
  (regions: (
    (r: HS.rid) ->
    Lemma
    (requires (HS.live_region h r))
    (ensures (HS.live_region h' r))
  ))
  (mrefs: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires ((r <> HS.frameOf b \/ n <> HS.as_addr b) /\ HS.contains h b))
    (ensures (HS.contains h' b /\ HS.sel h' b == HS.sel h b))
  ))
  (livenesses: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires (HS.contains h b))
    (ensures (HS.contains h' b))
  ))
  (addr_unused_in: (
    (r: HS.rid) ->
    (n: nat) ->
    Lemma
    (requires (HS.live_region h r /\ HS.live_region h' r /\ n `Heap.addr_unused_in` (HS.get_hmap h' `Map.sel` r)))
    (ensures (n `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` r)))
  ))
  (alocs: (
    (x: al r n) ->
    Lemma
    (requires (c.aloc_disjoint x z))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies (loc_of_aloc #_ #c z) h h')

val modifies_live_region
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_mreference_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc c)
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

val modifies_aloc_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#a: nat)
  (b: aloc r a)
  (p: loc c)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_of_aloc b) p /\
    modifies p h h'
  ))
  (ensures (
    c.aloc_preserved b h h'
  ))

val modifies_refl
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h: HS.mem)
: Lemma
  (modifies s h h)

val modifies_loc_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (s1: loc c)
  (h h': HS.mem)
  (s2: loc c)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))

val modifies_preserves_liveness
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union s1 s2) h h' /\ loc_disjoint s1 (loc_mreference r) /\ loc_includes (address_liveness_insensitive_locs c) s2 /\ h `HS.contains` r))
  (ensures (h' `HS.contains` r))

val modifies_preserves_liveness_strong
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (x: aloc (HS.frameOf r) (HS.as_addr r))
: Lemma
  (requires (modifies (loc_union s1 s2) h h' /\ loc_disjoint s1 (loc_of_aloc #_ #c #(HS.frameOf r) #(HS.as_addr r) x) /\ loc_includes (address_liveness_insensitive_locs c) s2 /\ h `HS.contains` r))
  (ensures (h' `HS.contains` r))

val modifies_preserves_region_liveness
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (h h' : HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ region_liveness_insensitive_locs c `loc_includes` l2 /\ loc_disjoint (loc_region_only false r) l1 /\ HS.live_region h r))
  (ensures (HS.live_region h' r))

val modifies_preserves_region_liveness_reference
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ region_liveness_insensitive_locs c `loc_includes` l2 /\ loc_disjoint (loc_mreference r) l1 /\ HS.live_region h (HS.frameOf r)))
  (ensures (HS.live_region h' (HS.frameOf r)))

val modifies_preserves_region_liveness_aloc
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (h h' : HS.mem)
  (#r: HS.rid)
  (#n: nat)
  (x: al r n)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ region_liveness_insensitive_locs c `loc_includes` l2 /\ loc_disjoint (loc_of_aloc x) l1 /\ HS.live_region h r))
  (ensures (HS.live_region h' r))

val modifies_trans
  (#aloc: aloc_t) (#c: cls aloc)
  (s12: loc c)
  (h1 h2: HS.mem)
  (s23: loc c)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val modifies_only_live_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (rs: Set.set HS.rid)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions false rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

val no_upd_fresh_region
  (#aloc: aloc_t) (#c: cls aloc)
  (r:HS.rid)
  (l:loc c)
  (h0:HS.mem)
  (h1:HS.mem)
: Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))

val fresh_frame_modifies
  (#aloc: aloc_t) (c: cls aloc)
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies #_ #c loc_none h0 h1))

val new_region_modifies
  (#al: aloc_t)
  (c: cls al)
  (m0: HS.mem)
  (r0: HS.rid)
  (col: option int)
: Lemma
  (requires (HST.is_eternal_region r0 /\ HS.live_region m0 r0 /\ (None? col \/ HS.is_heap_color (Some?.v col))))
  (ensures (
    let (_, m1) = HS.new_eternal_region m0 r0 col in
    modifies (loc_none #_ #c) m0 m1
  ))

val popped_modifies
  (#aloc: aloc_t) (c: cls aloc)
  (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies #_ #c (loc_region_only false (HS.get_tip h0)) h0 h1))

val modifies_fresh_frame_popped
  (#aloc: aloc_t) (#c: cls aloc)
  (h0 h1: HS.mem)
  (s: loc c)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_all_regions_from false (HS.get_tip h1)) s) h1 h2 /\
    HS.get_tip h2 == HS.get_tip h1 /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    HS.get_tip h3 == HS.get_tip h0
  ))

val modifies_loc_regions_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions #_ #c true rs) h1 h2))

val modifies_loc_addresses_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only false r) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses true r a) l) h1 h2))

val modifies_ralloc_post
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel)
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies (loc_none #_ #c) h h'))

val modifies_salloc_post
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HS.is_stack_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.salloc_post init h x h'))
  (ensures (modifies (loc_none #_ #c) h h'))

val modifies_free
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference #_ #c r) m (HS.free r m))

val modifies_none_modifies
  (#aloc: aloc_t) (#c: cls aloc)
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies (loc_none #_ #c) h1 h2))

val modifies_upd
  (#aloc: aloc_t) (#c: cls aloc)
  (#t: Type) (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (v: t)
  (h: HS.mem)
: Lemma
  (requires (HS.contains h r))
  (ensures (modifies #_ #c (loc_mreference r) h (HS.upd h r v)))

val modifies_strengthen
  (#al: aloc_t) (#c: cls al) (l: loc c) (#r0: HS.rid) (#a0: nat) (al0: al r0 a0) (h h' : HS.mem)
  (alocs: (
    (f: ((t: Type) -> (pre: Preorder.preorder t) -> (m: HS.mreference t pre) -> Lemma
      (requires (HS.frameOf m == r0 /\ HS.as_addr m == a0 /\ HS.contains h m))
      (ensures (HS.contains h' m))
    )) ->
    (x: al r0 a0) ->
    Lemma
    (requires (c.aloc_disjoint x al0 /\ loc_disjoint (loc_of_aloc x) l))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (requires (modifies (loc_union l (loc_addresses true r0 (Set.singleton a0))) h h'))
  (ensures (modifies (loc_union l (loc_of_aloc al0)) h h'))

(** BEGIN TODO: move to FStar.Monotonic.HyperStack *)

[@@erasable]
val does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: GTot Type0

val not_live_region_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: Lemma
  (requires (~ (HS.live_region h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val unused_in_does_not_contain_addr
  (h: HS.mem)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (h `does_not_contain_addr` (HS.frameOf r, HS.as_addr r)))

val addr_unused_in_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid & nat)
: Lemma
  (requires (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val does_not_contain_addr_addr_unused_in
  (h: HS.mem)
  (ra: HS.rid & nat)
: Lemma
  (requires (h `does_not_contain_addr` ra))
  (ensures (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` (fst ra))))

val free_does_not_contain_addr
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid & nat)
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

val does_not_contain_addr_elim
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid & nat)
: Lemma
  (requires (
    m `does_not_contain_addr` x /\
    HS.frameOf r == fst x /\
    HS.as_addr r == snd x
  ))
  (ensures (~ (m `HS.contains` r)))

(** END TODO *)

val loc_not_unused_in (#al: aloc_t) (c: cls al) (h: HS.mem) : GTot (loc c)

val loc_unused_in (#al: aloc_t) (c: cls al) (h: HS.mem) : GTot (loc c)

val loc_regions_unused_in (#al: aloc_t) (c: cls al) (h: HS.mem) (rs: Set.set HS.rid) : Lemma
  (requires (forall r . Set.mem r rs ==> (~ (HS.live_region h r))))
  (ensures (loc_unused_in c h `loc_includes` loc_regions false rs))

val loc_addresses_unused_in (#al: aloc_t) (c: cls al) (r: HS.rid) (a: Set.set nat) (h: HS.mem) : Lemma
  (requires (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x)))
  (ensures (loc_unused_in c h `loc_includes` loc_addresses false r a))

val loc_addresses_not_unused_in (#al: aloc_t) (c: cls al) (r: HS.rid) (a: Set.set nat) (h: HS.mem) : Lemma
  (requires (forall x . Set.mem x a ==> ~ (h `does_not_contain_addr` (r, x))))
  (ensures (loc_not_unused_in c h `loc_includes` loc_addresses false r a))

val loc_unused_in_not_unused_in_disjoint (#al: aloc_t) (c: cls al) (h: HS.mem) : Lemma
  (loc_unused_in c h `loc_disjoint` loc_not_unused_in c h)

val not_live_region_loc_not_unused_in_disjoint
  (#al: aloc_t)
  (c: cls al)
  (h0: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (~ (HS.live_region h0 r)))
  (ensures (loc_disjoint (loc_region_only false r) (loc_not_unused_in c h0)))

val modifies_address_liveness_insensitive_unused_in
  (#al: aloc_t)
  (c: cls al)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (address_liveness_insensitive_locs c) h h'))
  (ensures (loc_not_unused_in c h' `loc_includes` loc_not_unused_in c h /\ loc_unused_in c h `loc_includes` loc_unused_in c h'))

val modifies_only_not_unused_in
  (#al: aloc_t)
  (#c: cls al)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_unused_in c h `loc_union` l) h h'))
  (ensures (modifies l h h'))

let modifies_only_live_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses false r a) l) h h' /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
= loc_addresses_unused_in c r a h;
  loc_includes_refl l;
  loc_includes_union_l (loc_unused_in c h) l l;
  loc_includes_union_l (loc_unused_in c h) l (loc_addresses false r a);
  loc_includes_union_r (loc_union (loc_unused_in c h) l) (loc_addresses false r a) l;
  modifies_loc_includes (loc_union (loc_unused_in c h) l) h h' (loc_union (loc_addresses false r a) l);
  modifies_only_not_unused_in l h h'

val mreference_live_loc_not_unused_in
  (#al: aloc_t)
  (c: cls al)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in c h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in c h `loc_includes` loc_mreference r))


val mreference_unused_in_loc_unused_in
  (#al: aloc_t)
  (c: cls al)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in c h `loc_includes` loc_freed_mreference r /\ loc_unused_in c h `loc_includes` loc_mreference r))


(** * Compositionality *)

val aloc_union: (bool -> Tot (aloc_t u#x)) -> Tot (aloc_t u#x)

val cls_union (#a: (bool -> Tot aloc_t)) (c: ((b: bool) -> Tot (cls (a b)))) : Tot (cls (aloc_union a))

val union_loc_of_loc (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b))) (b: bool) (l: loc (c b)) : GTot (loc (cls_union c))

val union_loc_of_loc_none
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
: Lemma
  (union_loc_of_loc c b (loc_none #_ #(c b)) == loc_none #_ #(cls_union c))

val union_loc_of_loc_union
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (l1 l2: loc (c b))
: Lemma
  (union_loc_of_loc c b (loc_union #_ #(c b) l1 l2) == loc_union #_ #(cls_union c) (union_loc_of_loc c b l1) (union_loc_of_loc c b l2))

val union_loc_of_loc_addresses
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (union_loc_of_loc c b (loc_addresses #_ #(c b) preserve_liveness r n) == loc_addresses #_ #(cls_union c) preserve_liveness r n)

val union_loc_of_loc_regions
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (union_loc_of_loc c b (loc_regions #_ #(c b) preserve_liveness r) == loc_regions #_ #(cls_union c) preserve_liveness r)

val union_loc_of_loc_includes
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (s1 s2: loc (c b))
: Lemma
  (union_loc_of_loc c b s1 `loc_includes` union_loc_of_loc c b s2 <==> s1 `loc_includes` s2)

val union_loc_of_loc_disjoint
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (s1 s2: loc (c b))
: Lemma
  (union_loc_of_loc c b s1 `loc_disjoint` union_loc_of_loc c b s2 <==> s1 `loc_disjoint` s2)

val modifies_union_loc_of_loc
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2 <==> modifies #_ #(c b) l h1 h2)

val loc_of_union_loc
  (#al: (bool -> Tot aloc_t))
  (#c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (cls_union c))
: GTot (loc (c b))

val loc_of_union_loc_union_loc_of_loc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: loc (c b))
: Lemma
  (loc_of_union_loc b (union_loc_of_loc c b s) == s)

val loc_of_union_loc_none
  (#al: (bool -> Tot aloc_t))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
: Lemma
  (loc_of_union_loc #_ #c b loc_none == loc_none)

val loc_of_union_loc_union
  (#al: (bool -> Tot aloc_t))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l1 l2: loc (cls_union c))
: Lemma
  (loc_of_union_loc b (l1 `loc_union` l2) == loc_of_union_loc b l1 `loc_union` loc_of_union_loc b l2)

val loc_of_union_loc_addresses
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (loc_of_union_loc #_ #c b (loc_addresses preserve_liveness r n) == loc_addresses preserve_liveness r n)

val loc_of_union_loc_regions
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (loc_of_union_loc #_ #c b (loc_regions preserve_liveness r) == loc_regions preserve_liveness r)


/// Universes

val raise_aloc (al: aloc_t u#x) : Tot (aloc_t u#(max x (y + 1)))

val raise_cls (#al: aloc_t u#x) (c: cls al) : Tot (cls (raise_aloc u#x u#y al))

val raise_loc (#al: aloc_t u#x) (#c: cls al) (l: loc c) : Tot (loc (raise_cls u#x u#y c))

val raise_loc_none (#al: aloc_t u#x) (#c: cls al) : Lemma
  (raise_loc u#x u#y (loc_none #_ #c) == loc_none)

val raise_loc_union (#al: aloc_t u#x) (#c: cls al) (l1 l2: loc c) : Lemma
  (raise_loc u#x u#y (loc_union l1 l2) == loc_union (raise_loc l1) (raise_loc l2))

val raise_loc_addresses (#al: aloc_t u#x) (#c: cls al) (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (raise_loc u#x u#y (loc_addresses #_ #c preserve_liveness r a) == loc_addresses preserve_liveness r a)

val raise_loc_regions (#al: aloc_t u#x) (#c: cls al) (preserve_liveness: bool) (r: Set.set HS.rid) : Lemma
  (raise_loc u#x u#y (loc_regions #_ #c preserve_liveness r) == loc_regions preserve_liveness r)

val raise_loc_includes (#al: aloc_t u#x) (#c: cls al) (l1 l2: loc c) : Lemma
  (loc_includes (raise_loc u#x u#y l1) (raise_loc l2) <==> loc_includes l1 l2)

val raise_loc_disjoint (#al: aloc_t u#x) (#c: cls al) (l1 l2: loc c) : Lemma
  (loc_disjoint (raise_loc u#x u#y l1) (raise_loc l2) <==> loc_disjoint l1 l2)

val modifies_raise_loc (#al: aloc_t u#x) (#c: cls al) (l: loc c) (h1 h2: HS.mem) : Lemma
  (modifies (raise_loc u#x u#y l) h1 h2 <==> modifies l h1 h2)

val lower_loc (#al: aloc_t u#x) (#c: cls al) (l: loc (raise_cls u#x u#y c)) : Tot (loc c)

val lower_loc_raise_loc (#al: aloc_t u#x) (#c: cls al) (l: loc c) : Lemma
  (lower_loc (raise_loc u#x u#y l) == l)

val raise_loc_lower_loc (#al: aloc_t u#x) (#c: cls al) (l: loc (raise_cls u#x u#y c)) : Lemma
  (raise_loc (lower_loc l) == l)

val lower_loc_none (#al: aloc_t u#x) (#c: cls al) : Lemma
  (lower_loc u#x u#y #_ #c loc_none == loc_none)

val lower_loc_union (#al: aloc_t u#x) (#c: cls al) (l1 l2: loc (raise_cls u#x u#y c)) : Lemma
  (lower_loc u#x u#y (loc_union l1 l2) == loc_union (lower_loc l1) (lower_loc l2))

val lower_loc_addresses (#al: aloc_t u#x) (#c: cls al) (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (lower_loc u#x u#y #_ #c (loc_addresses preserve_liveness r a) == loc_addresses preserve_liveness r a)

val lower_loc_regions (#al: aloc_t u#x) (#c: cls al) (preserve_liveness: bool) (r: Set.set HS.rid) : Lemma
  (lower_loc u#x u#y #_ #c (loc_regions preserve_liveness r) == loc_regions preserve_liveness r)
