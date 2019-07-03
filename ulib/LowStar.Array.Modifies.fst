module LowStar.Array.Modifies

// Because of the use of reals, this cannot be extracted, hence it needs to be in a separate module


module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.ModifiesGen

open LowStar.Permissions

open FStar.Real

open LowStar.Array.Defs
friend LowStar.Array.Defs

(*** Definitions of locations for arrays with permissions ***)

// We need to define the atomic locations cell per cell. We will then define loc_buffer as the union of aloc of cells
// The reason for this is that we want to prove that the loc of the union of two buffers corresponds to the union of locs
// of the two smaller buffers.
noeq
type ucell_ : Type0 = {
  b_max: nat;
  b_index:nat;
  b_pid:perm_id;
}

val ucell (region:HS.rid) (addr:nat) : Tot Type0
let ucell region addr = ucell_

// let uarray_of_array (#a:Type0) (b:array a) : Tot (uarray (frameOf b) (as_addr b)) =
//   { b_max_length = U32.v b.max_length;
//     b_offset = U32.v b.idx;
//     b_length = U32.v b.length;
//     b_pid = b.pid }

let ucell_preserved (#r:HS.rid) (#a:nat) (b:ucell r a) (h0 h1:HS.mem) : GTot Type0 =
  forall (t:Type0) (b':array t).
    (let i = b.b_index - U32.v b'.idx in // This cell corresponds to index i in the buffer
      (frameOf b' == r /\ as_addr b' == a /\ b'.pid == (Ghost.hide b.b_pid) /\ U32.v b'.max_length == b.b_max /\
        b.b_index >= U32.v b'.idx /\ b.b_index < U32.v b'.idx + U32.v b'.length /\ // If this cell is part of the buffer
        live_cell h0 b' i ==>
          live_cell h1 b' i /\ // If this cell is preserved, then its liveness is preserved
          (sel h0 b' i == sel h1 b' i))) // And its contents (snapshot + permission) are the same

let prove_loc_preserved (#r: HS.rid) (#a: nat) (loc: ucell r a) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i))
    (ensures (
      let i = loc.b_index - U32.v b'.idx in
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
      ))
  )) : Lemma (ucell_preserved #r #a loc h0 h1)
  =
  let aux (t: Type0) (b':array t) : Lemma(
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i ==>
        live_cell h1 b' i /\
        sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i)
    ) : Lemma (
      let i = loc.b_index - U32.v b'.idx in
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
    )
    = lemma t b'
  in
    Classical.impl_intro aux'
  in
  Classical.forall_intro_2 aux


// Two cells are included if they are equal: Same pid and same index in the buffer
let ucell_includes (#r: HS.rid) (#a: nat) (c1 c2: ucell r a) : GTot Type0 =
  c1.b_pid == c2.b_pid /\
  c1.b_index == c2.b_index /\
  c1.b_max == c2.b_max


let ucell_disjoint (#r:HS.rid) (#a:nat) (c1 c2:ucell r a) : GTot Type0 =
  c1.b_max == c2.b_max /\
    (c1.b_index <> c2.b_index \/           // Either the cells are different (i.e. spatially disjoint)
    c1.b_pid <> c2.b_pid)                 // Or they don't have the same permission

let cls : MG.cls ucell = MG.Cls #ucell
  ucell_includes
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  ucell_disjoint
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  ucell_preserved
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f ->
    prove_loc_preserved #r #a b h1 h2 (fun t b' ->
      let ref_t = Seq.lseq (value_with_perms t) (U32.v b'.max_length) in
      f ref_t (Heap.trivial_preorder ref_t) b'.content
    )
  )

let loc = MG.loc cls

let loc_none = MG.loc_none #ucell #cls
let loc_union (l1 l2:loc) = MG.loc_union #ucell #cls l1 l2
let loc_disjoint (l1 l2:loc) = MG.loc_disjoint #ucell #cls l1 l2
let loc_includes (l1 l2:loc) = MG.loc_includes #ucell #cls l1 l2

let aloc_cell (#a:Type) (b:array a) (i:nat{i < vlength b}) : GTot (ucell (frameOf b) (as_addr b)) =
  let r = frameOf b in
  let a = as_addr b in
  {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i;       // The index of the cell is the index inside the bigger array
    b_pid = (Ghost.reveal b.pid);
  }

let loc_cell (#t:Type) (b:array t) (i:nat{i < vlength b}) : GTot loc =
  let r = frameOf b in
  let a = as_addr b in
  MG.loc_of_aloc #ucell #cls #r #a (aloc_cell #t b i)

// The location of an array is the recursive union of all of its cells
let rec compute_loc_array (#a:Type) (b:array a) (i:nat{i <= vlength b})
  : GTot loc
  (decreases (vlength b - i))
  = if i = vlength b then MG.loc_none
    else loc_cell b i `MG.loc_union #ucell #cls` compute_loc_array b (i+1)

let loc_array (#a:Type) (b:array a) : GTot loc =
  compute_loc_array b 0

// The location of a cell of the array is included in the global loc_array
let lemma_includes_loc_cell_loc_array (#a:Type) (b:array a) (i:nat{i < vlength b})
  : Lemma (loc_includes (loc_array b) (loc_cell b i))
  =
  let rec aux (j:nat{j <= i}) : Lemma
    (ensures loc_includes (compute_loc_array b j) (loc_cell b i))
    (decreases (i - j))
    =
    if j = i then begin
      MG.loc_includes_refl #ucell #cls (loc_cell b i);
      MG.loc_includes_union_l #ucell #cls (loc_cell b i) (compute_loc_array b (j+1)) (loc_cell b i)
    end else begin
      aux (j+1);
      MG.loc_includes_union_l #ucell #cls (loc_cell b j) (compute_loc_array b (j+1)) (loc_cell b i)
    end
  in aux 0

let lemma_disjoint_pid_disjoint_cells (#a:Type) (b1 b2:array a) (i1:nat{i1 < vlength b1}) (i2:nat{i2 < vlength b2}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_cell b1 i1) (loc_cell b2 i2))
  =
  let r1 = frameOf b1 in
  let r2 = frameOf b2 in
  let a1 = as_addr b1 in
  let a2 = as_addr b2 in
  let aloc1 = {
    b_max = U32.v b1.max_length;
    b_index = U32.v b1.idx + i1;
    b_pid = (Ghost.reveal b1.pid)
  } in
  let aloc2 = {
    b_max = U32.v b2.max_length;
    b_index = U32.v b2.idx + i2;
    b_pid = (Ghost.reveal b2.pid)
  } in
  MG.loc_disjoint_aloc_intro #ucell #cls #r1 #a1 #r2 #a2 aloc1 aloc2

let rec lemma_disjoint_pid_disjoint_cell_array (#a:Type0) (b1 b2:array a) (i:nat{i < vlength b1}) (j:nat{j <= vlength b2}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (compute_loc_array b2 j) (loc_cell b1 i))
  (decreases (vlength b2 - j))
  = if j = vlength b2 then begin
       MG.loc_disjoint_none_r #ucell #cls (loc_cell b1 i);
       MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end else begin
      lemma_disjoint_pid_disjoint_cell_array b1 b2 i (j+1);
      lemma_disjoint_pid_disjoint_cells b1 b2 i j;
      MG.loc_disjoint_sym (compute_loc_array b2 (j+1)) (loc_cell b1 i);
      MG.loc_disjoint_union_r #ucell #cls (loc_cell b1 i) (loc_cell b2 j) (compute_loc_array b2 (j+1));
      MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end

let rec lemma_disjoint_pid_disjoint_compute_array (#a:Type) (b1 b2:array a) (i:nat{i <= vlength b1}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_array b2)  (compute_loc_array b1 i) )
  (decreases (vlength b1 - i))
  = if i = vlength b1 then MG.loc_disjoint_none_r #ucell #cls (loc_array b2)
    else begin
      lemma_disjoint_pid_disjoint_cell_array b1 b2 i 0;
      lemma_disjoint_pid_disjoint_compute_array b1 b2 (i+1);
      MG.loc_disjoint_union_r #ucell #cls (loc_array b2) (loc_cell b1 i) (compute_loc_array b1 (i+1))
    end

let lemma_disjoint_pid_disjoint_arrays (#a:Type0) (b1 b2:array a) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_array b1) (loc_array b2))
  = lemma_disjoint_pid_disjoint_compute_array b1 b2 0;
    MG.loc_disjoint_sym (loc_array b2) (loc_array b1)

let loc_addresses = MG.loc_addresses #ucell #cls
let loc_regions = MG.loc_regions #ucell #cls

let loc_not_unused_in = MG.loc_not_unused_in _

let loc_unused_in = MG.loc_unused_in _

let modifies (s:loc) (h0 h1:HS.mem) : GTot Type0 = MG.modifies s h0 h1

let lemma_disjoint_loc_from_array_disjoint_from_cells (#t: Type) (b: array t) (p: loc)
  : Lemma (requires (loc_disjoint (loc_array b) p))
    (ensures (forall(i:nat{i < vlength b}). loc_disjoint (loc_cell b i) p))
  =
  let aux (i:nat{i < vlength b}) : Lemma (loc_disjoint (loc_cell b i) p) =
    lemma_includes_loc_cell_loc_array b i;
    MG.loc_includes_refl p;
    MG.loc_disjoint_includes
      (loc_array b) p
      (loc_cell b i) p
  in
  Classical.forall_intro aux

let modifies_array_elim #t b p h h' =
  lemma_disjoint_loc_from_array_disjoint_from_cells #t b p;
  assert(forall(i:nat{i < vlength b}). loc_disjoint (loc_cell b i) p);
  let aux (i:nat{i < vlength b}) : Lemma (ensures (ucell_preserved #(frameOf b) #(as_addr b) (aloc_cell b i) h h')) =
    MG.modifies_aloc_elim #ucell #cls #(frameOf b) #(as_addr b)
      (aloc_cell b i) p h h'
  in
  Classical.forall_intro aux;
  assert(forall(i:nat{i < vlength b}). ucell_preserved #(frameOf b) #(as_addr b) (aloc_cell b i) h h');
  assert(forall(i:nat{i < vlength b}). sel h b i == sel h' b i);
  assert(forall(i:nat{i < vlength b}). (sel h b i).wp_v == Seq.index (as_seq h b) i /\ (sel h' b i).wp_v == Seq.index (as_seq h' b) i);
  assert(forall(i:nat{i < vlength b}).
    (sel h b i).wp_perm == Seq.index (as_perm_seq h b) i /\
    (sel h' b i).wp_perm == Seq.index (as_perm_seq h' b) i
  );
  Seq.lemma_eq_intro (as_seq h b) (as_seq h' b);
  Seq.lemma_eq_intro (as_perm_seq h b) (as_perm_seq h' b);
  assert(as_seq h b  == as_seq h' b);
  assert(as_perm_seq h b  == as_perm_seq h' b);
  assert((forall (i:nat{i < vlength b}). live_cell h' b i /\ HS.contains h' b.content));
  assert(HS.contains h' b.content)

let loc_union_idem s = MG.loc_union_idem s
let loc_union_comm s1 s2 = MG.loc_union_comm s1 s2
let loc_union_assoc = MG.loc_union_assoc #ucell #cls

let loc_union_idem_1 s1 s2 = MG.loc_union_assoc s1 s1 s2; loc_union_idem s1
let loc_union_idem_2 s1 s2 = MG.loc_union_assoc s1 s2 s2

let loc_union_loc_none_l s = MG.loc_union_loc_none_l s
let loc_union_loc_none_r s = MG.loc_union_loc_none_r s
let loc_includes_refl s = MG.loc_includes_refl s
let loc_includes_trans_backwards s1 s2 s3 = MG.loc_includes_trans s1 s2 s3
let loc_includes_union_l s1 s2 s = MG.loc_includes_union_l s1 s2 s

let loc_includes_union_r s s1 s2 =
  Classical.move_requires (MG.loc_includes_union_r s s1) s2;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s1;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s2;
  Classical.move_requires (MG.loc_includes_trans s (loc_union s1 s2)) s1;
  Classical.move_requires (MG.loc_includes_trans s (loc_union s1 s2)) s2;
  MG.loc_includes_refl s1;
  MG.loc_includes_refl s2

let loc_includes_none s = MG.loc_includes_none s

let loc_includes_region_addresses preserve_liveness1 preserve_liveness2 s r a =
  MG.loc_includes_region_addresses #_ #cls preserve_liveness1 preserve_liveness2 s r a

let loc_includes_region_addresses' preserve_liveness r a = ()
let loc_includes_region_region preserve_liveness1 preserve_liveness2 s1 s2 =
  MG.loc_includes_region_region #_ #cls preserve_liveness1 preserve_liveness2 s1 s2
let loc_includes_region_region' preserve_liveness s = ()

let loc_includes_adresses_loc_cell (#a: Type) (b: array a) (preserve_liveness: bool) (i:nat{i < vlength b})
  : Lemma (
    loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
      (loc_cell b i)
  )
= MG.loc_includes_addresses_aloc #ucell #cls preserve_liveness (frameOf b) (Set.singleton (as_addr b))
    #(as_addr b) (aloc_cell b i)

let rec loc_includes_adresses_loc_array_rec (#a: Type) (b: array a) (preserve_liveness: bool) (i:nat{i <= vlength b})
  : Lemma (requires True) (ensures (
    loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
      (compute_loc_array b i)
   )) (decreases (vlength b - i))
= if i = vlength b then
    MG.loc_includes_none (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
  else begin
  loc_includes_adresses_loc_cell b preserve_liveness i;
  loc_includes_adresses_loc_array_rec b preserve_liveness (i+1);
  assert(loc_includes (loc_addresses preserve_liveness (frameOf b) (Set.singleton (as_addr b)))
    ((loc_cell b i) `loc_union` (compute_loc_array b (i + 1)))
  )
  end

let loc_includes_adresses_loc_array #a b preserve_liveness =
  loc_includes_adresses_loc_array_rec b preserve_liveness 0

let loc_includes_region_union_l preserve_liveness l s1 s2 =
  MG.loc_includes_region_union_l preserve_liveness l s1 s2

let loc_includes_addresses_addresses_1 preserve_liveness1 preserve_liveness2 r1 r2 s1 s2 =
  MG.loc_includes_addresses_addresses cls preserve_liveness1 preserve_liveness2 r1 s1 s2

let loc_includes_addresses_addresses_2 preserve_liveness r s = ()

let loc_disjoint_sym' s1 s2 =
  Classical.move_requires (MG.loc_disjoint_sym s1) s2;
  Classical.move_requires (MG.loc_disjoint_sym s2) s1

let loc_disjoint_none_r s = MG.loc_disjoint_none_r s

let loc_disjoint_union_r' s s1 s2 =
  Classical.move_requires (MG.loc_disjoint_union_r s s1) s2;
  loc_includes_union_l s1 s2 s1;
  loc_includes_union_l s1 s2 s2;
  Classical.move_requires (MG.loc_disjoint_includes s (loc_union s1 s2) s) s1;
  Classical.move_requires (MG.loc_disjoint_includes s (loc_union s1 s2) s) s2;
  MG.loc_includes_refl s

let loc_disjoint_includes p1 p2 p1' p2' = MG.loc_disjoint_includes p1 p2 p1' p2'

let loc_disjoint_includes_r b1 b2 b2' = loc_disjoint_includes b1 b2 b1 b2'

let loc_disjoint_addresses preserve_liveness1 preserve_liveness2 r1 r2 n1 n2 =
  MG.loc_disjoint_addresses #_ #cls preserve_liveness1 preserve_liveness2 r1 r2 n1 n2

let loc_disjoint_regions preserve_liveness1 preserve_liveness2 rs1 rs2 =
  MG.loc_disjoint_regions #_ #cls preserve_liveness1 preserve_liveness2 rs1 rs2

let modifies_live_region s h1 h2 r = MG.modifies_live_region s h1 h2 r

let modifies_mreference_elim #t #pre b p h h' = MG.modifies_mreference_elim b p h h'
let modifies_refl s h = MG.modifies_refl s h
let modifies_loc_includes s1 h h' s2 = MG.modifies_loc_includes s1 h h' s2

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _
let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_addresses r a = MG.loc_includes_address_liveness_insensitive_locs_addresses cls r a
let region_liveness_insensitive_addresses preserve_liveness r a =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls preserve_liveness r a
let region_liveness_insensitive_regions rs = MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls rs
let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference l1 l2 h h' #t #pre x = MG.modifies_preserves_liveness l1 l2 h h' x
let modifies_liveness_insensitive_mreference_weak l h h' #t #pre x = modifies_liveness_insensitive_mreference loc_none l h h' x
let modifies_liveness_insensitive_region l1 l2 h h' x = MG.modifies_preserves_region_liveness l1 l2 h h' x
let modifies_liveness_insensitive_region_mreference l1 l2 h h' #t #pre x = MG.modifies_preserves_region_liveness_reference l1 l2 h h' x
let modifies_liveness_insensitive_region_weak l2 h h' x = modifies_liveness_insensitive_region loc_none l2 h h' x
let modifies_liveness_insensitive_region_mreference_weak l2 h h' #t #pre x = modifies_liveness_insensitive_region_mreference loc_none l2 h h' x

let modifies_address_liveness_insensitive_unused_in h h' = MG.modifies_address_liveness_insensitive_unused_in cls h h'

let modifies_trans = MG.modifies_trans

let modifies_trans_linear l l_goal h1 h2 h3 = modifies_trans l h1 h2 l_goal h3

let no_upd_fresh_region r l h0 h1 = MG.no_upd_fresh_region r l h0 h1
let new_region_modifies m0 r0 col = MG.new_region_modifies cls m0 r0 col

let modifies_ralloc_post #a #rel i init h x h' = MG.modifies_ralloc_post #_ #cls i init h x h'
let modifies_free #a #rel r m = MG.modifies_free #_ #cls r m

let modifies_upd #t #pre r v h = MG.modifies_upd #_ #cls r v h

let fresh_frame_loc_not_unused_in_disjoint h0 h1 = MG.not_live_region_loc_not_unused_in_disjoint cls h0 (HS.get_tip h1)

let live_loc_not_unused_in #a b h =
  let set = Set.singleton (as_addr b) in
  Classical.move_requires (MG.does_not_contain_addr_elim b.content h) (frameOf b, as_addr b);
  MG.loc_addresses_not_unused_in cls (frameOf b) set h;
  assert (loc_not_unused_in h `loc_includes` loc_addresses false (frameOf b) set)

let mreference_live_loc_not_unused_in #t #pre h r = MG.mreference_live_loc_not_unused_in cls h r
let mreference_unused_in_loc_unused_in #t #pre h r = MG.mreference_unused_in_loc_unused_in cls h r

let unused_in_not_unused_in_disjoint_2 l1 l2 l1' l2' h =
  MG.loc_includes_trans (loc_unused_in h) l1 l1' ;
  MG.loc_includes_trans (loc_not_unused_in h) l2 l2'  ;
  MG.loc_unused_in_not_unused_in_disjoint cls h ;
  MG.loc_disjoint_includes (loc_unused_in h) (loc_not_unused_in h) l1' l2'

let modifies_loc_unused_in l h1 h2 l' =
  modifies_loc_includes (address_liveness_insensitive_locs) h1 h2 l;
  MG.modifies_address_liveness_insensitive_unused_in cls h1 h2;
  MG.loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'

let ralloc_post_fresh_loc #a #rel i init m0 x m1 = ()
let fresh_frame_modifies h0 h1 = MG.fresh_frame_modifies cls h0 h1
let popped_modifies h0 h1 = MG.popped_modifies cls h0 h1

let modifies_only_not_unused_in = MG.modifies_only_not_unused_in #ucell #cls
let modifies_remove_new_locs l_fresh l_aux l_goal h1 h2 h3 = modifies_only_not_unused_in l_goal h1 h3
let modifies_remove_fresh_frame h1 h2 h3 l =
   MG.loc_regions_unused_in cls h1 (HS.mod_set (Set.singleton (HS.get_tip h2)));
   modifies_only_not_unused_in l h1 h3

let live_same_arrays_equal_types
  (#a1: Type0)
  (#a2: Type0)
  (b1: array a1{U32.v b1.max_length > 0})
  (b2: array a2{U32.v b2.max_length > 0})
  (h: HS.mem)
  : Lemma (requires (
     frameOf b1 == frameOf b2 /\
     as_addr b1 == as_addr b2 /\
     HS.contains h b1.content /\
     HS.contains h b2.content))
   (ensures (a1 == a2 /\ HS.sel h b1.content == HS.sel h b2.content))
  =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  let s1 = HS.sel h b1.content in
  let s2 = HS.sel h b2.content in
  let (_, vp1) = Seq.index s1 0 in
  let (_, vp2) = Seq.index s2 0 in
  Seq.lemma_equal_instances_implies_equal_types ()

let only_one_live_pid_with_full_permission_specific
  (#a: Type0)
  (#v: a)
  (v_perms: value_perms a v)
  (pid: perm_id)
  (pid':live_pid v_perms)
  : Lemma (requires (get_permission_from_pid v_perms pid == 1.0R))
    (ensures pid == pid')
  = only_one_live_pid_with_full_permission v_perms pid

let rec loc_gsub_len_loc_gsub (#a:Type0) (b:array a) (i len1 len2:U32.t) (n:nat{n <= U32.v len1 + U32.v len2})
  :Lemma (requires (U32.v len1 > 0 /\ U32.v len2 > 0 /\ U32.v i + U32.v len1 + U32.v len2 <= vlength b /\ n >= U32.v len1))
         (ensures compute_loc_array (gsub b (i `U32.add` len1) len2) (n - U32.v len1)
                  == compute_loc_array (gsub b i (len1 `U32.add` len2)) n)
         (decreases (U32.v len1 + U32.v len2 - n))
  = if n = U32.v len1 + U32.v len2 then ()
    else begin
      loc_gsub_len_loc_gsub b i len1 len2 (n+1)
    end

let rec loc_union_gsub_compute_loc_array (#a:Type0) (b:array a) (i len1 len2:U32.t) (n:nat{n <= U32.v len1})
  :Lemma (requires (U32.v len1 > 0 /\ U32.v len2 > 0 /\ U32.v i + U32.v len1 + U32.v len2 <= vlength b))
         (ensures loc_union (compute_loc_array (gsub b i len1) n) (loc_array (gsub b (i `U32.add` len1) len2))
                  == compute_loc_array (gsub b i (len1 `U32.add` len2)) n)
         (decreases (U32.v len1 - n))
  =
  let b1 = gsub b i len1 in
  let b2 = gsub b (i `U32.add` len1) len2 in
  let ball = gsub b i (len1 `U32.add` len2) in
  let l1 = loc_union (compute_loc_array (gsub b i len1) n) (compute_loc_array (gsub b (i `U32.add` len1) len2) 0) in
  let l2 = compute_loc_array (gsub b i (len1 `U32.add` len2)) n in
  if n = U32.v len1 then begin
    assert (l1 == loc_union loc_none (loc_array b2));
    loc_gsub_len_loc_gsub b i len1 len2 (U32.v len1)
    end
  else begin
    loc_union_gsub_compute_loc_array b i len1 len2 (n+1);
    loc_union_assoc (loc_cell b1 n) (compute_loc_array b1 (n+1)) (loc_array b2)
  end

let loc_union_gsub #a b i len1 len2 = loc_union_gsub_compute_loc_array b i len1 len2 0

let loc_union_is_split_into #a b b1 b2 = loc_union_gsub #a b 0ul b1.length b2.length

let lemma_disjoint_index_disjoint_cells (#a:Type) (b:array a) (i1:nat{i1 < vlength b}) (i2:nat{i2 < vlength b}) : Lemma
  (requires i1 <> i2)
  (ensures loc_disjoint (loc_cell b i1) (loc_cell b i2))
  =
  let r = frameOf b in
  let a = as_addr b in
  let aloc1 = {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i1;
    b_pid = (Ghost.reveal b.pid)
  } in
  let aloc2 = {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i2;
    b_pid = (Ghost.reveal b.pid)
  } in
  MG.loc_disjoint_aloc_intro #ucell #cls #r #a #r #a aloc1 aloc2

let rec lemma_disjoint_index_disjoint_cell_array (#a:Type0) (b:array a) (idx:U32.t) (len:U32.t{U32.v len > 0})
  (i:nat{i < vlength b}) (j:nat{j <= U32.v len}) : Lemma
  (requires (i < U32.v idx \/ i >= U32.v idx + U32.v len) /\ U32.v idx + U32.v len <= vlength b)
  (ensures loc_disjoint (compute_loc_array (gsub b idx len) j) (loc_cell b i))
  (decreases (U32.v len - j))
  =
  let b2 = gsub b idx len in
  if j = U32.v len then begin
       loc_disjoint_none_r (loc_cell b i);
       loc_disjoint_sym' (loc_cell b i) (compute_loc_array b2 j)
  end else begin
      lemma_disjoint_index_disjoint_cell_array b idx len i (j+1);
      lemma_disjoint_index_disjoint_cells b i (U32.v idx + j);
      loc_disjoint_sym' (compute_loc_array b2 (j+1)) (loc_cell b i);
      loc_disjoint_union_r' (loc_cell b i) (loc_cell b2 j) (compute_loc_array b2 (j+1));
      loc_disjoint_sym' (loc_cell b i) (compute_loc_array b2 j)
    end

let rec lemma_disjoint_gsub_disjoint_compute_array (#a:Type) (b:array a)
  (i1 i2:U32.t) (len1:U32.t{U32.v len1 > 0}) (len2:U32.t{U32.v len2 > 0})
  (i:nat{i <= U32.v len2}) : Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= (vlength b) /\
                    UInt32.v i2 + UInt32.v len2 <= (vlength b) /\
		    (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
                     UInt32.v i2 + UInt32.v len2 <= UInt32.v i1)))
  (ensures loc_disjoint (loc_array (gsub b i1 len1)) (compute_loc_array (gsub b i2 len2) i))
  (decreases (U32.v len2 - i))
  = let b1 = gsub b i1 len1 in
    let b2 = gsub b i2 len2 in
    if i = U32.v len2 then loc_disjoint_none_r (loc_array b1)
    else begin
      lemma_disjoint_gsub_disjoint_compute_array b i1 i2 len1 len2 (i+1);
      lemma_disjoint_index_disjoint_cell_array b i1 len1 (U32.v i2 + i) 0;
      loc_disjoint_union_r' (loc_array b1) (loc_cell b2 i) (compute_loc_array b2 (i+1))
    end

let disjoint_gsubs #a b i1 i2 len1 len2 = lemma_disjoint_gsub_disjoint_compute_array b i1 i2 len1 len2 0
