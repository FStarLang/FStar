module LowStar.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.MG2

open LowStar.Permissions

open FStar.Real

friend LowStar.Array.Defs
friend LowStar.Array.Modifies

open LowStar.Array.Defs
open LowStar.Array.Modifies

(*** Stateful operations implementing the ghost specifications ***)


let index #a b i =
  (**) let open HST in
  (**) let h0 = get() in
  (**) assert (live_cell h0 b (U32.v i));
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v

#push-options "--z3rlimit 10"

let upd #a b i v =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) assert (writeable_cell h0 b (U32.v i));
  let s1 = Seq.upd s
    (U32.v b.idx + U32.v i)
    (v, Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) v))
  in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` Seq.upd (as_seq h0 b) (U32.v i) v);
  (**) assert (as_perm_seq h1 b `Seq.equal` as_perm_seq h0 b);
  (**) let aloc = aloc_cell b (U32.v i) in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   aloc
  (**)   h0 h1
  (**)   (fun aloc' ->
  (**)     ucell_preserved_intro aloc' h0 h1 (fun t' b' ->
  (**)       if frameOf b <> frameOf b' || as_addr b <> as_addr b' then () else begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         if aloc.b_index = aloc'.b_index then begin
  (**)           let s0 = HS.sel h0 b.content in
  (**)           let (v0, vp0) = Seq.index s0 aloc.b_index in
  (**)           if not (is_live_pid (Ghost.reveal vp0) aloc'.b_pid) then begin
  (**)             if aloc'.b_pid = aloc.b_pid then
  (**)               assert(is_live_pid (Ghost.reveal vp0) aloc.b_pid /\ (~ (is_live_pid (Ghost.reveal vp0) aloc.b_pid)))
  (**)             else begin
  (**)               assert(ucell_matches_live_array_cell aloc' t' b' h0);
  (**)               let s0' = HS.sel h0 b'.content in
  (**)               let (_, vp0') = Seq.index s0' aloc'.b_index in
  (**)               if (is_live_pid (Ghost.reveal vp0') aloc'.b_pid) then begin
  (**)                 only_one_live_pid_with_full_permission_specific #a #v0 (Ghost.reveal vp0') aloc.b_pid aloc'.b_pid;
  (**)                 assert(aloc'.b_pid = aloc.b_pid /\ (~ (aloc'.b_pid <> aloc.b_pid)))
  (**)               end else
  (**)                 assert(~ (is_live_pid (Ghost.reveal vp0') aloc'.b_pid) /\ is_live_pid (Ghost.reveal vp0') aloc'.b_pid)
  (**)             end
  (**)           end else
  (**)             only_one_live_pid_with_full_permission_specific #a #v0 (Ghost.reveal vp0) aloc.b_pid aloc'.b_pid
  (**)         end
  (**)         else begin
  (**)           live_same_arrays_equal_types b b' h1
  (**)         end
  (**)       end
  (**)     )
  (**)   );
  (**) assert (modifies (loc_cell b (U32.v i)) h0 h1);
  (**) lemma_includes_loc_cell_loc_array b (U32.v i);
  (**) MG.modifies_loc_includes (loc_array b) h0 h1 (loc_cell b (U32.v i))

#pop-options

let alloc #a init len =
  let perm_map_pid = Ghost.hide (
    let (vp, pid) = new_value_perms init true in
    ((vp <: perms_rec a), Ghost.hide pid)
  ) in
  let v = (init, Ghost.hide (fst (Ghost.reveal perm_map_pid))) in
  let s = Seq.create (U32.v len) v in
  (**) let h0 = HST.get() in
  let content = HST.ralloc_mm HS.root s in
  (**) let h1 = HST.get() in
  let b = Array len content 0ul len (snd (Ghost.reveal perm_map_pid)) in
  (**) assert (Seq.equal (as_seq h1 b) (Seq.create (U32.v len) init));
  (**) assume(loc_unused_in h0 `loc_includes` (loc_array b));
  (**) assume(loc_used_in h1 `loc_includes` (loc_array b));
  b

let free #a b =
  (**) let h0 = HST.get () in
  HST.rfree b.content;
  (**) let h1 = HST.get () in
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) modifies_free #(Seq.lseq (value_with_perms a) (U32.v b.max_length))
  (**)   #(Heap.trivial_preorder (Seq.lseq (value_with_perms a) (U32.v b.max_length)))
  (**)   b.content h0
  (**) ;
  (**) assert(modifies (loc_freed_mreference b.content) h0 h1);
  (**) assume(modifies (loc_array b) h0 h1);
  ()

val share_cell
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i < vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 ->
    live h0 b /\ (
      let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + U32.v i) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
    )
  ))
  (ensures (fun h0 _ h1 ->
    modifies (loc_cell b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    live_cell_pid h1 b (U32.v i) (Ghost.reveal pid) /\ // The cell is still live
    (forall (j:nat{j < vlength b}). // We only touch one cell
      j <> U32.v i ==> Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) ==
        Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\ // Permission is split into two
    get_perm h1 b (U32.v i) == P.half_permission (get_perm h0 b (U32.v i)) /\
    get_perm_pid h1 b (U32.v i) (Ghost.reveal pid) == P.half_permission (get_perm h0 b (U32.v i))
  ))

#push-options "--z3rlimit 10"

let share_cell #a b i pid =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) assert (live_cell h0 b (U32.v i));
  (**) lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid);
  let sb1 = Seq.upd sb0 (U32.v i)
    (v_init, Ghost.hide (share_perms_with_pid #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal pid)))
  in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   #r #n
  (**)   ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = Ghost.reveal b.pid})
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun aloc' ->
  (**)      prove_loc_preserved #r #n aloc' h0 h1 (fun t b'->
  (**)        live_same_arrays_equal_types b b' h0;
  (**)        live_same_arrays_equal_types b b' h1;
  (**)        if aloc'.b_index <> U32.v b.idx + U32.v i then ()
  (**)        else lemma_greater_max_not_live_pid (Ghost.reveal perm_map) (Ghost.reveal pid)
  (**)      )
  (**)     )

#pop-options

val share_cells
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i <= vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 -> live h0 b /\
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> (
      let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
    ))
  ))
  (ensures (fun h0 b' h1 ->
    modifies (compute_loc_array b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    (forall (j:nat{j < vlength b}). j < U32.v i ==> // We haven't modified the beginning
      Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) == Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> // Cells atr still live but permissiosn are halved
      live_cell_pid h1 b j (Ghost.reveal pid) /\
      get_perm h1 b j == P.half_permission (get_perm h0 b j) /\
      get_perm_pid h1 b j (Ghost.reveal pid) == P.half_permission (get_perm h0 b j)
    )
  ))

let rec share_cells #a b i pid =
  (**) let h0 = HST.get() in
  if U32.v i >= vlength b then
    (**) MG.modifies_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
    (**)   (fun _ _ _ -> ())
    (**)   (fun _ _ -> ())
  else begin
    share_cells b (U32.add i 1ul) pid;
    (**) let h1 = HST.get() in
    share_cell b i pid;
    (**) let h2 = HST.get () in
    (**) let s12 = compute_loc_array b (U32.v i + 1) in
    (**) let s23 = loc_cell b (U32.v i) in
    (**) MG.loc_union_comm #ucell #cls s12 s23;
    (**) MG.modifies_trans #ucell #cls s12 h0 h1 s23 h2
  end


val lemma_different_live_pid (#a:Type0) (h:HS.mem) (b:array a{vlength b > 0}) : Lemma
  (requires live h b)
  (ensures Ghost.reveal (get_array_current_max h b) <> Ghost.reveal b.pid)

let lemma_different_live_pid #a h b =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx) in
  assert (live_cell h b 0);
  lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid)


let share #a b =
  (**) let open HST in
  (**) let h0 = get() in
  let new_pid = get_array_current_max h0 b in
  share_cells b 0ul new_pid;
  (**) let h1 = get() in
  let b' = Array b.max_length b.content b.idx b.length new_pid in
  (**) assert (as_seq h1 b' `Seq.equal` as_seq h0 b);
  (**) lemma_different_live_pid h0 b;
  (**) lemma_disjoint_pid_disjoint_arrays b b';
  get_array_current_max_same_with_new_pid #a b h0 new_pid;
  array_not_used_pid_in_loc_unused_in b' h0;
  (**) assert( loc_unused_in h0 `loc_includes` (loc_array b'));
  (**) assert( loc_not_unused_in h1 `loc_includes` (loc_array b'));
  b'

val merge_cell:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i < vlength b} ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live_cell h0 b1 (U32.v i) /\ HS.contains h0 b1.content /\
    P.summable_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ HS.contains h1 b1.content /\
    as_seq h0 b == as_seq h1 b /\
    (sel h1 b (U32.v i)).wp_perm = sum_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm /\
    (sel h1 b (U32.v i)).wp_v == (sel h0 b (U32.v i)).wp_v /\
    (forall (j:nat{j <> U32.v i /\ j < vlength b}). sel h0 b j == sel h1 b j /\ sel h0 b1 j == sel h1 b1 j) /\
    modifies (loc_cell b (U32.v i) `loc_union` loc_cell b1 (U32.v i)) h0 h1
  ))

let merge_cell #a b b1 i =
 let open HST in
  (**) let h0 = HST.get () in
  let s0 = !b.content in
  let (v_init, perm_map) = Seq.index s0 (U32.v b.idx + U32.v i) in
  let s1 = Seq.upd s0 (U32.v b.idx + U32.v i) (v_init, Ghost.hide (
    merge_perms #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal b1.pid)
  )) in
  b.content := s1;
  (**) let h1 = HST.get () in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) let acell = aloc_cell b (U32.v i) in
  (**) let cell = loc_cell b (U32.v i) in
  (**) let acell1 = aloc_cell b1 (U32.v i) in
  (**) let cell1 = loc_cell b1 (U32.v i) in
  (**) let l = cell `loc_union` cell1 in
  (**) MG.modifies_intro #ucell #cls
  (**)   l
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre ref ->
  (**)     MG.loc_includes_refl cell;
  (**)     MG.loc_includes_union_l cell cell1 cell;
  (**)     MG.loc_includes_refl (MG.loc_mreference #ucell #cls #t #pre ref);
  (**)     MG.loc_disjoint_includes
  (**)       (MG.loc_mreference ref)
  (**)       l
  (**)       (MG.loc_mreference ref)
  (**)       cell;
  (**)     MG.loc_disjoint_sym  (MG.loc_mreference ref) cell;
  (**)     MG.loc_disjoint_aloc_addresses_elim #ucell #cls #r #n acell
  (**)       true
  (**)       (HS.frameOf ref)
  (**)       (Set.singleton (HS.as_addr ref))
  (**)   )
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun r' n' loc' ->
  (**)     prove_loc_preserved #r' #n' loc' h0 h1 (fun t' b' ->
  (**)       MG.loc_includes_refl cell;
  (**)       MG.loc_includes_union_l cell cell1 cell;
  (**)       MG.loc_includes_refl (MG.loc_of_aloc #ucell #cls #r' #n' loc');
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc loc')
  (**)         l
  (**)         (MG.loc_of_aloc loc')
  (**)         cell;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc loc') cell;
  (**)       MG.loc_includes_refl cell1;
  (**)       MG.loc_includes_union_l cell cell1 cell1;
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc loc')
  (**)         l
  (**)         (MG.loc_of_aloc loc')
  (**)         cell1;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc loc') cell1;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n loc' acell;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n loc' acell1;
  (**)       let i' = loc'.b_index - U32.v b'.idx in
  (**)       let (_, new_perm_map) = Seq.index (HS.sel h1 b'.content) (U32.v b'.idx + i') in
  (**)       if r' = r && n' = n then begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         live_same_arrays_equal_types b b' h1
  (**)       end else ()
  (**)     )
  (**)  )

let rec double_array_union_intro (#a: Type) (buf buf1: array a) (i:nat{i < vlength buf}) : Lemma
  (requires (mergeable buf buf1))
  (ensures (
      let s02 = compute_loc_array buf i `MG.loc_union` compute_loc_array buf1 i in
      let s12 = compute_loc_array buf (i + 1) `MG.loc_union` (compute_loc_array buf1 (i + 1)) in
      let s01 = loc_cell buf i `MG.loc_union` loc_cell buf1 i in
      s02 == s01 `MG.loc_union` s12
  ))
  (decreases (vlength buf - i))
  =
  assert(mergeable buf buf1) ;
  let lbi = compute_loc_array buf i in
  let lb1i = compute_loc_array buf1 i in
  let b = compute_loc_array buf (i + 1) in
  let d = compute_loc_array buf1 (i + 1) in
  let a = loc_cell buf i in
  let c = loc_cell buf1 i in
  let s02 = (compute_loc_array buf i) `MG.loc_union` (compute_loc_array buf1 i) in
  let s12 = b `MG.loc_union` d in
  let s01 = a `MG.loc_union` c in
  assert(compute_loc_array buf i == a `MG.loc_union` b);
  assert(compute_loc_array buf1 i == c `MG.loc_union` d);
  assert(s02 == s01 `MG.loc_union` s12  <==>
    (a `MG.loc_union` b) `MG.loc_union` (c `MG.loc_union` d) ==
    (a `MG.loc_union` c) `MG.loc_union` (b `MG.loc_union` d)
  );
  calc (==) {
     (a `MG.loc_union` b) `MG.loc_union` (c `MG.loc_union` d);
     (==) { MG.loc_union_assoc (a `MG.loc_union` b) c d }
     ((a `MG.loc_union` b) `MG.loc_union` c) `MG.loc_union` d;
     (==) { MG.loc_union_comm a b }
     ((b `MG.loc_union` a) `MG.loc_union` c) `MG.loc_union` d;
     (==) { MG.loc_union_assoc b a c}
     (b `MG.loc_union` (a `MG.loc_union` c)) `MG.loc_union` d;
     (==) { MG.loc_union_comm (a `MG.loc_union` c) b }
     ((a `MG.loc_union` c) `MG.loc_union` b) `MG.loc_union` d;
     (==) { MG.loc_union_assoc (a `MG.loc_union` c) b d }
     (a `MG.loc_union` c) `MG.loc_union` (b `MG.loc_union` d);
  }

val merge_cells:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i <= vlength b} ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\  HS.contains h0 b1.content /\
    (forall (j:nat{j < vlength b /\ j >= U32.v i}). live_cell h0 b1 j /\ P.summable_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm)
  ))
  (ensures (fun h0 _ h1 ->
    modifies (compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i)) h0 h1 /\
    as_seq h0 b == as_seq h1 b /\
    live h1 b /\ (forall (j:nat{j >= U32.v i /\ j < vlength b}).
      (sel h1 b j).wp_perm = sum_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm /\
      (sel h1 b j).wp_v == (sel h0 b j).wp_v
    ) /\ (forall (j:nat{j < U32.v i /\ j < vlength b}).
      sel h1 b j ==  sel h0 b j
    )
  ))

let rec merge_cells #a b b1 i =
  (**) let h0 = HST.get () in
  if U32.v i >= vlength b then begin
    (**) MG.modifies_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
    (**)   (fun _ _ _ -> ())
    (**)   (fun _ _ -> ());
    (**) MG.loc_union_loc_none_l #ucell #cls (MG.loc_none)
  end else begin
    merge_cell #a b b1 i;
    (**) let h1 = HST.get () in
    (**) assert(forall (j:nat{j >=  U32.v i + 1 /\ j < vlength b}).
    (**)   live_cell h0 b1 j /\ sel h0 b1 j == sel h1 b1 j /\ live_cell h1 b1 j /\
    (**)   P.summable_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm
    (**) );
    merge_cells #a b b1 (U32.add i 1ul);
    (**) let h2 = HST.get () in
    (**) let s02 = compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i) in
    (**) let s12 = compute_loc_array b (U32.v i + 1) `MG.loc_union` (compute_loc_array b1 (U32.v i + 1)) in
    (**) let s01 = loc_cell b (U32.v i) `MG.loc_union` loc_cell b1 (U32.v i) in
    (**) MG.loc_union_comm #ucell #cls s01 s12;
    (**) MG.modifies_trans #ucell #cls s01 h0 h1 s12 h2;
    (**) double_array_union_intro b b1 (U32.v i);
    (**) assert(MG.modifies s02 h0 h2)
    (**)
  end;
  (**) let h2 = HST.get () in
  assert(MG.modifies (compute_loc_array b (U32.v i) `MG.loc_union` compute_loc_array b1 (U32.v i)) h0 h2)

let merge #a b b1 =
  merge_cells #a b b1 0ul;
  (**) let h1 = HST.get () in
  (**) assert(forall (i:nat{i < vlength b}). (sel h1 b i).wp_perm = get_perm h1 b i)

val move_cell
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i < vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 ->
    live_cell h0 b (U32.v i)  /\ (
      let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + U32.v i) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
    )
  ))
  (ensures (fun h0 _ h1 ->
    modifies (loc_cell b (U32.v i)) h0 h1 /\
    HS.contains h0 b.content /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    live_cell_pid h1 b (U32.v i) (Ghost.reveal pid) /\ // The cell is still live
    (forall (j:nat{j < vlength b}). // We only touch one cell
      j <> U32.v i ==> Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) ==
        Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\ // Permission is moved
    get_perm h1 b (U32.v i) == FStar.Real.of_int 0 /\
    get_perm_pid h1 b (U32.v i) (Ghost.reveal pid) == get_perm h0 b (U32.v i)
  ))

#push-options "--z3rlimit 10"

let move_cell #a b i pid =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid);
  let sb1 = Seq.upd sb0 (U32.v i)
    (v_init, Ghost.hide (move_perms_with_pid #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal pid)))
  in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let r = frameOf b in
  (**) let n = as_addr b in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   #r #n
  (**)   ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = Ghost.reveal b.pid})
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun aloc' ->
  (**)      prove_loc_preserved #r #n aloc' h0 h1 (fun t b'->
  (**)        live_same_arrays_equal_types b b' h0;
  (**)        live_same_arrays_equal_types b b' h1;
  (**)        if aloc'.b_index <> U32.v b.idx + U32.v i then ()
  (**)        else lemma_greater_max_not_live_pid (Ghost.reveal perm_map) (Ghost.reveal pid)
  (**)      )
  (**)     )

#pop-options

val move_cells
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i <= vlength b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires (fun h0 ->
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> (
      live_cell h0 b j /\ begin
        let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) in
        Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)
      end
    ))
  ))
  (ensures (fun h0 b' h1 ->
    modifies (compute_loc_array b (U32.v i)) h0 h1 /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    (forall (j:nat{j < vlength b}). j < U32.v i ==> // We haven't modified the beginning
      Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) == Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)
    ) /\
    (forall (j:nat{j < vlength b}). j >= U32.v i ==> // Cells atr still live but permissiosn are halved
      live_cell_pid h1 b j (Ghost.reveal pid) /\
      get_perm h1 b j == FStar.Real.of_int 0 /\
      get_perm_pid h1 b j (Ghost.reveal pid) == get_perm h0 b j
    )
  ))

let rec move_cells #a b i pid =
  (**) let h0 = HST.get() in
  if U32.v i >= vlength b then
    (**) MG.modifies_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
    (**)   (fun _ _ _ -> ())
    (**)   (fun _ _ -> ())
  else begin
    move_cells b (U32.add i 1ul) pid;
    (**) let h1 = HST.get() in
    move_cell b i pid;
    (**) let h2 = HST.get () in
    (**) let s12 = compute_loc_array b (U32.v i + 1) in
    (**) let s23 = loc_cell b (U32.v i) in
    (**) MG.loc_union_comm #ucell #cls s12 s23;
    (**) MG.modifies_trans #ucell #cls s12 h0 h1 s23 h2
  end


let move #a b =
  (**) let open HST in
  (**) let h0 = get() in
  let new_pid = get_array_current_max h0 b in
  move_cells b 0ul new_pid;
  (**) let h1 = get() in
  let b' = Array b.max_length b.content b.idx b.length new_pid in
  (**) assert (as_seq h1 b' `Seq.equal` as_seq h0 b);
  (**) assert (as_perm_seq h1 b' `Seq.equal` as_perm_seq h0 b);
  (**) lemma_different_live_pid h0 b;
  (**) lemma_disjoint_pid_disjoint_arrays b b';
  get_array_current_max_same_with_new_pid #a b h0 new_pid;
  array_not_used_pid_in_loc_unused_in b' h0;
  b'

let split #a b idx =
  (**) let h0 = HST.get () in
  let b1 = msub b 0ul idx in
  let b2 = msub b idx U32.(b.length -^ idx) in
  (**) disjoint_gsubs b 0ul idx idx U32.(b.length -^ idx);
  (b1, b2)



#push-options "--z3rlimit 10"

let glue #a b b1 b2 =
  (**) let h0 = HST.get () in
  (**)let aux (i:nat{i < vlength b}) : Lemma (live_cell h0 b i) =
  (**)  if i < vlength b1 then
  (**)    assert(live_cell h0 b1 i)
  (**)  else
  (**)    assert(live_cell h0 b2 (i - vlength b1))
  (**) in
  (**) Classical.forall_intro aux;
  (**) let h1 = HST.get () in
  (**) assert(as_seq h0 b1 `Seq.equal` Seq.slice (as_seq h0 b) 0 (vlength b1));
  (**) assert(as_seq h0 b2 `Seq.equal` Seq.slice (as_seq h0 b) (vlength b1) (vlength b1 + vlength b2));
  (**) Seq.Properties.lemma_split (as_seq h0 b) (U32.v b2.idx - U32.v b1.idx);
  (**) assert(as_perm_seq h0 b1 `Seq.equal` Seq.slice (as_perm_seq h0 b) 0 (vlength b1));
  (**) assert(as_perm_seq h0 b2 `Seq.equal` Seq.slice (as_perm_seq h0 b) (vlength b1) (vlength b1 + vlength b2));
  (**) Seq.Properties.lemma_split (as_perm_seq h0 b) (U32.v b2.idx - U32.v b1.idx);
  (**) loc_union_gsub #a b 0ul b1.length b2.length

#pop-options
