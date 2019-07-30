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

#push-options "--z3rlimit 15"

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
  (**) array_unused_in_intro b h0 (fun j ->
  (**)  ucell_unused_in_intro_not_allocated (aloc_cell b j) h0 (fun t ref -> ())
  (**) );
  (**) let aux (i:nat{i < vlength b}) : Lemma (requires (ucell_unused_in (aloc_cell b i) h1)) (ensures False) =
  (**)  let cell = aloc_cell b i in
  (**)  ucell_unused_in_elim cell h1 False (Seq.lseq (value_with_perms a) (U32.v len)) content
  (**)    (fun () -> ())
  (**)    (fun a' ref' ->
  (**)      live_same_ref_equal_types b ref' h1
  (**)    )
  (**)    (fun t' b' cell' ->
  (**)      live_same_arrays_equal_types b b' h1;
  (**)      let (_, perm_map) = Seq.index (HS.sel h1 b.content) i in
  (**)      let current_max = P.get_current_max (Ghost.reveal perm_map) in
  (**)      assert(ucell_matches_unused_array_cell cell t' b' h1);
  (**)      assert(ucell_matches_used_array_cell cell a b h1)
  (**)    )
  (**) in
  (**) Classical.forall_intro (Classical.move_requires aux);
  (**) array_used_in_intro b h1;
  (**) MG.modifies_loc_none_intro #ucell #cls h0 h1 (fun cell -> ());
  b

#pop-options

let free #a b =
  (**) let h0 = HST.get () in
  (**) // We don't delete the Heap map entry to keep all the adresses used!
  //HST.rfree b.content;
  (**) let h1 = HST.get () in
  (**) MG.modifies_intro #ucell #cls (loc_array b) h0 h1 (fun cell ->
  (**)   ucell_preserved_intro cell h0 h1 (fun t' b' ->
  (**)     let is_inside_b = ucell_matches_array_cell cell a b h0 in
  (**)     Classical.excluded_middle (is_inside_b);
  (**)     let i' = cell.b_index - U32.v b'.idx in
  (**)     let i = cell.b_index - U32.v b.idx in
  (**)     let goal = fun _ -> ucell_matches_live_array_cell cell t' b' h1 /\ sel h0 b' i' == sel h1 b' i' in
  (**)     Classical.or_elim #(is_inside_b) #(~ is_inside_b) #goal
  (**)       (fun _ ->
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         assert(cell.b_max = U32.v b.max_length);
  (**)         assert(cell == aloc_cell b (cell.b_index - U32.v b.idx));
  (**)         lemma_includes_loc_cell_loc_array #a b (cell.b_index - U32.v b.idx);
  (**)         loc_disjoint_includes (loc_array b) (MG.loc_of_aloc cell) (MG.loc_of_aloc cell) (MG.loc_of_aloc cell);
  (**)         MG.loc_disjoint_aloc_elim #ucell #cls cell cell
  (**)       )
  (**)       (fun _ ->
  (**)         (* Here we basically prove that b is the only live array that is standing at the freed location *)
  (**)         if frameOf b <> cell.b_rid || as_addr b <> cell.b_addr then (* Different memory locations *)
  (**)           ()
  (**)         else if U32.v b.max_length <> cell.b_max then (* Two arrays allocated at same memory locations *)
  (**)           live_same_arrays_equal_types b b' h0
  (**)         else if cell.b_index < U32.v b.idx || cell.b_index > U32.v b.idx + U32.v b.length then (* Cell outside of array *)
  (**)           ()
  (**)         else begin (* Different pids *)
  (**)           live_same_arrays_equal_types b b' h0;
  (**)           assert(writeable_cell h0 b i);
  (**)           let (v, perm_map') = Seq.index (HS.sel h0 b'.content) cell.b_index in
  (**)           assert(live_cell h0 b' i');
  (**)           let aux (pid': live_pid (Ghost.reveal perm_map')) : Lemma ((Ghost.reveal b.pid) == pid') =
  (**)             only_one_live_pid_with_full_permission #a #v (Ghost.reveal perm_map') (Ghost.reveal b.pid)
  (**)           in
  (**)           aux (Ghost.reveal b'.pid);
  (**)           assert(Ghost.reveal b.pid == Ghost.reveal b'.pid /\ Ghost.reveal b.pid <> Ghost.reveal b'.pid)
  (**)         end
  (**)       )
  (**)   )
  (**)   (fun t' b' cell' ->
  (**)      assert(ucell_matches_used_array_cell cell' t' b' h0);
  (**)      assert(ucell_matches_used_array_cell cell' t' b' h1);
  (**)      ucell_used_in_intro cell h1 t' b' cell'
  (**)   )
  (**) )


let index #a b i =
  (**) let open HST in
  (**) let h0 = get() in
  (**) assert (live_cell h0 b (U32.v i));
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v

#push-options "--z3rlimit 15"

let upd #a b i v =
  (**) let open HST in
  (**) let h0 = get() in
  let s = ! b.content in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  (**) assert (writeable_cell h0 b (U32.v i));
  let new_perm_map = Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) v) in
  let s1 = Seq.upd s
    (U32.v b.idx + U32.v i)
    (v, new_perm_map)
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
  (**)         (* Here we prove that a disjoint location at the same memory address cannot be live in the first place *)
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
  (**)     (fun t' b' cell' ->
  (**)       if frameOf b <> frameOf b' || as_addr b <> as_addr b' then () else begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         live_same_arrays_equal_types b b' h1;
  (**)         assert(get_current_max (Ghost.reveal new_perm_map) = get_current_max (Ghost.reveal perm_map));
  (**)         let (_, perm_map) = Seq.index s (cell'.b_index) in
  (**)         assert(aloc'.b_pid <= get_current_max (Ghost.reveal perm_map));
  (**)         ucell_used_in_intro aloc' h1 t' b' cell'
  (**)       end
  (**)     )
  (**)   );
  (**) assert (modifies (loc_cell b (U32.v i)) h0 h1);
  (**) lemma_includes_loc_cell_loc_array b (U32.v i);
  (**) MG.modifies_loc_includes (loc_array b) h0 h1 (loc_cell b (U32.v i))

#pop-options

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

#push-options "--z3rlimit 50"

let share_cell #a b i pid =
  (**) let open HST in
  (**) let h0 = get() in
  let s0 = ! b.content in
  let (v_init, perm_map) = Seq.index s0 (U32.v b.idx + U32.v i) in
  (**) assert (live_cell h0 b (U32.v i));
  (**) lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid);
  let perm_map' = Ghost.hide (share_perms_with_pid #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal pid)) in
  let s1 = Seq.upd s0 (U32.v b.idx + U32.v i)
    (v_init, perm_map')
  in
  b.content := s1;
  (**) let h1 = get() in
  (**) assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  (**) let cell = aloc_cell b (U32.v i) in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   cell
  (**)   h0 h1
  (**)   (fun aloc' ->
  (**)      ucell_preserved_intro aloc' h0 h1 (fun t' b'->
  (**)        let i' = aloc'.b_index - U32.v b'.idx in
  (**)        ucell_disjoint_elim aloc' cell (ucell_matches_live_array_cell aloc' t' b' h1 /\ sel h0 b' i' == sel h1 b' i')
  (**)          (fun _ -> ())
  (**)          (fun _ -> ())
  (**)          (fun _ -> live_same_arrays_equal_types b b' h0)
  (**)          (fun _ -> (* Different indexes *)
  (**)            live_same_arrays_equal_types b b' h0; live_same_arrays_equal_types b b' h1
  (**)          )
  (**)          (fun _ -> (* Different PIDs *)
  (**)            live_same_arrays_equal_types b b' h0; live_same_arrays_equal_types b b' h1
  (**)          )
  (**)      )
  (**)      (fun t' b' cell' ->
  (**)        if frameOf b <> frameOf b' || as_addr b <> as_addr b' then () else begin
  (**)          live_same_arrays_equal_types b b' h0;
  (**)          live_same_arrays_equal_types b b' h1;
  (**)          let (_, perm_map) = Seq.index s0 (cell'.b_index) in
  (**)          assert(aloc'.b_pid <= get_current_max (Ghost.reveal perm_map));
  (**)          ucell_used_in_intro aloc' h1 t' b' cell'
  (**)        end
  (**)      )
  (**)   )

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
    (**) MG.modifies_loc_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
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

#set-options "--z3rlimit 20"

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
  (**) get_array_current_max_same_with_new_pid #a b h0 new_pid;
  (**) array_unused_in_intro b' h0 (fun j ->
  (**)   ucell_unused_in_intro_unused_cell (aloc_cell b' j) h0 a b'
  (**) );
  (**) let aux (i:nat{i < vlength b'}) : Lemma (requires (ucell_unused_in (aloc_cell b' i) h1)) (ensures False) =
  (**)  let cell = aloc_cell b' i in
  (**)  ucell_unused_in_elim cell h1 False (Seq.lseq (value_with_perms a) (U32.v b'.max_length)) b'.content
  (**)    (fun () -> ())
  (**)    (fun a' ref' -> ())
  (**)    (fun t'' b'' cell'' ->
  (**)       live_same_arrays_equal_types b' b'' h1;
  (**)       let (_, perm_map) = Seq.index (HS.sel h1 b'.content) cell.b_index in
  (**)       lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b'.pid)
  (**)    )
  (**) in
  (**) Classical.forall_intro (Classical.move_requires aux);
  (**) array_used_in_intro b' h1 ;
  b'

let gatherable_trans (#a: Type0) (b1 b2 b3: array a): Lemma
  (requires (gatherable b1 b2 /\ gatherable b2 b3 /\ loc_disjoint (loc_array b1) (loc_array b3)))
  (ensures (gatherable b1 b3)) =
  (* prove with ucell_disjoint_elim *)
  assert(loc_cell b1 0 `loc_disjoint` loc_array b3);
  lemma_includes_loc_cell_loc_array b1 0;
  lemma_includes_loc_cell_loc_array b3 0;
  MG.loc_disjoint_includes (loc_array b1) (loc_array b3) (loc_cell b1 0) (loc_cell b3 0);
  MG.loc_disjoint_aloc_elim  #ucell #cls (aloc_cell b1 0) (aloc_cell b3 0)

val gather_cell:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i < vlength b} ->
  Stack unit (requires (fun h0 ->
    gatherable b b1 /\
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

let gather_cell #a b b1 i =
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
  (**) let acell = aloc_cell b (U32.v i) in
  (**) let cell = loc_cell b (U32.v i) in
  (**) let acell1 = aloc_cell b1 (U32.v i) in
  (**) let cell1 = loc_cell b1 (U32.v i) in
  (**) let l = cell `loc_union` cell1 in
  (**) MG.modifies_intro #ucell #cls
  (**)   l
  (**)   h0 h1
  (**)   (fun loc' ->
  (**)     ucell_preserved_intro loc' h0 h1 (fun t' b' ->
  (**)       MG.loc_includes_refl cell;
  (**)       MG.loc_includes_union_l cell cell1 cell;
  (**)       MG.loc_includes_refl (MG.loc_of_aloc #ucell #cls loc');
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
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls loc' acell;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls loc' acell1;
  (**)       let (_, new_perm_map) = Seq.index (HS.sel h1 b'.content) loc'.b_index in
  (**)       if loc'.b_rid = acell.b_rid && loc'.b_addr = acell.b_addr then begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         live_same_arrays_equal_types b b' h1;
  (**)         lemma_live_pid_smaller_max (Ghost.reveal new_perm_map) loc'.b_pid
  (**)       end else ()
  (**)     )
  (**)     (fun t' b' cell' ->
  (**)        if frameOf b <> frameOf b' || as_addr b <> as_addr b' then () else begin
  (**)          live_same_arrays_equal_types b b' h0;
  (**)          live_same_arrays_equal_types b b' h1;
  (**)          let (_, perm_map) = Seq.index s0 (cell'.b_index) in
  (**)          assert(loc'.b_pid <= get_current_max (Ghost.reveal perm_map));
  (**)          ucell_used_in_intro loc' h1 t' b' cell'
  (**)        end
  (**)      )
  (**)  )

let rec double_array_union_intro (#a: Type) (buf buf1: array a) (i:nat{i < vlength buf}) : Lemma
  (requires (gatherable buf buf1))
  (ensures (
      let s02 = compute_loc_array buf i `MG.loc_union` compute_loc_array buf1 i in
      let s12 = compute_loc_array buf (i + 1) `MG.loc_union` (compute_loc_array buf1 (i + 1)) in
      let s01 = loc_cell buf i `MG.loc_union` loc_cell buf1 i in
      s02 == s01 `MG.loc_union` s12
  ))
  (decreases (vlength buf - i))
  =
  assert(gatherable buf buf1) ;
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

val gather_cells:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i <= vlength b} ->
  Stack unit (requires (fun h0 ->
    gatherable b b1 /\
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

let rec gather_cells #a b b1 i =
  (**) let h0 = HST.get () in
  if U32.v i >= vlength b then begin
    (**) MG.modifies_loc_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ());
    (**) MG.loc_union_loc_none_l #ucell #cls (MG.loc_none)
  end else begin
    gather_cell #a b b1 i;
    (**) let h1 = HST.get () in
    (**) assert(forall (j:nat{j >=  U32.v i + 1 /\ j < vlength b}).
    (**)   live_cell h0 b1 j /\ sel h0 b1 j == sel h1 b1 j /\ live_cell h1 b1 j /\
    (**)   P.summable_permissions (sel h0 b j).wp_perm (sel h0 b1 j).wp_perm
    (**) );
    gather_cells #a b b1 (U32.add i 1ul);
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

let gather #a b b1 =
  gather_cells #a b b1 0ul;
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
  (**) let cell = aloc_cell b (U32.v i) in
  (**) MG.modifies_aloc_intro
  (**)   #ucell #cls
  (**)   cell
  (**)   h0 h1
  (**)   (fun aloc' ->
  (**)     ucell_preserved_intro aloc' h0 h1 (fun t' b' ->
  (**)       let i' = aloc'.b_index - U32.v b'.idx in
  (**)       let goal = ucell_matches_live_array_cell aloc' t' b' h1 /\ sel h0 b' i'  == sel h1 b' i' in
  (**)       ucell_disjoint_elim cell aloc' goal
  (**)         (fun _ -> ())
  (**)         (fun _ -> ())
  (**)         (fun _ -> (* different max length *)
  (**)           live_same_arrays_equal_types b b' h0;
  (**)           live_same_arrays_equal_types b b' h1
  (**)         )
  (**)         (fun _ -> (* Different indexes *)
  (**)           live_same_arrays_equal_types b b' h0;
  (**)           live_same_arrays_equal_types b b' h1
  (**)         )
  (**)         (fun _ -> (* Different pids *)
  (**)           live_same_arrays_equal_types b b' h0;
  (**)           live_same_arrays_equal_types b b' h1;
  (**)           lemma_greater_max_not_live_pid (Ghost.reveal perm_map) (Ghost.reveal pid)
  (**)         )
  (**)     )
  (**)     (fun t' b' cell' ->
  (**)       if frameOf b <> frameOf b' || as_addr b <> as_addr b' then () else begin
  (**)        live_same_arrays_equal_types b b' h0;
  (**)        live_same_arrays_equal_types b b' h1;
  (**)        let (_, perm_map) = Seq.index s (cell'.b_index) in
  (**)        assert(aloc'.b_pid <= get_current_max (Ghost.reveal perm_map));
  (**)        ucell_used_in_intro aloc' h1 t' b' cell'
  (**)      end
  (**)     )
  (**)   )

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
    (**) MG.modifies_loc_none_intro #ucell #cls h0 h0
    (**)   (fun _ -> ())
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
  (**) array_unused_in_intro b' h0 (fun j ->
  (**)   ucell_unused_in_intro_unused_cell (aloc_cell b' j) h0 a b'
  (**) );
  (**) let aux (i:nat{i < vlength b'}) : Lemma (requires (ucell_unused_in (aloc_cell b' i) h1)) (ensures False) =
  (**)  let cell = aloc_cell b' i in
  (**)  ucell_unused_in_elim cell h1 False (Seq.lseq (value_with_perms a) (U32.v b'.max_length)) b'.content
  (**)    (fun () -> ())
  (**)    (fun a' ref' -> ())
  (**)    (fun t'' b'' cell'' ->
  (**)       live_same_arrays_equal_types b' b'' h1;
  (**)       let (_, perm_map) = Seq.index (HS.sel h1 b'.content) cell.b_index in
  (**)       lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b'.pid)
  (**)    )
  (**) in
  (**) Classical.forall_intro (Classical.move_requires aux);
  (**) array_used_in_intro b' h1;
  b'

let sub #a b i len =
 Array b.max_length b.content (U32.add b.idx i) len b.pid

let split #a b idx =
  (**) let h0 = HST.get () in
  let b1 = sub b 0ul idx in
  let b2 = sub b idx U32.(b.length -^ idx) in
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
