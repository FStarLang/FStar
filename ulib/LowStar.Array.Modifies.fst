module LowStar.Array.Modifies

// Because of the use of reals, this cannot be extracted, hence it needs to be in a separate module


module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.MG2

open LowStar.Permissions

open FStar.Real

open LowStar.Array.Defs
friend LowStar.Array.Defs

(*** Definitions of locations for arrays with permissions ***)

type array_len = n:nat{n > 0 /\ n <= UInt.max_int 32}
type index_len = n:nat{n <= UInt.max_int 32}

/// We need to define the atomic locations cell per cell. We will then define loc_buffer as the union of aloc of cells
/// The reason for this is that we want to prove that the loc of the union of two buffers corresponds to the union of locs
/// of the two smaller buffers.
noeq
type ucell : Type0 = {
  b_rid: HS.rid;
  b_addr: nat;
  b_max: array_len;
  b_index:index_len;
  b_pid:perm_id;
}

let ucell_matches_array_cell (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
  frameOf b = cell.b_rid /\ as_addr b = cell.b_addr /\ cell.b_pid = Ghost.reveal b.pid /\ // The pids match
  HS.contains h b.content /\
  cell.b_index >= U32.v b.idx /\ cell.b_index < U32.v b.idx + U32.v b.length // If this cell is part of the buffer

let ucell_matches_used_array_cell (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
  ucell_matches_array_cell cell t b h /\ begin
    let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
    cell.b_pid <= get_current_max (Ghost.reveal perm_map)
  end

let ucell_matches_unused_array_cell (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
  ucell_matches_array_cell cell t b h /\ begin
    let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
    cell.b_pid > get_current_max (Ghost.reveal perm_map)
  end

let ucell_matches_live_array_cell (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
  ucell_matches_used_array_cell cell t b h /\ cell.b_max = U32.v b.max_length /\ begin
    let i = cell.b_index - U32.v b.idx in
    live_cell h b i
  end

let ucell_preserved (cell:ucell) (h0 h1:HS.mem) : GTot Type0 =
  forall (t:Type0) (b:array t). begin let i = cell.b_index - U32.v b.idx in // This cell corresponds to index i in the buffer
    ucell_matches_live_array_cell cell t b h0 ==>
      (ucell_matches_live_array_cell cell t b h1 /\  // If this cell is preserved, then its liveness is preserved
      sel h0 b i == sel h1 b i) // And its contents (snapshot + permission) are the same
  end

let ucell_preserved_intro (loc: ucell) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = loc.b_index - U32.v b'.idx in
      ucell_matches_live_array_cell loc t b' h0))
    (ensures (
      let i = loc.b_index - U32.v b'.idx in
      ucell_matches_live_array_cell loc t b' h1 /\
      sel h0 b' i  == sel h1 b' i
      ))
  )) : Lemma (ucell_preserved loc h0 h1)
  =
  let aux (t: Type0) (b':array t) : Lemma(
      let i = loc.b_index - U32.v b'.idx in
      ucell_matches_live_array_cell loc t b' h0 ==>
      ucell_matches_live_array_cell loc t b' h1 /\
      sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = loc.b_index - U32.v b'.idx in
      ucell_matches_live_array_cell loc t b' h0)
    ) : Lemma (
      let i = loc.b_index - U32.v b'.idx in
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      ucell_matches_live_array_cell loc t b' h1 /\
      sel h0 b' i  == sel h1 b' i
    )
    = lemma t b'
  in
    Classical.impl_intro aux'
  in
  Classical.forall_intro_2 aux


// Two cells are included if they are equal: Same pid and same index in the buffer
let ucell_includes (c1 c2: ucell) : GTot Type0 =
  c1.b_rid = c2.b_rid /\
  c1.b_addr = c2.b_addr /\
  c1.b_pid = c2.b_pid /\
  c1.b_index = c2.b_index /\
  c1.b_max = c2.b_max

let ucell_disjoint (c1 c2:ucell) : GTot Type0 =
  (c1.b_rid <> c2.b_rid) \/
  (c1.b_addr <> c2.b_addr) \/
  (c1.b_pid <> c2.b_pid) \/  // They don't have the same permission id
  (c1.b_index <> c2.b_index)      // Cells are different (i.e. spatially disjoint)

let ucell_disjoint_elim (c1 c2: ucell) (goal: Type)
  (not_same_region: unit -> Lemma (requires (c1.b_rid <> c2.b_rid)) (ensures goal))
  (not_same_address: unit -> Lemma (requires (c1.b_rid = c2.b_rid /\ c1.b_addr <> c2.b_addr)) (ensures goal))
  (not_same_pid: unit -> Lemma
    (requires (c1.b_rid = c2.b_rid /\ c1.b_addr = c2.b_addr /\ c1.b_pid <> c2.b_pid))
    (ensures goal)
  )
  (not_same_index: unit -> Lemma
    (requires (c1.b_rid = c2.b_rid /\ c1.b_addr = c2.b_addr /\ c1.b_index <> c2.b_index))
    (ensures goal)
  )
  : Lemma (requires (c1 `ucell_disjoint` c2)) (ensures goal)
  =
  if c1.b_rid <> c2.b_rid then not_same_region ()
  else if c1.b_addr <> c2.b_addr then not_same_address ()
  else if c1.b_pid <> c2.b_pid then not_same_pid ()
  else if c1.b_index <> c2.b_index then not_same_index ()


let ucell_unused_in (cell:ucell) (h: HS.mem) =
  // Either there is nothing allocated at that memory cell
  (forall (t:Type) (ref: HST.reference t).
    (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) ==> (~ (HS.contains h ref))
  ) \/
  // Or there is something allocated but it is not an array of length susceptible to contain the cell
  (exists (a: Type) (ref: HST.reference a).
    HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref /\
      (forall (t: Type) (len:array_len).len > cell.b_index ==>  a =!= Seq.lseq (value_with_perms t) len)
  ) \/
  // Or there is an allocated array matching the cell or another cell with a different
  //max_length but it's unused
  (exists (t:Type) (b:array t) (cell': ucell).
    cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
    ucell_matches_unused_array_cell cell' t b h
  )

let ucell_unused_in_intro_not_allocated (cell: ucell) (h: HS.mem)
  (not_allocated: (t: Type) -> (ref: HST.reference t) -> Lemma (
    (HS.as_addr ref =  cell.b_addr /\ HS.frameOf ref = cell.b_rid) ==> (~ (HS.contains h ref))
  )) : Lemma (ucell_unused_in cell h)
  =
  Classical.forall_intro_2 not_allocated

let ucell_unused_in_intro_unused_cell (cell: ucell) (h: HS.mem) (t: Type) (b: array t) : Lemma
  (requires (ucell_matches_unused_array_cell cell t b h))
  (ensures (ucell_unused_in cell h))
  =
  ()


let ucell_unused_in_intro_not_matching (cell: ucell) (h: HS.mem) (t: Type) (b: array t) : Lemma
  (requires (ucell_matches_unused_array_cell cell t b h))
  (ensures (ucell_unused_in cell h))
  =
  ()

let ucell_unused_in_intro_allocated_but_not_array
  (cell: ucell)
  (h: HS.mem)
  (a: Type)
  (ref: HST.reference a)
  (not_matching_array: (t: Type) -> (len: array_len)  -> Lemma
    (requires (len > cell.b_index))
    (ensures (a =!= Seq.lseq (value_with_perms t) len))
  )
  : Lemma
    (requires (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref))
    (ensures (ucell_unused_in cell h))
  =
  let aux (t: Type) (len: array_len) : Lemma
    (len > cell.b_index ==> a =!= Seq.lseq (value_with_perms t) len)
    =
      let aux' (_ :squash (len > cell.b_index)) : Lemma
      (a =!= Seq.lseq (value_with_perms t) len)
      =
      not_matching_array t len
      in
      Classical.impl_intro aux'
  in
  Classical.forall_intro_2 aux

#push-options "--z3rlimit 15"

let ucell_unused_in_elim (cell: ucell) (h: HS.mem) (goal: Type0)
  (t: Type)
  (ref: HST.reference t)
  (not_allocated: (unit -> Lemma
    (requires (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid ==> (~ (HS.contains h ref))))
    (ensures (goal))
  ))
  (allocated_but_no_matching_array: (a: Type) -> (ref: HST.reference a) -> Lemma
    (requires (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref /\
       (forall (t: Type) (len: array_len). len > cell.b_index ==> a =!= Seq.lseq (value_with_perms t) len)
    ))
    (ensures goal)
  )
  (matching_cell_not_used: (t: Type) -> (b: array t) -> (cell': ucell) -> Lemma
    (requires (
      cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
      ucell_matches_unused_array_cell cell' t b h
    ))
    (ensures (goal))
  )
  : Lemma (requires (ucell_unused_in cell h)) (ensures (goal))
  =
  let l = forall (t:Type) (ref: HST.reference t).
    (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) ==> (~ (HS.contains h ref))
  in
  let m = exists (a: Type) (ref: HST.reference a).
    HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref /\
    (forall (t: Type) (len: array_len).
      len > cell.b_index ==> a =!= Seq.lseq (value_with_perms t) len
    )
  in
  let r = exists (t:Type) (b:array t) (cell': ucell).
    cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
    ucell_matches_unused_array_cell cell' t b h
  in
  let goal' = fun (_ : squash ((l \/ m) \/ r)) -> goal in
  Classical.or_elim #(l \/ m) #r #goal'
    (fun (_ : squash (l \/ m)) ->
      Classical.or_elim #l #m #goal'
        (fun (_: squash l) -> not_allocated ())
        (fun (pf_m : squash m) ->
          let p (a: Type) = exists (ref: HST.reference a).
            HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref /\
            (forall (t: Type) (len: array_len{len > cell.b_index}).
               a =!= Seq.lseq (value_with_perms t) len
            )
          in
          let pf : squash (exists (a: Type) . p a) = pf_m in
          Classical.exists_elim goal #Type #p pf (fun a ->
            let p (ref: HST.reference a) =
              HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid /\ HS.contains h ref /\
              (forall (t: Type) (len: array_len).
                len > cell.b_index ==> a =!= Seq.lseq (value_with_perms t) len
              )
            in
            let pf : squash (exists (ref: HST.reference a) . p ref) = pf_m in
            Classical.exists_elim goal #(HST.reference a) #p pf (fun ref ->
	      allocated_but_no_matching_array a ref
            )
          )
        )
    )
    (fun (pf_term : squash r) ->
      let p (t': Type) = exists (b': array t') (cell': ucell).
        cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
        ucell_matches_unused_array_cell cell' t' b' h
      in
      let pf : squash (exists (t': Type) . p t') = pf_term in
      Classical.exists_elim goal #Type #p pf (fun t' ->
        let p (b': array t') = exists (cell': ucell).
          cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
          ucell_matches_unused_array_cell cell' t' b' h
        in
        let pf : squash (exists (b': array t') . p b') = () in
        Classical.exists_elim goal #(array t') #p pf (fun b' ->
          let p (cell': ucell) =
            cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
            ucell_matches_unused_array_cell cell' t' b' h
          in
          let pf : squash (exists (cell': ucell) . p cell') = () in
          Classical.exists_elim goal #ucell #p pf (fun cell' ->
            matching_cell_not_used t' b' cell'
          )
        )
      )
    )

#pop-options

let ucell_used_in (cell: ucell) (h: HS.mem) : Type =
  ~ (ucell_unused_in cell h)

let cast_ref (a: Type) (b: Type) (x: HST.reference a)
  : Pure (HST.reference b) (requires (a == b)) (ensures (fun _ -> True))
  = x

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
   (ensures (a1 == a2 /\ HS.sel h b1.content == HS.sel h b2.content /\ b1.max_length = b2.max_length))
  =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  let s1 = HS.sel h b1.content in
  let s2 = HS.sel h b2.content in
  let (_, vp1) = Seq.index s1 0 in
  let (_, vp2) = Seq.index s2 0 in
  Seq.lemma_equal_instances_implies_equal_types ()


let live_same_ref_equal_types
  (#a: Type0)
  (#t: Type0)
  (b: array t)
  (ref: HST.reference a)
  (h: HS.mem)
  : Lemma (requires (
     frameOf b == HS.frameOf ref /\
     as_addr b == HS.as_addr ref /\
     HS.contains h b.content /\
     HS.contains h ref))
   (ensures (a == Seq.lseq (value_with_perms t) (U32.v b.max_length)))
  =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  let v_b : Seq.lseq (value_with_perms t) (U32.v b.max_length) = HS.sel h b.content in
  let v_ref: a = HS.sel h ref in
  assert(v_b == v_ref)

#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 1"

let ucell_not_unused_in_elim
  (cell: ucell)
  (h: HS.mem)
  (goal: Type)
  (lemma: (t: Type) -> (b: array t) -> (cell': ucell) -> Lemma
    (requires (
      cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
      ucell_matches_used_array_cell cell' t b h
    ))
    (ensures (goal))
  )
  : Lemma
  (requires (ucell_used_in cell h))
  (ensures (goal))
  =
  assert(
    (exists (t:Type) (ref: HST.reference t).
      (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) /\ (HS.contains h ref)
    ) /\
    (forall (a: Type) (ref: HST.reference a).
      HS.as_addr ref <> cell.b_addr \/ HS.frameOf ref <> cell.b_rid \/ (~ (HS.contains h ref)) \/
      (exists (t: Type) (len: array_len).
        len > cell.b_index /\ a == Seq.lseq (value_with_perms t) len
      )
    ) /\
    (forall (t:Type) (b:array t) (cell': ucell).
      cell.b_rid <> cell'.b_rid \/ cell.b_addr <> cell'.b_addr \/ cell.b_pid <> cell'.b_pid \/ cell.b_index <> cell'.b_index \/
      (~ (ucell_matches_unused_array_cell cell' t b h))
    )
  );
  let p (a: Type) = exists (ref: HST.reference a).
    (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) /\ (HS.contains h ref)
  in
  let pf : squash (exists (a: Type). p a) = () in
  Classical.exists_elim goal #Type #p pf (fun a ->
    let p (ref: HST.reference a)=
      (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) /\ (HS.contains h ref)
    in
    let pf : squash (exists (ref: HST.reference a). p ref) = () in
    Classical.exists_elim goal #(HST.reference a) #p pf (fun ref ->
      assert(exists (t: Type) (len: array_len).
        len > cell.b_index /\ a == Seq.lseq (value_with_perms t) len
      );
      let p (t: Type) = exists (len: array_len).
        len > cell.b_index /\ a == Seq.lseq (value_with_perms t) len
      in
      let pf : squash (exists (t: Type). p t) = () in
      Classical.exists_elim goal #Type #p pf (fun t ->
        let p  (len: array_len) =
          len > cell.b_index /\ a == Seq.lseq (value_with_perms t) len
        in
        let pf : squash (exists (len: array_len). p len) = () in
        Classical.exists_elim goal #array_len #p pf (fun len ->
          let ref : HST.reference
            (Seq.lseq (value_with_perms t) len)
          =
            cast_ref a (Seq.lseq (value_with_perms t) len) (ref <: (HST.reference a))
          in
          let b = Array (U32.uint_to_t len) ref 0ul (U32.uint_to_t len) (Ghost.hide cell.b_pid) in
          assert(HS.contains h b.content);
          let cell' = { cell with b_max = len } in
          assert(ucell_matches_array_cell cell' t b h);
          assert(~ (ucell_matches_unused_array_cell cell' t b h));
          assert(ucell_matches_used_array_cell cell' t b h);
          lemma t b cell'
        )
      )
    )
  )

let ucell_used_in_intro (cell: ucell) (h: HS.mem) (t: Type) (b: array t) (cell': ucell) : Lemma
  (requires (
    cell.b_rid = cell'.b_rid /\ cell.b_addr = cell'.b_addr /\ cell.b_pid = cell'.b_pid /\ cell.b_index = cell'.b_index /\
    ucell_matches_used_array_cell cell' t b h
  ))
  (ensures (ucell_used_in cell h))
  =
  let t' = Seq.lseq (value_with_perms t) (U32.v b.max_length) in
  let ref' = b.content in
  assert(
    (HS.as_addr ref' = cell.b_addr /\ HS.frameOf ref' = cell.b_rid) /\ (HS.contains h ref')
  );
  assert(forall (a: Type) (ref: HST.reference a).
    HS.as_addr ref <> cell.b_addr \/ HS.frameOf ref <> cell.b_rid \/ (~ (HS.contains h ref)) \/
    (exists (t: Type) (len: array_len).
      len > cell.b_index /\ a == Seq.lseq (value_with_perms t) len
    )
  );
  let aux (t':Type) (b':array t') (cell'': ucell) : Lemma (
     cell.b_rid <> cell''.b_rid \/ cell.b_addr <> cell''.b_addr \/ cell.b_pid <> cell''.b_pid \/ cell.b_index <> cell''.b_index \/
    (~ (ucell_matches_unused_array_cell cell'' t' b' h))
  ) =
    if cell.b_rid <> cell''.b_rid then () else
    if cell.b_addr <> cell''.b_addr then () else
    if cell.b_pid <> cell''.b_pid then () else
    if cell.b_index <> cell''.b_index then () else begin
      Classical.excluded_middle (ucell_matches_unused_array_cell cell'' t' b' h);
      Classical.or_elim
        #(ucell_matches_unused_array_cell cell'' t' b' h)
        #(~ (ucell_matches_unused_array_cell cell'' t' b' h))
        #(fun _ -> ~ (ucell_matches_unused_array_cell cell'' t' b' h))
        (fun _ ->
          live_same_arrays_equal_types b b' h;
          assert(HS.sel h b.content == HS.sel h b'.content);
          assert(cell''.b_index = cell'.b_index);
          let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
          assert(
            cell.b_pid > get_current_max (Ghost.reveal perm_map) /\
            cell.b_pid <= get_current_max (Ghost.reveal perm_map)
          )
        )
        (fun _ -> ())
    end
  in
  Classical.forall_intro_3 aux;
  assert(forall (t:Type) (b:array t) (cell': ucell).
    cell.b_rid <> cell'.b_rid \/ cell.b_addr <> cell'.b_addr \/ cell.b_pid <> cell'.b_pid \/ cell.b_index <> cell'.b_index \/
    (~ (ucell_matches_unused_array_cell cell' t b h))
  )


let cls : MG.cls ucell = MG.Cls #ucell
  ucell_includes
  (fun  x -> ())
  (fun  x1 x2 x3 -> ())
  ucell_disjoint
  (fun x1 x2 -> ())
  (fun x1 xl -> ())
  (fun larger1 larger2 smaller1 smaller2 -> ())
  ucell_preserved
  (fun x h -> ())
  (fun x h1 h2 h3 -> ())
  ucell_unused_in
  (fun greater lesser h -> ())
  (fun x2 x1 h ->
    (* used_in and unused_in disjoint *)
    let aux (_ : squash ((~ (x1 `ucell_unused_in` h)) /\ x2 `ucell_unused_in` h)) : Lemma (x1 `ucell_disjoint` x2) =
      ucell_not_unused_in_elim x1 h (x1 `ucell_disjoint` x2) (fun t b x1' ->
        ucell_unused_in_elim x2 h (x1 `ucell_disjoint` x2) (Seq.lseq (value_with_perms t) (U32.v b.max_length)) b.content
          (fun () ->
            if (x1.b_rid <> x2.b_rid || x1.b_addr <> x2.b_addr) then () else
              assert((HS.contains h b.content) /\ ~ (HS.contains h b.content))
          )
          (fun a ref ->
            if (x1.b_rid <> x2.b_rid || x1.b_addr <> x2.b_addr) then () else begin
              live_same_ref_equal_types #a #t b ref h
            end
          )
          (fun t' b' x2' ->
            if (x1.b_rid <> x2.b_rid || x1.b_addr <> x2.b_addr) then () else begin
              live_same_arrays_equal_types b' b h;
              if x1'.b_index <> x2'.b_index then () else begin
                let (_, perm_map1) = Seq.index (HS.sel h b.content) x1'.b_index in
                let (_, perm_map2) = Seq.index (HS.sel h b'.content) x2'.b_index in
                if x1'.b_pid <> x2'.b_pid then () else begin
                  assert(perm_map1 == perm_map2);
                  assert(
                    x1'.b_pid <= get_current_max (Ghost.reveal perm_map1) /\
                    x1'.b_pid > get_current_max (Ghost.reveal perm_map1)
                  )
                end
              end
            end
         )
      )
      in Classical.impl_intro aux
  )
  (fun x h0 h1 ->
    (* unused means preserved *)
    ucell_preserved_intro x h0 h1 (fun t b ->
      let i = x.b_index - U32.v b.idx in
      ucell_unused_in_elim x h0 (ucell_preserved x h0 h1) (Seq.lseq (value_with_perms t) (U32.v b.max_length)) b.content
        (fun () ->  assert((HS.contains h1 b.content) /\ (~ (HS.contains h1 b.content))))
        (fun a ref ->
          assert(
            a =!= Seq.lseq (value_with_perms t) (U32.v b.max_length) /\
            a == Seq.lseq (value_with_perms t) (U32.v b.max_length)
          )
        )
        (fun t' b' x' ->
          let i' = x'.b_index - U32.v b'.idx in
          live_same_arrays_equal_types b' b h0;
          let (_, perm_map) = Seq.index (HS.sel h0 b.content) x'.b_index in
          LowStar.Permissions.lemma_greater_max_not_live_pid (Ghost.reveal perm_map) x'.b_pid;
          assert((live_cell h0 b i) /\ (~ (live_cell h0 b' i')))
        )
      )
  )

#pop-options

let loc = MG.loc cls

let loc_none = MG.loc_none #ucell #cls
let loc_union (l1 l2:loc) = MG.loc_union #ucell #cls l1 l2
let loc_disjoint (l1 l2:loc) = MG.loc_disjoint #ucell #cls l1 l2
let loc_includes (l1 l2:loc) = MG.loc_includes #ucell #cls l1 l2

let aloc_cell (#a:Type) (b:array a) (i:nat{i < vlength b}) : GTot ucell =
  {
    b_rid = frameOf b;
    b_addr =  as_addr b;
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i;       // The index of the cell is the index inside the bigger array
    b_pid = (Ghost.reveal b.pid);
  }

let loc_cell (#t:Type) (b:array t) (i:nat{i < vlength b}) : GTot loc =
  MG.loc_of_aloc (aloc_cell #t b i)

// The location of an array is the recursive union of all of its cells
let rec compute_loc_array (#a:Type) (b:array a) (i:nat{i <= vlength b})
  : GTot loc
  (decreases (vlength b - i))
  = if i = vlength b then loc_none
    else loc_cell b i `loc_union` compute_loc_array b (i+1)

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
  let aloc1 = {
    b_rid = frameOf b1;
    b_addr = as_addr b1;
    b_max = U32.v b1.max_length;
    b_index = U32.v b1.idx + i1;
    b_pid = (Ghost.reveal b1.pid)
  } in
  let aloc2 = {
    b_rid = frameOf b2;
    b_addr = as_addr b2;
    b_max = U32.v b2.max_length;
    b_index = U32.v b2.idx + i2;
    b_pid = (Ghost.reveal b2.pid)
  } in
  MG.loc_disjoint_aloc_intro #ucell #cls aloc1 aloc2

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

let loc_unused_in = MG.loc_unused_in #ucell cls
let loc_used_in = MG.loc_used_in #ucell cls

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

#set-options "--z3rlimit 10"

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

let loc_disjoint_sym' s1 s2 = MG.loc_disjoint_sym s1 s2

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

let modifies_array_elim #t b p h h' =
  lemma_disjoint_loc_from_array_disjoint_from_cells #t b p;
  assert(forall(i:nat{i < vlength b}). loc_disjoint (loc_cell b i) p);
  let aux (i:nat{i < vlength b}) : Lemma (ensures (ucell_preserved (aloc_cell b i) h h')) =
    MG.modifies_aloc_elim #ucell #cls
      (aloc_cell b i) p h h'
  in
  Classical.forall_intro aux;
  assert(forall(i:nat{i < vlength b}). ucell_preserved (aloc_cell b i) h h');
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
  assert(live_cell h' b 0 /\ HS.contains h' b.content)


let modifies_refl s h = MG.modifies_refl s h

let modifies_loc_includes s1 h h' s2 = MG.modifies_loc_includes s1 h h' s2

let modifies_trans = MG.modifies_trans

let modifies_trans_linear l l_goal h1 h2 h3 = modifies_trans l h1 h2 l_goal h3

let unused_in_used_in_disjoint_2 l1 l2 l1' l2' h =
  MG.loc_includes_trans (loc_unused_in h) l1 l1' ;
  MG.loc_includes_trans (loc_used_in h) l2 l2'  ;
  MG.loc_unused_in_used_in_disjoint cls h ;
  MG.loc_disjoint_includes (loc_unused_in h) (loc_used_in h) l1' l2'


let modifies_only_used_in l h h' =
  MG.modifies_only_used_in #ucell #cls l h h'

let modifies_remove_new_locs l_fresh l_aux l_goal h1 h2 h3 = modifies_only_used_in l_goal h1 h3

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

let modifies_loc_disjoint (l0 l1:loc) (h0 h1 h2:HS.mem)
  : Lemma (requires (modifies l0 h0 h1 /\
                     modifies l1 h1 h2 /\
                     (forall l .
                       loc_disjoint l l0 /\
                       loc_includes (loc_used_in h0) l
                       ==>
                       loc_disjoint l l1)))
          (ensures  (modifies l0 h0 h2))
   =
   MG.modifies_trans l0 h0 h1 l1 h2;
   assert(modifies (loc_union l0 l1) h0 h2);
   MG.framing_loc_still_unused_in l0 l1 h0 (fun l -> ());
   MG.modifies_loc_includes (loc_unused_in h0 `loc_union` l0) h0 h2 (loc_union l0 l1);
   MG.modifies_only_used_in l0 h0 h2

let loc_disjoint_used_in_modifies (h0 h1:HS.mem) (l l':loc)
  : Lemma (requires (loc_disjoint l' l /\
                     loc_includes (loc_used_in h0) l' /\
                     modifies l h0 h1))
          (ensures  (loc_includes (loc_used_in h1) l'))
  = MG.loc_used_in_preserved h0 h1 l l'

let rec live_array_used_in' (#t: Type) (b: array t) (h: HS.mem) (i:nat{i <= vlength b}) : Lemma
  (requires (live h b))
  (ensures (loc_used_in h `loc_includes` (compute_loc_array b i)))
  (decreases (vlength b - i))
  =
  if i = vlength b then MG.loc_includes_none (loc_used_in h) else begin
    let cell = aloc_cell b i in
    let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
    assert(live_cell h b i);
    P.lemma_live_pid_smaller_max (Ghost.reveal perm_map) cell.b_pid;
    ucell_used_in_intro cell h t b cell;
    assert(ucell_used_in cell h);
    MG2.aloc_used_in_intro cls cell h;
    live_array_used_in' b h (i+1)
  end

let live_array_used_in (#t: Type) (b: array t) (h: HS.mem) : Lemma
  (requires (live h b))
  (ensures (loc_used_in h `loc_includes` (loc_array b)))
  = live_array_used_in' b h 0

let loc_union_gsub #a b i len1 len2 = loc_union_gsub_compute_loc_array b i len1 len2 0

let loc_union_is_split_into #a b b1 b2 = loc_union_gsub #a b 0ul b1.length b2.length

let lemma_disjoint_index_disjoint_cells (#a:Type) (b:array a) (i1:nat{i1 < vlength b}) (i2:nat{i2 < vlength b}) : Lemma
  (requires i1 <> i2)
  (ensures loc_disjoint (loc_cell b i1) (loc_cell b i2))
  =
  let aloc1 = {
    b_rid = frameOf b;
    b_addr = as_addr b;
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i1;
    b_pid = (Ghost.reveal b.pid)
  } in
  let aloc2 = {
    b_rid = frameOf b;
    b_addr = as_addr b;
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i2;
    b_pid = (Ghost.reveal b.pid)
  } in
  MG.loc_disjoint_aloc_intro #ucell #cls aloc1 aloc2

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

val get_array_current_max' (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t{U32.v i <= vlength b}) : Pure (Ghost.erased perm_id)
  (requires True)
  (ensures fun pid -> forall (j:nat{j < vlength b}). j >= U32.v i ==>
    (let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)))
  (decreases (vlength b - U32.v i))

let rec get_array_current_max' #a h b i =
  if U32.v i = vlength b then (Ghost.hide 1)
  else  begin
    let max_end = get_array_current_max' h b (U32.add i 1ul) in
    let (v, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + U32.v i) in
    let current_max = Ghost.hide (get_current_max (Ghost.reveal perm_map) + 1) in
    Ghost.elift2 (fun (a b:perm_id) -> if a > b then a else b) max_end current_max
  end

val get_array_current_max (#a:Type0) (h:HS.mem) (b:array a) : Pure (Ghost.erased perm_id)
  (requires True)
  (ensures fun pid -> forall (j:nat{j < vlength b}).
    (let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)))

let get_array_current_max #a h b = get_array_current_max' #a h b 0ul

let rec get_array_current_max_same_with_new_pid'
  (#a: Type)
  (b: array a)
  (h: HS.mem)
  (new_pid: Ghost.erased perm_id)
  (i:U32.t{U32.v i <= vlength b})
  : Lemma (requires (True)) (ensures (
    let b' = Array b.max_length b.content b.idx b.length new_pid in
    Ghost.reveal (get_array_current_max' #a h b' i) =  Ghost.reveal (get_array_current_max' #a h b i)
  )) (decreases (vlength b - U32.v i))  =
  if U32.v i = vlength b then ()
  else
    get_array_current_max_same_with_new_pid' #a b h new_pid (U32.add i 1ul)

let get_array_current_max_same_with_new_pid (#a: Type) (b: array a) (h: HS.mem) (new_pid: Ghost.erased perm_id) : Lemma (
   let b' = Array b.max_length b.content b.idx b.length new_pid in
   Ghost.reveal (get_array_current_max #a h b') =  Ghost.reveal (get_array_current_max #a h b)
) =
  get_array_current_max_same_with_new_pid' #a b h new_pid 0ul

let fresh_array_pid #a b' h0 h1 =
  Ghost.reveal b'.pid > Ghost.reveal (get_array_current_max h0 b') /\
  Ghost.reveal (get_array_current_max h1 b') = Ghost.reveal b'.pid

let cell_unused_in_intro (#t: Type) (b: array t) (i:nat{i < vlength b}) (h: HS.mem) : Lemma
  (requires (ucell_unused_in (aloc_cell b i) h))
  (ensures (loc_unused_in h `loc_includes` loc_cell b i))
  = MG.aloc_unused_in_intro cls (aloc_cell b i) h

let rec array_unused_in_intro' (#t: Type) (b: array t) (h : HS.mem) (i:nat{i <= vlength b}) : Lemma
  (requires (forall (j:nat{j < vlength b}). ucell_unused_in (aloc_cell b j) h))
  (ensures (loc_unused_in h `loc_includes` compute_loc_array b i))
  (decreases (vlength b - i))
  =
  if i >= vlength b then () else begin
    array_unused_in_intro' #t b h (i + 1);
    cell_unused_in_intro #t b i h;
    loc_includes_union_r (loc_unused_in h)(loc_cell b i) (compute_loc_array b (i+1))
  end

let rec array_unused_in_intro (#t: Type) (b: array t) (h : HS.mem)
  (cell_unused_in: (j:nat{j < vlength b}) -> Lemma ( ucell_unused_in (aloc_cell b j) h))
  : Lemma
  (ensures (loc_unused_in h `loc_includes` loc_array b))
  =
  Classical.forall_intro cell_unused_in;
  array_unused_in_intro' #t b h 0

let cell_used_in_intro (#t: Type) (b: array t) (i:nat{i < vlength b}) (h: HS.mem) : Lemma
  (requires (~ (ucell_unused_in (aloc_cell b i) h)))
  (ensures (loc_used_in h `loc_includes` loc_cell b i))
  = MG.aloc_used_in_intro cls (aloc_cell b i) h

let rec array_used_in_intro' (#t: Type) (b: array t) (h : HS.mem) (i:nat{i <= vlength b}) : Lemma
  (requires (forall (j:nat{j < vlength b}). ~ (ucell_unused_in (aloc_cell b j) h)))
  (ensures (loc_used_in h `loc_includes` compute_loc_array b i))
  (decreases (vlength b - i))
  =
  if i >= vlength b then () else begin
    array_used_in_intro' #t b h (i + 1);
    cell_used_in_intro #t b i h;
    loc_includes_union_r (loc_used_in h)(loc_cell b i) (compute_loc_array b (i+1))
  end

let rec array_used_in_intro (#t: Type) (b: array t) (h : HS.mem) : Lemma
  (requires (forall (j:nat{j < vlength b}). ~ (ucell_unused_in (aloc_cell b j) h)))
  (ensures (loc_used_in h `loc_includes` loc_array b))
  = array_used_in_intro' #t b h 0

let cell_not_used_pid_implies_aloc_unused_in (#t: Type) (b: array t) (i:nat{i < vlength b}) (h: HS.mem) :
  Lemma (requires (
    HS.contains h b.content /\ begin
      let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
      Ghost.reveal b.pid > get_current_max (Ghost.reveal perm_map)
    end
  ))
  (ensures (ucell_unused_in (aloc_cell b i) h))
=
  let r = frameOf b in
  let a = as_addr b in
  let cell = aloc_cell b i in
  let aux (t': Type) (b': array t') : Lemma (
    (frameOf b' = r /\ as_addr b' = a /\ HS.contains h b'.content) ==>
    (cell.b_index < U32.v b'.max_length /\
    begin
      let (_, perm_map) = Seq.index (HS.sel h b'.content) (cell.b_index) in
      cell.b_pid > get_current_max (Ghost.reveal perm_map)
    end))
  =
    let aux (_ : squash ((frameOf b' = r /\ as_addr b' = a /\ HS.contains h b'.content))) : Lemma
      (cell.b_index < U32.v b'.max_length /\
      begin
        let (_, perm_map) = Seq.index (HS.sel h b'.content) (cell.b_index) in
        cell.b_pid > get_current_max (Ghost.reveal perm_map)
      end)
     =
      live_same_arrays_equal_types #t #t' b b' h
    in Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux;
  ucell_unused_in_intro_unused_cell cell h t b
