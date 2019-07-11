module FStar.MG2

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

noeq
type cls (aloc: Type) : Type = | Cls:
  (aloc_includes: (
    aloc ->
    aloc ->
    GTot Type0
  )) ->
  (aloc_includes_refl: (
    (x: aloc) ->
    Lemma
    (aloc_includes x x)
  )) ->
  (aloc_includes_trans: (
    (x1: aloc) ->
    (x2: aloc) ->
    (x3: aloc) ->
    Lemma
    (requires (aloc_includes x1 x2 /\ aloc_includes x2 x3))
    (ensures (aloc_includes x1 x3))
  )) ->
  (aloc_disjoint: (
    (x1: aloc) ->
    (x2: aloc) ->
    GTot Type0
  )) ->
  (aloc_disjoint_sym: (
    (x1: aloc) ->
    (x2: aloc) ->
    Lemma
    (aloc_disjoint x1 x2 <==> aloc_disjoint x2 x1)
  )) ->
  (aloc_disjoint_not_includes: (
    (x1: aloc) ->
    (x2: aloc) ->
    Lemma
    ((aloc_disjoint x1 x2 /\ aloc_includes x1 x2) ==> False)
  )) ->
  (aloc_disjoint_includes: (
    (larger1: aloc) ->
    (larger2: aloc) ->
    (smaller1: aloc) ->
    (smaller2: aloc) ->
    Lemma
    (requires (aloc_disjoint larger1 larger2 /\ larger1 `aloc_includes` smaller1 /\ larger2 `aloc_includes` smaller2))
    (ensures (aloc_disjoint smaller1 smaller2))
  )) ->
  (aloc_preserved: (
    aloc ->
    HS.mem ->
    HS.mem ->
    GTot Type0
  )) ->
  (aloc_preserved_refl: (
    (x: aloc) ->
    (h: HS.mem) ->
    Lemma
    (aloc_preserved x h h)
  )) ->
  (aloc_preserved_trans: (
    (x: aloc) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (h3: HS.mem) ->
    Lemma
    (requires (aloc_preserved x h1 h2 /\ aloc_preserved x h2 h3))
    (ensures (aloc_preserved x h1 h3))
  )) ->
  (aloc_used_in: (
    (x: aloc) ->
    (h: HS.mem) ->
    GTot Type0
  )) ->
  (aloc_unused_in: (
    (x: aloc) ->
    (h: HS.mem) ->
    GTot Type0
  )) ->
  (aloc_used_in_unused_in_disjoint: (
    (x: aloc) ->
    (y: aloc) ->
    (h: HS.mem) ->
    Lemma
    ((x `aloc_used_in` h /\ y `aloc_unused_in` h) ==> x `aloc_disjoint` y)
  )) ->
  (aloc_used_in_includes: (
    (greater: aloc) ->
    (lesser: aloc) ->
    (h: HS.mem) ->
    Lemma
    ((greater `aloc_includes` lesser /\ greater `aloc_used_in` h) ==> lesser `aloc_used_in` h)
  )) ->
  (aloc_unused_in_includes: (
    (greater: aloc) ->
    (lesser: aloc) ->
    (h: HS.mem) ->
    Lemma
    ((greater `aloc_includes` lesser /\ greater `aloc_unused_in` h) ==> lesser `aloc_unused_in` h)
  )) ->
  (aloc_unused_in_preserved: (
    (x: aloc) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    Lemma
    (requires (x `aloc_unused_in` h1))
    (ensures (aloc_preserved x h1 h2))
  )) ->
  cls aloc

module GSet = FStar.GSet

type loc (#aloc: Type) (c: cls aloc) = (s: GSet.set aloc { forall (greater lesser: aloc) . {:pattern (greater `GSet.mem` s); (greater `c.aloc_includes` lesser)} greater `GSet.mem` s /\ greater `c.aloc_includes` lesser ==> lesser `GSet.mem` s })

let loc_includes (#aloc: Type) (#c: cls aloc) (greater lesser: loc c) : GTot Type0 =
  forall (x_lesser: aloc) . {:pattern (x_lesser `GSet.mem` lesser)} x_lesser `GSet.mem` lesser ==> (exists (x_greater: aloc) . {:pattern (x_greater `GSet.mem` greater)} x_greater `GSet.mem` greater /\ x_greater `c.aloc_includes` x_lesser)

let loc_disjoint (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot Type0 =
  forall (x1 x2: aloc) . {:pattern (GSet.mem x1 l1); (GSet.mem x2 l2)} (GSet.mem x1 l1 /\ GSet.mem x2 l2) ==> c.aloc_disjoint x1 x2

let loc_disjoint_sym (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : Lemma
  (loc_disjoint l1 l2 <==> loc_disjoint l2 l1)
  [SMTPat (loc_disjoint l1 l2)]
= Classical.forall_intro_2 c.aloc_disjoint_sym

let loc_union (#aloc: Type) (#c: cls aloc) (l1 l2: loc c) : GTot (loc c) =
  l1 `GSet.union` l2

let loc_includes_disjoint_elim
  #al (c: cls al)
  (l l1 l2: loc c)
: Lemma
  (requires ((l1 `loc_union` l2) `loc_includes` l /\ l1 `loc_disjoint` l /\ l1 `loc_disjoint` l2))
  (ensures (l2 `loc_includes` l))
= let f
    (x: al)
    (y: al)
  : Lemma
    (requires (GSet.mem x l /\ GSet.mem y (l1 `loc_union` l2) /\ y `c.aloc_includes` x))
    (ensures (GSet.mem y l2))
  = if GSet.mem y l2
    then ()
    else
      let g
        ()
      : Lemma
        (requires (GSet.mem y l1))
        (ensures False)
      = assert (l `loc_disjoint` l1);
        c.aloc_disjoint_not_includes y x
      in
      Classical.move_requires g ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (f x))

let preserved #al (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0 =
  forall (x: al) . {:pattern (x `GSet.mem` l)} x `GSet.mem` l ==> c.aloc_preserved x h1 h2

let modifies #al (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0 =
  forall (l' : loc c) . {:pattern (l' `loc_disjoint` l)} l' `loc_disjoint` l ==> preserved l' h1 h2

let used_in #al (c: cls al) (h: HS.mem) : Tot (loc c) =
  Classical.forall_intro_3 c.aloc_used_in_includes;
  GSet.comprehend (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x `c.aloc_used_in` h))

let unused_in #al (c: cls al) (h: HS.mem) : Tot (loc c) =
  Classical.forall_intro_3 c.aloc_unused_in_includes;
  GSet.comprehend (fun x -> FStar.StrongExcludedMiddle.strong_excluded_middle (x `c.aloc_unused_in` h))

open LowStar.Array.Defs
friend LowStar.Array.Defs
open LowStar.Permissions
module U32 = FStar.UInt32

// We need to define the atomic locations cell per cell. We will then define loc_buffer as the union of aloc of cells
// The reason for this is that we want to prove that the loc of the union of two buffers corresponds to the union of locs
// of the two smaller buffers.
noeq
type ucell : Type0 = {
  b_rid: HS.rid;
  b_addr: nat;
  b_max: nat;
  b_index:nat;
  b_pid:perm_id;
}

let ucell_matches_array_cell (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
frameOf b = cell.b_rid /\ as_addr b = cell.b_addr /\ U32.v b.max_length = cell.b_max /\ HS.contains h b.content /\
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
  ucell_matches_used_array_cell cell t b h /\ begin
    let i = cell.b_index - U32.v b.idx in
    live_cell h b i
  end

let ucell_preserved (cell:ucell) (h0 h1:HS.mem) : GTot Type0 =
  forall (t:Type0) (b':array t). begin let i = cell.b_index - U32.v b'.idx in // This cell corresponds to index i in the buffer
    ucell_matches_live_array_cell cell t b' h0 ==>
      (ucell_matches_live_array_cell cell t b' h1 /\  // If this cell is preserved, then its liveness is preserved
      sel h0 b' i == sel h1 b' i) // And its contents (snapshot + permission) are the same
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
  ((c1.b_max = c2.b_max) /\ // At this point c1 and c2 point to the same allocated array
    (c1.b_index <> c2.b_index \/           // Either the cells are different (i.e. spatially disjoint)
    c1.b_pid <> c2.b_pid))                 // Or they don't have the same permission

let ucell_unused_in (cell:ucell) (h: HS.mem) =
  // Either there is nothing allocated at that memory cell
  (forall (t:Type) (ref: HS.mreference t (Heap.trivial_preorder t)).
    (HS.as_addr ref = cell.b_addr /\ HS.frameOf ref = cell.b_rid) ==> (~ (HS.contains h ref))
  ) \/
  // Or there is an allocated array but it doesnt use the ucell
  (exists (t:Type) (b:array t). ucell_matches_unused_array_cell cell t b h)

let ucell_used_in (cell:ucell) (h: HS.mem) =
  // There exists an array allocated with the correct size that contains a live cell corresponding to the ucell
  exists (t:Type) (b:array t). ucell_matches_live_array_cell cell t b h


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

#set-options "--z3rlimit 30"

let cls_ucell : cls ucell = Cls #ucell
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
  ucell_used_in
  ucell_unused_in
  (fun x1 x2 h ->
    (* used_in and unused_in disjoint *)
    let aux (_ : squash(x1 `ucell_used_in` h /\ x2 `ucell_unused_in` h)) : Lemma
      (x1 `ucell_disjoint` x2)
      =
      let p (t: Type) = exists (b: array t). ucell_matches_live_array_cell x1 t b h in
      let pf : squash (exists (t: Type) . p t) = () in
      Classical.exists_elim (x1 `ucell_disjoint` x2) #Type #p pf (fun t ->
        let p (b: array t) = ucell_matches_live_array_cell x1 t b h in
        let pf : squash (exists (b: array t) . p b) = () in
        Classical.exists_elim (x1 `ucell_disjoint` x2) #(array t) #p pf (fun b ->
          let case1 = forall (t':Type) (ref: HS.mreference t' (Heap.trivial_preorder t')).
           (HS.as_addr ref = x2.b_addr /\ HS.frameOf ref = x2.b_rid) ==> (~ (HS.contains h ref))
          in
          let case2 = (exists (t':Type) (b':array t'). ucell_matches_unused_array_cell x2 t' b' h) in
          Classical.or_elim
            #case1 #case2 #(fun _ -> x1 `ucell_disjoint` x2)
            (fun (_ : squash (case1)) ->
              if (x1.b_rid <> x2.b_rid || x1.b_addr <> x2.b_addr) then () else
                assert((HS.contains h b.content) /\ ~ (HS.contains h b.content))
            )
            (fun (_ : squash (case2)) ->
              let p (t': Type) = exists (b': array t'). ucell_matches_unused_array_cell x2 t' b' h in
              let pf : squash (exists (t': Type) . p t') = () in
              Classical.exists_elim (x1 `ucell_disjoint` x2) #Type #p pf (fun t' ->
                let p (b': array t') = ucell_matches_unused_array_cell x2 t' b' h in
                let pf : squash (exists (b': array t') . p b') = () in
                Classical.exists_elim (x1 `ucell_disjoint` x2) #(array t') #p pf (fun b' ->
                  if (x1.b_rid <> x2.b_rid || x1.b_addr <> x2.b_addr) then () else begin
                    live_same_arrays_equal_types b' b h;
                    if x1.b_index <> x2.b_index then () else begin
                      let (_, perm_map1) = Seq.index (HS.sel h b.content) x1.b_index in
                      let (_, perm_map2) = Seq.index (HS.sel h b'.content) x2.b_index in
                      if x1.b_pid <> x2.b_pid then () else begin
                        assert(perm_map1 == perm_map2);
                        assert(
                          x1.b_pid <= get_current_max (Ghost.reveal perm_map1) /\
                          x1.b_pid > get_current_max (Ghost.reveal perm_map1)
                        )
                      end
                    end
                  end
                )
              )
            )
        )
      )
    in
    Classical.impl_intro aux
  )
  (fun greater lesser h -> ())
  (fun greater lesser h -> ())
  (fun x h0 h1 ->
    ucell_preserved_intro x h0 h1 (fun t b ->
      let i = x.b_index - U32.v b.idx in
      let case1 = forall (t':Type) (ref: HS.mreference t' (Heap.trivial_preorder t')).
        (HS.as_addr ref = x.b_addr /\ HS.frameOf ref = x.b_rid) ==> (~ (HS.contains h0 ref))
      in
      let case2 = exists (t':Type) (b':array t').
        ucell_matches_unused_array_cell x t' b' h0
      in
      let goal = ucell_matches_live_array_cell x t b h1 /\ sel h0 b i  == sel h1 b i in
      Classical.or_elim #case1 #case2 #(fun _ -> goal)
        (fun (_ : squash (case1)) -> assert((HS.contains h1 b.content) /\ (~ (HS.contains h1 b.content))))
        (fun (_ : squash (case2)) ->
          let p (t': Type) = exists (b': array t'). ucell_matches_unused_array_cell x t' b' h0 in
          let pf : squash (exists (t': Type) . p t') = () in
          Classical.exists_elim goal #Type #p pf (fun t' ->
            let p (b': array t') = ucell_matches_unused_array_cell x t' b' h0 in
            let pf : squash (exists (b': array t') . p b') = () in
            Classical.exists_elim goal #(array t') #p pf (fun b' ->
              live_same_arrays_equal_types b' b h0;
              let (_, perm_map) = Seq.index (HS.sel h0 b.content) x.b_index in
              LowStar.Permissions.lemma_greater_max_not_live_pid (Ghost.reveal perm_map) x.b_pid;
              assert((live_cell h0 b i) /\ (~ (live_cell h0 b i)))
            )
          )
        )
    )
  )

let loc_ucell = loc cls_ucell
