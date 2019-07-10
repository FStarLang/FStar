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

let ucell_preserved (b:ucell) (h0 h1:HS.mem) : GTot Type0 =
  forall (t:Type0) (b':array t).
    (let i = b.b_index - U32.v b'.idx in // This cell corresponds to index i in the buffer
      (frameOf b' == b.b_rid /\ as_addr b' == b.b_addr /\ b'.pid == (Ghost.hide b.b_pid) /\ U32.v b'.max_length == b.b_max /\
        b.b_index >= U32.v b'.idx /\ b.b_index < U32.v b'.idx + U32.v b'.length /\ // If this cell is part of the buffer
        live_cell h0 b' i ==>
          live_cell h1 b' i /\ // If this cell is preserved, then its liveness is preserved
          (sel h0 b' i == sel h1 b' i))) // And its contents (snapshot + permission) are the same

let prove_loc_preserved (loc: ucell) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == loc.b_rid /\ as_addr b' == loc.b_addr /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i))
    (ensures (
      let i = loc.b_index - U32.v b'.idx in
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
      ))
  )) : Lemma (ucell_preserved loc h0 h1)
  =
  let aux (t: Type0) (b':array t) : Lemma(
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == loc.b_rid /\ as_addr b' == loc.b_addr /\
      Ghost.reveal b'.pid == loc.b_pid /\ U32.v b'.max_length == loc.b_max /\
      loc.b_index >= U32.v b'.idx /\ loc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i ==>
        live_cell h1 b' i /\
        sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = loc.b_index - U32.v b'.idx in
      frameOf b' == loc.b_rid /\ as_addr b' == loc.b_addr /\
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
let ucell_includes (c1 c2: ucell) : GTot Type0 =
  c1.b_rid = c2.b_rid /\
  c1.b_addr = c2.b_addr /\
  c1.b_pid = c2.b_pid /\
  c1.b_index = c2.b_index /\
  c1.b_max = c2.b_max


let ucell_disjoint (c1 c2:ucell) : GTot Type0 =
  (c1.b_rid <> c2.b_rid) \/
  (c1.b_addr <> c2.b_addr) \/
  (c1.b_max == c2.b_max /\
    (c1.b_index <> c2.b_index \/           // Either the cells are different (i.e. spatially disjoint)
    c1.b_pid <> c2.b_pid))                 // Or they don't have the same permission

let live_ucell_matches_array (cell: ucell) (t:Type) (b: array t) (h: HS.mem) =
frameOf b = cell.b_rid /\ as_addr b = cell.b_addr /\ U32.v b.max_length = cell.b_max /\ HS.contains h b.content /\
     cell.b_index >= U32.v b.idx /\ cell.b_index < U32.v b.idx + U32.v b.length /\ // If this cell is part of the buffer
     live_cell h b (cell.b_index - U32.v b.idx)

let ucell_unused_in (cell:ucell) (h: HS.mem) =
  forall (t:Type) (b:array t).
    live_ucell_matches_array cell t b h ==>
    begin
      let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
      cell.b_pid > get_current_max (Ghost.reveal perm_map)
    end



let ucell_used_in (cell:ucell) (h: HS.mem) =
  let used_in  (t:Type) (b:array t) =
    live_ucell_matches_array cell t b h ==>
    begin
      let (_, perm_map) = Seq.index (HS.sel h b.content) cell.b_index in
      cell.b_pid <= get_current_max (Ghost.reveal perm_map)
    end
  in
  (forall (t:Type) (b:array t). used_in t b) /\
  (exists (t:Type) (b:array t). used_in t b)

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
  (fun x y h ->
    (* used_in and unused_in disjoint *)
    let aux (_ : squash(x `ucell_used_in` h /\ y `ucell_unused_in` h)) : Lemma
      (x `ucell_disjoint` y)
      = admit()
    in
    Classical.impl_intro aux
  )
  (fun greater lesser h -> ())
  (fun greater lesser h -> ())
  (fun x h1 h2 ->
    (* aloc_unused_in_preserved *)
    admit()
  )

let loc_ucell = loc cls_ucell
