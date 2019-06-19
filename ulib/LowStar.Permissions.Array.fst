module LowStar.Permissions.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.ModifiesGen

open LowStar.Permissions
open LowStar.Permissions.References

open FStar.Real

noeq type array (a:Type0) :Type0 =
  | Array:
    max_length:U32.t ->
    content:HST.reference (Seq.lseq (value_with_perms a) (U32.v max_length)) ->
    idx:U32.t ->
    length:U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
    pid:Ghost.erased perm_id ->
    array a

(*** Definitions of Ghost operations and predicates on arrays ***)

let length #a b = UInt32.v b.length

let get' (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : GTot a =
  let ( _, perm_map ) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal b.pid)

let live_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : Type0 =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal b.pid) >. 0.0R /\ HS.contains h b.content

let live_cell_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) (pid:perm_id)
  : Type0 =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) pid >. 0.0R /\ HS.contains h b.content

let live #a h b =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). live_cell h b i)

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : Type0 =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal b.pid) == 1.0R /\ HS.contains h b.content

let writeable #a h b =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). writeable_cell h b i)

let lemma_writeable_implies_live (#a:Type) (h:HS.mem) (b:array a)
  : Lemma (requires writeable h b)
          (ensures live h b)
   = ()

let as_seq #a h b =
  let s = HS.sel h b.content in
  Seq.init (length b) (fun x -> fst (Seq.index s (U32.v b.idx + x)))

let sel (#a: Type0)  (h: HS.mem) (b: array a) (i:nat{i < length b}) : GTot (with_perm a) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  let perm = get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal b.pid) in
  let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal b.pid) in
  { wp_v = snapshot; wp_perm = perm}

// Two arrays are mergeable (for permissions) if they correspond to the same subarray in the same array, and they have different pids
let mergeable #a b1 b2 =
  b1.max_length == b2.max_length /\
  b1.content == b2.content /\
  b1.idx == b2.idx /\
  b1.length == b2.length /\
  (Ghost.reveal b1.pid <> Ghost.reveal b2.pid)

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

let frameOf (#a:Type0) (b:array a) : Tot HS.rid = HS.frameOf b.content
let as_addr (#a:Type0) (b:array a) : GTot nat = HS.as_addr b.content

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

let prove_bloc_preserved (#r: HS.rid) (#a: nat) (bloc: ucell r a) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = bloc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
      bloc.b_index >= U32.v b'.idx /\ bloc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i))
    (ensures (
      let i = bloc.b_index - U32.v b'.idx in
      live_cell h1 b' i /\
      sel h0 b' i  == sel h1 b' i
      ))
  )) : Lemma (ucell_preserved #r #a bloc h0 h1)
  =
  let aux (t: Type0) (b':array t) : Lemma(
      let i = bloc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
      bloc.b_index >= U32.v b'.idx /\ bloc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i ==>
        live_cell h1 b' i /\
        sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = bloc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      Ghost.reveal b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
      bloc.b_index >= U32.v b'.idx /\ bloc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i)
    ) : Lemma (
      let i = bloc.b_index - U32.v b'.idx in
      bloc.b_index >= U32.v b'.idx /\ bloc.b_index < U32.v b'.idx + U32.v b'.length /\
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
    prove_bloc_preserved #r #a b h1 h2 (fun t b' ->
      let ref_t = Seq.lseq (value_with_perms t) (U32.v b'.max_length) in
      f ref_t (Heap.trivial_preorder ref_t) b'.content
    )
  )

let bloc = MG.loc cls

let loc_none = MG.loc_none #ucell #cls
let loc_union (l1 l2:bloc) = MG.loc_union #ucell #cls l1 l2
let loc_disjoint (l1 l2:bloc) = MG.loc_disjoint #ucell #cls l1 l2
let loc_includes (l1 l2:bloc) = MG.loc_includes #ucell #cls l1 l2

let aloc_cell (#a:Type) (b:array a) (i:nat{i < length b}) : GTot (ucell (frameOf b) (as_addr b)) =
  let r = frameOf b in
  let a = as_addr b in
  {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i;       // The index of the cell is the index inside the bigger array
    b_pid = (Ghost.reveal b.pid);
  }

let loc_cell (#t:Type) (b:array t) (i:nat{i < length b}) : GTot bloc =
  let r = frameOf b in
  let a = as_addr b in
  MG.loc_of_aloc #ucell #cls #r #a (aloc_cell #t b i)

// The location of an array is the recursive union of all of its cells
let rec compute_loc_array (#a:Type) (b:array a) (i:nat{i <= length b})
  : GTot bloc
  (decreases (length b - i))
  = if i = length b then MG.loc_none
    else loc_cell b i `MG.loc_union #ucell #cls` compute_loc_array b (i+1)

let loc_array (#a:Type) (b:array a) : GTot bloc =
  compute_loc_array b 0

// The location of a cell of the array is included in the global loc_array
let lemma_includes_loc_cell_loc_array (#a:Type) (b:array a) (i:nat{i < length b})
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

let lemma_disjoint_pid_disjoint_cells (#a:Type) (b1 b2:array a) (i1:nat{i1 < length b1}) (i2:nat{i2 < length b2}) : Lemma
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

let rec lemma_disjoint_pid_disjoint_cell_array (#a:Type0) (b1 b2:array a) (i:nat{i < length b1}) (j:nat{j <= length b2}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (compute_loc_array b2 j) (loc_cell b1 i))
  (decreases (length b2 - j))
  = if j = length b2 then begin
       MG.loc_disjoint_none_r #ucell #cls (loc_cell b1 i);
       MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end else begin
      lemma_disjoint_pid_disjoint_cell_array b1 b2 i (j+1);
      lemma_disjoint_pid_disjoint_cells b1 b2 i j;
      MG.loc_disjoint_sym (compute_loc_array b2 (j+1)) (loc_cell b1 i);
      MG.loc_disjoint_union_r #ucell #cls (loc_cell b1 i) (loc_cell b2 j) (compute_loc_array b2 (j+1));
      MG.loc_disjoint_sym (loc_cell b1 i) (compute_loc_array b2 j)
    end

let rec lemma_disjoint_pid_disjoint_compute_array (#a:Type) (b1 b2:array a) (i:nat{i <= length b1}) : Lemma
  (requires Ghost.reveal b1.pid <> Ghost.reveal b2.pid /\ b1.max_length == b2.max_length)
  (ensures loc_disjoint (loc_array b2)  (compute_loc_array b1 i) )
  (decreases (length b1 - i))
  = if i = length b1 then MG.loc_disjoint_none_r #ucell #cls (loc_array b2)
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

let modifies (s:bloc) (h0 h1:HS.mem) : GTot Type0 = MG.modifies s h0 h1

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

(*** Stateful operations implementing the ghost specifications ***)


let index #a b i =
  let open HST in
  let h0 = get() in
  assert (live_cell h0 b (U32.v i));
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v

let upd #a b i v =
  let open HST in
  let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  assert (writeable_cell h0 b (U32.v i));
  let sb1 = Seq.upd sb0 (U32.v i) (v, Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) v)) in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  let h1 = get() in
  assert (as_seq h1 b `Seq.equal` Seq.upd (as_seq h0 b) (U32.v i) v);
  let r = frameOf b in
  let n = as_addr b in

  MG.modifies_aloc_intro
    #ucell #cls
    #r #n
    ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = (Ghost.reveal b.pid)})
    h0 h1
    (fun r -> ())
    (fun t pre b -> ())
    (fun t pre b -> ())
    (fun r n -> ())
    (fun aloc' ->
      let aloc = ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = (Ghost.reveal b.pid)}) in
      let aux (t:Type0) (b':array t) : Lemma
        (requires (
          let i = aloc'.b_index - U32.v b'.idx in
          frameOf b' == r /\ as_addr b' == n /\ Ghost.reveal b'.pid == aloc'.b_pid /\ U32.v b'.max_length == aloc'.b_max /\
          aloc'.b_index >= U32.v b'.idx /\ aloc'.b_index < U32.v b'.idx + U32.v b'.length /\
          live_cell h0 b' i))
        (ensures (let i = aloc'.b_index - U32.v b'.idx in
         live_cell h1 b' i /\
         (sel h0 b' i == sel h1 b' i))) =
         live_same_arrays_equal_types b b' h0;
         if aloc.b_index = aloc'.b_index then begin
           let s0 = HS.sel h0 b.content in
           let (v0, vp0) = Seq.index s0 aloc.b_index in
           only_one_live_pid_with_full_permission_specific #a #v0 (Ghost.reveal vp0) aloc.b_pid aloc'.b_pid
         end
         else begin
           live_same_arrays_equal_types b b' h1
         end
      in
      prove_bloc_preserved #r #n aloc' h0 h1 aux
    );

  assert (modifies (loc_cell b (U32.v i)) h0 h1);
  lemma_includes_loc_cell_loc_array b (U32.v i);
  MG.modifies_loc_includes (loc_array b) h0 h1 (loc_cell b (U32.v i))


let gsub #a b i len =
  match b with
  | Array max_len content idx length pid ->
    Array max_len content (U32.add idx i) len pid


let sub #a b i len =
  match b with
  | Array max_len content i0 len0 pid ->
    // Keep the same perm_id, to avoid being considered disjoint
    Array max_len content (U32.add i0 i) len pid


let alloc #a init len =
  let perm_map_pid = (
    let (vp, pid) = new_value_perms init true in
    ((vp <: perms_rec a), Ghost.hide pid)
  ) in
  let v = (init, Ghost.hide (fst perm_map_pid)) in
  let s = Seq.create (U32.v len) v in
  let h0 = HST.get() in
  let content = HST.ralloc_mm HS.root s in
  let h1 = HST.get() in
  MG.modifies_ralloc_post #ucell #cls HS.root s h0 content h1;
  let b = Array len content 0ul len (snd perm_map_pid) in
  assert (Seq.equal (as_seq h1 b) (Seq.create (U32.v len) init));
  b

val share_cell
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i < length b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires fun h0 -> live h0 b /\ (let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + U32.v i) in Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)))
  (ensures fun h0 _ h1 ->
    modifies (loc_cell b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    live_cell_pid h1 b (U32.v i) (Ghost.reveal pid) /\
    (forall (j:nat{j < length b}). j <> U32.v i ==> Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) == Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)) /\
    True) // TODO: Talk about permissions here

let share_cell #a b i pid =
  let open HST in
  let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  assert (live_cell h0 b (U32.v i));
  lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid);
  let sb1 = Seq.upd sb0 (U32.v i) (v_init, Ghost.hide (share_perms_with_pid #a #v_init (Ghost.reveal perm_map) (Ghost.reveal b.pid) (Ghost.reveal pid))) in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  let h1 = get() in
  assert (as_seq h1 b `Seq.equal` as_seq h0 b);
  let r = frameOf b in
  let n = as_addr b in
  MG.modifies_aloc_intro
    #ucell #cls
    #r #n
    ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = Ghost.reveal b.pid})
    h0 h1
    (fun r -> ())
    (fun t pre b -> ())
    (fun t pre b -> ())
    (fun r n -> ())
    (fun aloc' ->
       prove_bloc_preserved #r #n aloc' h0 h1 (fun t b'->
         live_same_arrays_equal_types b b' h0;
         live_same_arrays_equal_types b b' h1;
         if aloc'.b_index <> U32.v b.idx + U32.v i then ()
         else lemma_greater_max_not_live_pid (Ghost.reveal perm_map) (Ghost.reveal pid)
       )
    )

val share_cells
  (#a:Type0)
  (b:array a)
  (i:U32.t{U32.v i <= length b})
  (pid:Ghost.erased perm_id)
  : Stack unit
  (requires fun h0 -> live h0 b /\
    (forall (j:nat{j < length b}). j >= U32.v i ==> (let (_, perm_map) = Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) in Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)) ))
  (ensures fun h0 b' h1 ->
    modifies (compute_loc_array b (U32.v i)) h0 h1 /\
    live h1 b /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    (forall (j:nat{j < length b}). j < U32.v i ==> Seq.index (HS.sel h0 b.content) (U32.v b.idx + j) == Seq.index (HS.sel h1 b.content) (U32.v b.idx + j)) /\
    (forall (j:nat{j < length b}). j >= U32.v i ==> live_cell_pid h1 b j (Ghost.reveal pid)) /\
    True) // TODO: Talk about permissions here

let rec share_cells #a b i pid =
  let h0 = HST.get() in
  if U32.v i >= length b then
    MG.modifies_none_intro #ucell #cls h0 h0
      (fun _ -> ())
      (fun _ _ _ -> ())
      (fun _ _ -> ())
  else begin
    share_cells b (U32.add i 1ul) pid;
    let h1 = HST.get() in
    share_cell b i pid;
    let h2 = HST.get () in
    let s12 = compute_loc_array b (U32.v i + 1) in
    let s23 = loc_cell b (U32.v i) in
    MG.loc_union_comm #ucell #cls s12 s23;
    MG.modifies_trans #ucell #cls s12 h0 h1 s23 h2
  end

val get_array_current_max (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t{U32.v i <= length b}) : Pure (Ghost.erased perm_id)
  (requires True)
  (ensures fun pid -> forall (j:nat{j < length b}). j >= U32.v i ==>
    (let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + j) in
      Ghost.reveal pid > get_current_max (Ghost.reveal perm_map)))
  (decreases (length b - U32.v i))

let rec get_array_current_max #a h b i =
  if U32.v i = length b then (Ghost.hide 1)
  else  begin
    let max_end = get_array_current_max h b (U32.add i 1ul) in
    let (v, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + U32.v i) in
    let current_max = Ghost.hide (get_current_max (Ghost.reveal perm_map) + 1) in
    Ghost.elift2 (fun (a b:perm_id) -> if a > b then a else b) max_end current_max
  end

val lemma_different_live_pid (#a:Type0) (h:HS.mem) (b:array a{length b > 0}) : Lemma
  (requires live h b)
  (ensures Ghost.reveal (get_array_current_max h b 0ul) <> Ghost.reveal b.pid)

let lemma_different_live_pid #a h b =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx) in
  assert (live_cell h b 0);
  lemma_live_pid_smaller_max (Ghost.reveal perm_map) (Ghost.reveal b.pid)

let share #a b =
  let open HST in
  let h0 = get() in
  let new_pid = get_array_current_max h0 b 0ul in
  share_cells b 0ul new_pid;
  let h1 = get() in
  let b' = Array b.max_length b.content b.idx b.length new_pid in
  assert (as_seq h1 b' `Seq.equal` as_seq h0 b);
  lemma_different_live_pid h0 b;
  lemma_disjoint_pid_disjoint_arrays b b';
  b'


val merge_cell:
  #a: Type ->
  b: array a ->
  b1: array a ->
  i:U32.t{U32.v i < length b} ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live h0 b1 /\
    summable_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (sel h1 b (U32.v i)).wp_perm = sum_permissions (sel h0 b (U32.v i)).wp_perm (sel h0 b1 (U32.v i)).wp_perm /\
    (sel h1 b (U32.v i)).wp_v == (sel h0 b (U32.v i)).wp_v /\
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
  (**)     )
  (**)     (fun t pre b -> ())
  (**)     (fun r n -> ())
  (**)  (fun r' n' bloc' ->
  (**)     prove_bloc_preserved #r' #n' bloc' h0 h1 (fun t' b' ->
  (**)       MG.loc_includes_refl cell;
  (**)       MG.loc_includes_union_l cell cell1 cell;
  (**)       MG.loc_includes_refl (MG.loc_of_aloc #ucell #cls #r' #n' bloc');
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc bloc')
  (**)         l
  (**)         (MG.loc_of_aloc bloc')
  (**)         cell;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc bloc') cell;
  (**)       MG.loc_includes_refl cell1;
  (**)       MG.loc_includes_union_l cell cell1 cell1;
  (**)       MG.loc_disjoint_includes
  (**)         (MG.loc_of_aloc bloc')
  (**)         l
  (**)         (MG.loc_of_aloc bloc')
  (**)         cell1;
  (**)       MG.loc_disjoint_sym (MG.loc_of_aloc bloc') cell1;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n bloc' acell;
  (**)       MG.loc_disjoint_aloc_elim #ucell #cls #r' #n' #r #n bloc' acell1;
  (**)       let i' = bloc'.b_index - U32.v b'.idx in
  (**)       let (_, new_perm_map) = Seq.index (HS.sel h1 b'.content) (U32.v b'.idx + i') in
  (**)       if r' = r && n' = n then begin
  (**)         live_same_arrays_equal_types b b' h0;
  (**)         live_same_arrays_equal_types b b' h1
  (**)       end else ()
  (**)     )
  (**)  )

val merge:
  #a: Type ->
  b: array a ->
  b1: array a ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live h0 b1 /\
    (forall (i:nat{i < length b}). summable_permissions (sel h0 b i).wp_perm (sel h0 b1 i).wp_perm)
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < length b}).
      (sel h1 b i).wp_perm = sum_permissions (sel h0 b i).wp_perm (sel h0 b1 i).wp_perm /\
      (sel h1 b i).wp_v == (sel h0 b i).wp_v
    ) /\
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))
