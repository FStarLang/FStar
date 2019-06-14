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
    pid:perm_id ->
    array a

(*** Definitions of Ghost operations and predicates on arrays ***)

let length (#a:Type) (b:array a) : nat = UInt32.v b.length

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : GTot a =
  let ( _, perm_map ) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_snapshot_from_pid (Ghost.reveal perm_map) b.pid

let live_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : Type0 =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) b.pid >. 0.0R /\ HS.contains h b.content

let live (#a:Type) (h:HS.mem) (b:array a) : Type0 =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). {:pattern (get h b i)} live_cell h b i)

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : Type0 =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) b.pid == 1.0R /\ HS.contains h b.content

let writeable (#a:Type) (h:HS.mem) (b:array a) : Type0 =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). writeable_cell h b i)

let lemma_writeable_implies_live (#a:Type) (h:HS.mem) (b:array a)
  : Lemma (requires writeable h b)
          (ensures live h b)
   = ()

let as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == length b}) =
  let s = HS.sel h b.content in
  Seq.init (length b) (fun x -> fst (Seq.index s (U32.v b.idx + x))) 

let equiv_get_as_seq (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b /\ live_cell h b i})
  : Lemma (Seq.index (as_seq h b) i == get h b i)
  = ()

let sel (#a: Type0)  (h: HS.mem) (b: array a) (i:nat{i < length b}) : GTot (with_perm a) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  let perm = get_permission_from_pid (Ghost.reveal perm_map) b.pid in
  let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) b.pid in
  { wp_v = snapshot; wp_perm = perm}

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
      (frameOf b' == r /\ as_addr b' == a /\ b'.pid == b.b_pid /\ U32.v b'.max_length == b.b_max /\
        b.b_index >= U32.v b'.idx /\ b.b_index < U32.v b'.idx + U32.v b'.length /\ // If this cell is part of the buffer
        live_cell h0 b' i ==>
          live_cell h1 b' i /\ // If this cell is preserved, then its liveness is preserved
          (sel h0 b' i == sel h1 b' i))) // And its contents (snapshot + permission) are the same

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
  (fun #r #a b h1 h2 f -> admit())

let bloc = MG.loc cls

let loc_union (l1 l2:bloc) = MG.loc_union #ucell #cls l1 l2
let loc_disjoint (l1 l2:bloc) = MG.loc_disjoint #ucell #cls l1 l2
let loc_includes (l1 l2:bloc) = MG.loc_includes #ucell #cls l1 l2

let loc_cell (#a:Type) (b:array a) (i:nat{i < length b}) : GTot bloc =
  let r = frameOf b in
  let a = as_addr b in
  let aloc = {
    b_max = U32.v b.max_length;
    b_index = U32.v b.idx + i;       // The index of the cell is the index inside the bigger array
    b_pid = b.pid;
  } in
  MG.loc_of_aloc #ucell #cls #r #a aloc

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
  
let modifies (s:bloc) (h0 h1:HS.mem) : GTot Type0 = MG.modifies s h0 h1

let prove_bloc_preserved (#r: HS.rid) (#a: nat) (bloc: ucell r a) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> b': array t -> Lemma
    (requires (
      let i = bloc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
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
      b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
      bloc.b_index >= U32.v b'.idx /\ bloc.b_index < U32.v b'.idx + U32.v b'.length /\
      live_cell h0 b' i ==>
        live_cell h1 b' i /\
        sel h0 b' i  == sel h1 b' i)
  =
  let aux' (_ : squash (
      let i = bloc.b_index - U32.v b'.idx in
      frameOf b' == r /\ as_addr b' == a /\
      b'.pid == bloc.b_pid /\ U32.v b'.max_length == bloc.b_max /\
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

val index (#a:Type) (b:array a) (i:UInt32.t{UInt32.v i < length b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (UInt32.v i))

let index #a b i =
  let open HST in
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v


val upd (#a:Type) (b:array a) (i:UInt32.t{UInt32.v i < length b}) (v:a)
    : Stack unit (requires fun h -> writeable h b)
                 (ensures fun h0 _ h1 ->  writeable h1 b /\
                                       modifies (loc_array b) h0 h1 /\
                                       as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v)

let upd #a b i v =
  let open HST in
  let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  assert (writeable_cell h0 b (U32.v i));
  let sb1 = Seq.upd sb0 (U32.v i) (v, Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) b.pid v)) in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  let h1 = get() in
  assert (as_seq h1 b `Seq.equal` Seq.upd (as_seq h0 b) (U32.v i) v);
  let r = frameOf b in
  let n = as_addr b in
  
  MG.modifies_aloc_intro
    #ucell #cls
    #r #n
    ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = b.pid})
    h0 h1
    (fun r -> ())
    (fun t pre b -> ())
    (fun t pre b -> ())
    (fun r n -> ())
    (fun aloc' -> 
      let aloc = ({b_max = U32.v b.max_length; b_index = U32.v b.idx + U32.v i; b_pid = b.pid}) in
      let aux (t:Type0) (b':array t) : Lemma
        (requires (
          let i = aloc'.b_index - U32.v b'.idx in
          frameOf b' == r /\ as_addr b' == n /\ b'.pid == aloc'.b_pid /\ U32.v b'.max_length == aloc'.b_max /\
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

val gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  :Ghost (array a)
         (requires (U32.v i + U32.v len <= length b))
	 (ensures (fun _ -> True))

let gsub #a b i len =
  match b with
  | Array max_len content idx length pid ->
    Array max_len content (U32.add idx i) len pid

val sub (#a:Type) (b:array a) (i:UInt32.t) (len:UInt32.t)
  : Stack (array a)
          (requires fun h -> UInt32.v i + UInt32.v len <= length b /\ live h b)
          (ensures fun h0 y h1 -> h0 == h1 /\ y == gsub b i len)

let sub #a b i len =
  match b with
  | Array max_len content i0 len0 pid ->
    // Keep the same perm_id, to avoid being considered disjoint
    Array max_len content (U32.add i0 i) len pid
