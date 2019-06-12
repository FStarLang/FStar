module LowStar.Permissions.Array

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32

open LowStar.Permissions
open LowStar.Permissions.References

open FStar.Real

noeq type array (a:Type0) :Type0 =
  | Array:
    max_length:U32.t ->
    content:HST.reference (Seq.lseq (value_with_perms a) (U32.v max_length)) ->
    idx:U32.t ->
    length:U32.t{U32.v idx + U32.v length <= U32.v max_length} ->
    b_pid:perm_id ->
    array a

let length (#a:Type) (b:array a) = UInt32.v b.length

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) =
  let ( _, perm_map ) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_snapshot_from_pid (Ghost.reveal perm_map) b.b_pid

let live_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) b.b_pid >. 0.0R

let live (#a:Type) (h:HS.mem) (b:array a) =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). {:pattern (get h b i)} live_cell h b i)

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  get_permission_from_pid (Ghost.reveal perm_map) b.b_pid == 1.0R

let writeable (#a:Type) (h:HS.mem) (b:array a) =
  HS.contains h b.content /\
  (forall (i:nat{i < length b}). writeable_cell h b i)

let lemma_writeable_implies_live (#a:Type) (h:HS.mem) (b:array a)
  : Lemma (requires writeable h b)
          (ensures live h b)
   = ()

val index (#a:Type) (b:array a) (i:UInt32.t{UInt32.v i < length b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (UInt32.v i))

let index #a b i =
  let open HST in
  let s = ! b.content in
  let ( v, _ ) = Seq.index s (U32.v b.idx + U32.v i) in
  v

let as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == length b}) =
  let s = HS.sel h b.content in
  Seq.init (length b) (fun x -> fst (Seq.index s (U32.v b.idx + x))) 

let equiv_get_as_seq (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b /\ live_cell h b i})
  : Lemma (Seq.index (as_seq h b) i == get h b i)
  = ()

//TODO: Need to add modifies. First need to define locs
val upd (#a:Type) (b:array a) (i:UInt32.t{UInt32.v i < length b}) (v:a)
    : Stack unit (requires fun h -> writeable h b)
                 (ensures fun h0 _ h1 ->  writeable h1 b /\
                                       as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v)

let upd #a b i v =
  let open HST in
  let h0 = get() in
  let s = ! b.content in
  let sb0 = Seq.slice s (U32.v b.idx) (U32.v b.idx + U32.v b.length) in
  let (v_init, perm_map) = Seq.index s (U32.v b.idx + U32.v i) in
  assert (writeable_cell h0 b (U32.v i));
  let sb1 = Seq.upd sb0 (U32.v i) (v, Ghost.hide (change_snapshot #a #v_init (Ghost.reveal perm_map) b.b_pid v)) in
  let s1 = Seq.replace_subseq s (U32.v b.idx) (U32.v b.idx + U32.v b.length) sb1 in
  b.content := s1;
  let h1 = get() in
  assert (as_seq h1 b `Seq.equal` Seq.upd (as_seq h0 b) (U32.v i) v)

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
