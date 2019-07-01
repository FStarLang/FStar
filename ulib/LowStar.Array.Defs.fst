module LowStar.Array.Defs

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module F = FStar.FunctionalExtensionality
module G = FStar.Ghost
module U32 = FStar.UInt32
module MG = FStar.ModifiesGen

open LowStar.Permissions

open FStar.Real


type value_with_perms (a: Type0) = vp : (a & Ghost.erased (perms_rec a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

noeq type array (a:Type0) :Type0 =
  | Array:
    max_length:U32.t{U32.v max_length > 0} ->
    content:HST.reference (Seq.lseq (value_with_perms a) (U32.v max_length)) ->
    idx:U32.t ->
    length:U32.t{U32.v idx + U32.v length <= U32.v max_length /\ U32.v length > 0} ->
    pid:Ghost.erased perm_id ->
    array a

(*** Definitions of Ghost operations and predicates on arrays ***)

let length #a b = b.length

let as_seq #a h b =
  let s = HS.sel h b.content in
  Seq.init (vlength b) (fun x -> fst (Seq.index s (U32.v b.idx + x)))

let as_perm_seq (#a:Type) (h:HS.mem) (b: array a) : GTot (Seq.seq permission) =
  let s = HS.sel h b.content in
  Seq.init_ghost (vlength b) (fun x ->
    get_permission_from_pid (Ghost.reveal (snd (Seq.index s (U32.v b.idx + x)))) (Ghost.reveal b.pid)
  )

let live_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : Type0 =
  get_perm #a h b i >. 0.0R /\ HS.contains h b.content

let as_perm_seq_pid (#a:Type) (h:HS.mem) (b: array a) (pid:perm_id) : GTot (Seq.seq permission) =
  let s = HS.sel h b.content in
  Seq.init_ghost (vlength b) (fun x ->
    get_permission_from_pid (Ghost.reveal (snd (Seq.index s (U32.v b.idx + x)))) pid
  )

let get_perm_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id) : GTot P.permission
  = Seq.index (as_perm_seq_pid h b pid) i

let cell_perm_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id) =
  Seq.index (as_perm_seq_pid #a h b pid) i

let live_cell_pid (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) (pid:perm_id)
  : Type0 =
  cell_perm_pid #a h b i pid >. 0.0R /\ HS.contains h b.content

let live #a h b =
  HS.contains h b.content /\
  (forall (i:nat{i < vlength b}). live_cell h b i)

let sel (#a: Type0)  (h: HS.mem) (b: array a) (i:nat{i < vlength b}) : GTot (with_perm a) =
  let (_, perm_map) = Seq.index (HS.sel h b.content) (U32.v b.idx + i) in
  let perm = get_perm h b i in
  let snapshot = get h b i in
  { wp_v = snapshot; wp_perm = perm}

// Two arrays are mergeable (for permissions) if they correspond to the same subarray in the same array, and they have different pids
let mergeable #a b1 b2 =
  b1.max_length == b2.max_length /\
  b1.content == b2.content /\
  b1.idx == b2.idx /\
  b1.length == b2.length /\
  (Ghost.reveal b1.pid <> Ghost.reveal b2.pid)

let mergeable_same_length (#a:Type0) (b1 b2:array a) : Lemma
  (requires (mergeable b1 b2))
  (ensures (length b1 = length b2))
= ()

let mergeable_comm (#a: Type0) (b1 b2: array a): Lemma
  (requires (mergeable b1 b2))
  (ensures (mergeable b2 b1))
= ()

let frameOf (#a:Type0) (b:array a) : Tot HS.rid = HS.frameOf b.content
let as_addr (#a:Type0) (b:array a) : GTot nat = HS.as_addr b.content

let freeable #a b = b.idx = 0ul /\ b.max_length = b.length /\
  HS.is_mm b.content /\ HST.is_eternal_region (frameOf b)


(*** Sub-buffers *)


let gsub #a b i len =
    let b' = Array b.max_length b.content (U32.add b.idx i) len b.pid in
    let aux (h:HS.mem) : Lemma
      (as_seq h b' == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) /\
       as_perm_seq h b' == Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len)) =
      let sb' = as_seq h b' in
      let sbslice =  Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) in
      let sbp' =  as_perm_seq h b' in
      let sbpslice =  Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len) in
      FStar.Seq.Base.lemma_eq_intro sb' sbslice;
      FStar.Seq.Base.lemma_eq_intro sbp' sbpslice
    in
    Classical.forall_intro aux;
    b'

let live_gsub #a h b i len =
  let b' = gsub b i len in
  let f1 (_ : squash (live h b))  : Lemma (live h b') =
    assert(forall (j:nat{j < vlength b'}). get_perm #a h b (U32.v i + j) >. 0.0R);
    assert(forall (j:nat{j < vlength b'}). get_perm #a h b' j >. 0.0R)
  in
  FStar.Classical.impl_intro f1

let len_gsub #a b i len' = ()

let frameOf_gsub #a b i len = ()

let as_addr_gsub #a b i len = ()

let gsub_inj #a b1 b2 i1 i2 len1 len2 = ()

let gsub_gsub #a b i1 len1 i2 len2 = ()

let gsub_zero_length #a b = ()

let msub #a b i len =
 Array b.max_length b.content (U32.add b.idx i) len b.pid
