module Steel.IArray

open Steel.FractionalPermission
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

module G = FStar.Ghost
module Seq = FStar.Seq
module Set = FStar.Set
module Map = FStar.Map
module U32 = FStar.UInt32
module A = Steel.Array

#set-options "--ide_id_info_off --print_implicits"

noeq
type iarray k v (h:hash_fn_t k) = {
  store_len    : u32;
  store        : A.array (option (k & v));
  g_repr       : ghost_ref (Map.t k v);
  default_v    : G.erased v;
  store_len_pf : squash (A.length store == U32.v store_len);
}

let rec seq_to_map (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v)
  : Tot (repr k v) (decreases Seq.length s)
  = if Seq.length s = 0
    then empty_repr default_v
    else let hd, tl = Seq.head s, Seq.tail s in
         let m = seq_to_map tl default_v in
         match hd with
         | Some (x, y) -> Map.upd m x y
         | None -> m

let rec seq_to_map_empty_seq (#k:eqtype) (#v:Type0) (n:nat) (default_v:v)
  : Lemma (Map.equal (seq_to_map (Seq.create n None) default_v)
                     (empty_repr #k #v default_v))
  = if n = 0
    then ()
    else begin
      assert (Seq.equal (Seq.tail (Seq.create #(option (k & v)) n None))
                        (Seq.create (n-1) None));
      seq_to_map_empty_seq #k #v (n-1) default_v
    end

let sub_map_of (#k:eqtype) (#v:Type0) (m1 m2:Map.t k v) : prop =
  Map.domain m1 `Set.subset` Map.domain m2 /\
  (forall (x:k). m1 `Map.contains` x ==> m1 `Map.sel` x == m2 `Map.sel` x)

[@@__reduce__]
let store_contents_pred (#k:eqtype) (#v:Type0) (#h:hash_fn_t k)
  (arr:iarray k v h) (m:repr k v)
  : A.elseq (option (k & v)) (A.length arr.store) -> vprop
  = fun s ->
    A.varray_pts_to arr.store s
      `star`
    ghost_pts_to arr.g_repr full_perm m
      `star`
    pure (seq_to_map s arr.default_v `sub_map_of` m)

let ipts_to arr m = h_exists (store_contents_pred arr m)

let create #k #v h x n =
  let store = A.malloc #(option (k & v)) None n in
  let g_ref = ghost_alloc_pt (G.hide (empty_repr #k #v x)) in
  let arr = {
    store_len = n;
    store = store;
    g_repr = g_ref;
    default_v = x;
    store_len_pf = () } in
  let s : A.elseq (option (k & v)) (A.length arr.store) = A.intro_varray_pts_to store in
  seq_to_map_empty_seq #k #v (U32.v n) x;
  intro_pure (sub_map_of (seq_to_map s arr.default_v) (empty_repr #k #v x));
  assert_spinoff (ghost_pts_to g_ref full_perm (empty_repr #k #v x) ==
                  ghost_pts_to arr.g_repr full_perm (empty_repr #k #v x));
  change_equal_slprop (ghost_pts_to g_ref full_perm (empty_repr #k #v x))
                      (ghost_pts_to arr.g_repr full_perm (empty_repr #k #v x));
  change_equal_slprop (A.varray_pts_to store s)
                      (A.varray_pts_to arr.store s);
  intro_exists s (store_contents_pred arr (empty_repr #k #v x));
  return arr
