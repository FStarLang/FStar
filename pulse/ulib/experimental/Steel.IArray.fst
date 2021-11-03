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
  store_len    : n:u32{U32.v n > 0};
  store        : A.array (option (k & v));
  g_repr       : ghost_ref (Map.t k v);
  default_v    : G.erased v;
  store_len_pf : squash (A.length store == U32.v store_len);
}

let seq_props (#k:eqtype) (#v:Type0) (h:hash_fn_t k)
  (s:Seq.seq (option (k & v))) : prop =
  
  0 < Seq.length s /\ UInt.size (Seq.length s) 32 /\
  
  (forall (i:nat{i < Seq.length s}).
     Some? (Seq.index s i) ==>
     (let Some (x, _) = Seq.index s i in
      U32.v (h x) `UInt.mod` (Seq.length s) == i))

let seq_props_derived (#k:eqtype) (#v:Type0) (h:hash_fn_t k) (s:Seq.seq (option (k & v))) : prop =
  forall (i j:(k:nat{k < Seq.length s})).{:pattern Seq.index s i; Seq.index s j}
    (i =!= j /\ Some? (Seq.index s i) /\ Some? (Seq.index s j)) ==>
    (fst (Some?.v (Seq.index s i)) =!= fst (Some?.v (Seq.index s j)))  

let seq_props_derived_lemma (#k:eqtype) (#v:Type0) (h:hash_fn_t k) (s:Seq.seq (option (k & v)))
  : Lemma
      (requires seq_props h s)
      (ensures seq_props_derived h s)
  = ()

let rec seq_to_map (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v)
  : Tot (repr k v) (decreases Seq.length s)
  = if Seq.length s = 0
    then empty_repr default_v
    else let hd, tl = Seq.head s, Seq.tail s in
         let m = seq_to_map tl default_v in
         match hd with
         | Some (x, y) -> Map.upd m x y
         | None -> m

let submap_of (#k:eqtype) (#v:Type0) (m1 m2:Map.t k v) : prop =
  let open FStar.Map in
  forall (x:k). m1 `contains` x ==> (m2 `contains` x /\ m1 `sel` x == m2 `sel` x)

[@@__reduce__]
let store_contents_pred (#k:eqtype) (#v:Type0) (#h:hash_fn_t k)
  (arr:iarray k v h) (m:repr k v)
  : Seq.lseq (option (k & v)) (A.length arr.store) -> vprop
  = fun s ->
    A.varray_pts_to arr.store s
      `star`
    ghost_pts_to arr.g_repr full_perm m
      `star`
    pure (seq_props h s /\ seq_to_map s arr.default_v `submap_of` m)

[@@__reduce__]
let ipts_to arr m = h_exists (store_contents_pred arr m)

let rec seq_to_map_empty_seq (#k:eqtype) (#v:Type0) (n:nat) (default_v:v)
  : Lemma (Map.equal (seq_to_map (Seq.create n None) default_v)
                     (empty_repr #k #v default_v))
  = if n = 0 then ()
    else begin
      assert (Seq.equal (Seq.tail (Seq.create #(option (k & v)) n None))
                        (Seq.create (n-1) None));
      seq_to_map_empty_seq #k #v (n-1) default_v
    end

let rec seq_to_map_ith (#k:eqtype) (#v:Type0) (h:hash_fn_t k) (s:Seq.seq (option (k & v)))
  (default_v:v)
  (i:nat{i < Seq.length s})
  : Lemma
      (requires seq_props_derived h s /\ Some? (Seq.index s i))
      (ensures (let Some (x, y) = Seq.index s i in
                Map.contains (seq_to_map s default_v) x /\
                Map.sel (seq_to_map s default_v) x == y))
      (decreases i)
  = if i = 0 then () else seq_to_map_ith h (Seq.tail s) default_v (i-1)

let create #k #v h x n =
  let store = A.malloc #(option (k & v)) None n in
  let g_ref = ghost_alloc_pt (G.hide (empty_repr #k #v x)) in
  let arr = {
    store_len = n;
    store = store;
    g_repr = g_ref;
    default_v = x;
    store_len_pf = () } in
  let s = A.intro_varray_pts_to arr.store in
  seq_to_map_empty_seq #k #v (U32.v n) x;
  intro_pure (seq_props h s /\ submap_of (seq_to_map s arr.default_v) (empty_repr #k #v x));
  assert_spinoff (ghost_pts_to g_ref full_perm (empty_repr #k #v x) ==
                  ghost_pts_to arr.g_repr full_perm (empty_repr #k #v x));
  change_equal_slprop (ghost_pts_to g_ref full_perm (empty_repr #k #v x))
                      (ghost_pts_to arr.g_repr full_perm (empty_repr #k #v x));
  intro_exists (G.reveal s) (store_contents_pred arr (empty_repr #k #v x));
  return arr

let index #k #v #h #m a i =
  let s = witness_exists () in
  A.elim_varray_pts_to a.store s;
  elim_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m);
  let vopt = A.index a.store (h i `U32.rem` a.store_len) in
  let r =
    match vopt with
    | None -> return None
    | Some (i', v) ->
      if i = i'
      then begin
        seq_to_map_ith h s a.default_v (U32.v (h i `U32.rem` a.store_len));
        return (Some v)
      end
      else return None in
  let s = A.intro_varray_pts_to a.store in
  intro_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m);
  intro_exists (G.reveal s) (store_contents_pred a m);
  intro_pure (Some? r ==> r == Some (Map.sel m i));
  return r

let rec seq_to_map_domain (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v) (x:k)
  : Lemma
      (ensures
        seq_to_map s default_v `Map.contains` x ==>
        (exists (i:nat{i < Seq.length s}). Some? (Seq.index s i) /\ fst (Some?.v (Seq.index s i)) == x))
      (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else seq_to_map_domain (Seq.tail s) default_v x

let rec seq_to_map_upd_aux (#k:eqtype) (#v:Type0) h (s:Seq.seq (option (k & v))) (default_v:v)
  (i:nat{i < Seq.length s}) (x:k) (y:v)
  : Lemma
      (requires
        seq_props_derived h s /\
        seq_props_derived h (Seq.upd s i (Some (x, y))))
      (ensures
        seq_to_map (Seq.upd s i (Some (x, y))) default_v `submap_of`
        Map.upd (seq_to_map s default_v) x y)
      (decreases i)
  = if i = 0 then begin
      match Seq.head s with
      | None -> ()
      | Some (x', _) -> seq_to_map_domain (Seq.tail s) default_v x'
    end
    else begin
      seq_to_map_upd_aux h (Seq.tail s) default_v (i-1) x y;
      match Seq.head s with
      | None -> ()
      | Some (x', y') ->
        assert (Seq.index (Seq.upd s i (Some (x, y))) 0 == Some (x', y'));
        assert (Seq.index (Seq.upd s i (Some (x, y))) i == Some (x, y));
        assert (x =!= x')
    end

let seq_to_map_upd (#k:eqtype) (#v:Type0) h (s:Seq.seq (option (k & v))) (default_v:v)
  (m:Map.t k v)
  (i:nat{i < Seq.length s}) (x:k) (y:v)
  : Lemma
      (requires
        seq_props_derived h s /\
        seq_props_derived h (Seq.upd s i (Some (x, y))) /\
        seq_to_map s default_v `submap_of` m)
      (ensures
        seq_to_map (Seq.upd s i (Some (x, y))) default_v `submap_of` Map.upd m x y)
  = seq_to_map_upd_aux h s default_v i x y
            
let upd #k #v #h #m a i x =
  let s = witness_exists () in
  A.elim_varray_pts_to a.store s;
  elim_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m);
  A.upd a.store (h i `U32.rem` a.store_len) (Some (i, x));
  ghost_write_pt a.g_repr (Map.upd m i x);
  assert (seq_props #k #v h (Seq.upd s (U32.v (h i `U32.rem` a.store_len)) (Some (i, x))));
  seq_to_map_upd #k #v h s a.default_v m (U32.v (h i `U32.rem` a.store_len)) i x;
  let s = A.intro_varray_pts_to a.store in
  intro_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` Map.upd m i x);
  intro_exists (G.reveal s) (store_contents_pred a (Map.upd m i x))
