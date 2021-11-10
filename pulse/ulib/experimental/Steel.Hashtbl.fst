(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi
*)


module Steel.Hashtbl

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

/// We implement the table using an array of length n as the store,
///
/// The elements of the array are (k, v) pairs in the hashtable
///
/// For a key k, we would compute the index in the array as ((h k) % store.len)
///
/// We will then lookup the index, if it is Some (k', _) then k' == k implies that the key k is present
///   in the table
///
/// We also maintain a ghost reference to store the logical map view of the hashtable

noeq
type tbl k v (h:hash_fn k) = {
  store_len    : n:u32{U32.v n > 0};
  store        : A.array (option (k & v));
  g_repr       : ghost_ref (Map.t k v);
  default_v    : G.erased v;
  store_len_pf : squash (A.length store == U32.v store_len);
}


/// The underlying sequence representation of the hashtable store has
///   the following properties:
///
/// - Its length is bounded by u32
/// - For a Some (k, _) entry at index i, (h k % len == i)

let seq_props (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v))) : prop =  
  0 < Seq.length s /\ UInt.size (Seq.length s) 32 /\
  
  (forall (i:nat{i < Seq.length s}). Some? (Seq.index s i) ==> (let Some (x, _) = Seq.index s i in
                                                         U32.v (h x) `UInt.mod` Seq.length s == i))


/// Given seq_props, we can prove that all the keys in the sequence are distinct
///
/// Sometimes in the proofs, it is easier to directly use the uniqueness property,
///   rather than the seq_props

let seq_keys_distinct (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) : prop =
  forall (i j:(k:nat{k < Seq.length s})).{:pattern Seq.index s i; Seq.index s j}
    (i =!= j /\ Some? (Seq.index s i) /\ Some? (Seq.index s j)) ==>
    (fst (Some?.v (Seq.index s i)) =!= fst (Some?.v (Seq.index s j)))


/// We can easily prove the distinctness property given seq_props

let seq_props_implies_seq_keys_distinct (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v)))
  : Lemma (requires seq_props h s) (ensures seq_keys_distinct s)
  = ()


/// We now relate the store to the logical map
///
/// We first define a function to convert the sequence to a map
///
/// Later, we will maintain an invariant that the map obtained by applying this function
///   to the store is a submap of the logical map

let rec seq_to_map (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v)
  : GTot (repr k v) (decreases Seq.length s)
  = if Seq.length s = 0
    then empty_repr default_v
    else let hd, tl = Seq.head s, Seq.tail s in
         let m = seq_to_map tl default_v in
         match hd with
         | None -> m
         | Some (x, y) -> Map.upd m x y

let submap_of (#k:eqtype) (#v:Type0) (m1 m2:Map.t k v) : prop =
  let open FStar.Map in
  forall (x:k). m1 `contains` x ==> (m2 `contains` x /\ m1 `sel` x == m2 `sel` x)


/// The main separation logic assertion
///
/// Maintains the permission to the store and the ghost reference,
///   and a pure proposition to relate the two

[@@__reduce__]
let store_contents_pred (#k:eqtype) (#v:Type0) (#h:hash_fn k) (arr:tbl k v h) (m:repr k v)
  : Seq.lseq (option (k & v)) (A.length arr.store) -> vprop
  = fun s ->
    A.varray_pts_to arr.store s
      `star`
    ghost_pts_to arr.g_repr full_perm m
      `star`
    pure (seq_props h s /\ seq_to_map s arr.default_v `submap_of` m)

[@@__reduce__]
let tpts_to arr m = h_exists (store_contents_pred arr m)


/// Some pure lemmas for a few properties of the store and logical map


let rec seq_to_map_create (k:eqtype) (#v:Type0) (n:nat) (default_v:v)
  : Lemma (Map.equal (seq_to_map (Seq.create n None) default_v)
                     (empty_repr #k #v default_v))
  = if n = 0 then ()
    else begin
      assert (Seq.equal #(option (k & v)) (Seq.tail (Seq.create n None))
                                          (Seq.create (n-1) None));
      seq_to_map_create k (n-1) default_v
    end


/// The ith entry in the sequence, if it is Some (x, y) then in the corresponding map x |-> v
///
/// Note that this needs that the keys in the sequence are distinct

let rec seq_to_map_ith (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v)
  (i:nat{i < Seq.length s})
  : Lemma
      (requires
        seq_keys_distinct s /\
        Some? (Seq.index s i))
      (ensures (let open Map in
                let Some (x, y) = Seq.index s i in
                let m = seq_to_map s default_v in
                m `contains` x /\
                m `sel` x == y))
      (decreases i)
  = if i = 0 then () else seq_to_map_ith (Seq.tail s) default_v (i-1)


/// The domain of the seq_to_map map is strictly the entries in the sequence

let rec seq_to_map_domain (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v) (x:k)
  : Lemma
      (ensures
        seq_to_map s default_v `Map.contains` x ==>  //if x is in the seq_to_map map,
        (exists (i:nat{i < Seq.length s}).
           Some? (Seq.index s i) /\
           fst (Some?.v (Seq.index s i)) == x))  //then it must be in the sequence
      (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else seq_to_map_domain (Seq.tail s) default_v x


/// Commutation of seq_to_map with Seq.upd
///
/// It requires the keys distinctness property in the original and updated sequence

let rec seq_to_map_upd (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (default_v:v)
  (i:nat{i < Seq.length s})
  (x:k) (y:v)
  : Lemma
      (requires
        seq_keys_distinct s /\
        seq_keys_distinct (Seq.upd s i (Some (x, y))))
      (ensures
        seq_to_map (Seq.upd s i (Some (x, y))) default_v `submap_of`
        Map.upd (seq_to_map s default_v) x y)
      (decreases i)
  = let m = seq_to_map s default_v in
    let s1 = Seq.upd s i (Some (x, y)) in
    let m1 = seq_to_map s1 default_v in

    //To prove: m1 `submap_of` Map.upd m x y

    if i = 0 then begin
      let m_tl = seq_to_map (Seq.tail s) default_v in
      match Seq.head s with
      | None ->
        assert (m == m_tl);
        assert (m1 == Map.upd m_tl x y);
        assert (m1 == Map.upd m x y)  //and submap_of is reflexive
      | Some (x', y') ->
        assert (m == Map.upd m_tl x' y');
        assert (m1 == Map.upd m_tl x y);
        //
        //We need to prove:
        //  Map.upd m_tl x y `submap_of` Map.upd (Map.upd m_tl x' y') x y
        //
        //Note that this would not be the case if m_tl `Map.contains` x'
        //  since if it does, then it could be the case that m_tl[x'] = y'',
        //  whereas its mapping on the right hand side is y'
        //
        //But we are in luck, we can prove that x' \notin m_tl
        //
        //And we prove it by appealing to the fact that a key in the seq_to_map map
        //  must be present in the sequence
        //
        //Conversely, if a key is not in the sequence, then it is not in the map
        //
        seq_to_map_domain (Seq.tail s) default_v x';
        assert (m1 `submap_of` Map.upd m x y)
    end
    else begin
      seq_to_map_upd (Seq.tail s) default_v (i-1) x y;
      //Induction hypothesis
      assert (seq_to_map (Seq.upd (Seq.tail s) (i-1) (Some (x, y))) default_v `submap_of`
              Map.upd (seq_to_map (Seq.tail s) default_v) x y);
      match Seq.head s with
      | None ->
        assert (m == seq_to_map (Seq.tail s) default_v);
        assert (m1 == seq_to_map (Seq.upd (Seq.tail s) (i-1) (Some (x, y))) default_v);
        assert (m1 `submap_of` Map.upd m x y)  //directly from Induction hypothesis
      | Some (x', y') ->
        assert (m == Map.upd (seq_to_map (Seq.tail s) default_v) x' y');
        assert (m1 == Map.upd (seq_to_map (Seq.upd (Seq.tail s) (i-1) (Some (x, y))) default_v) x' y');
        //
        //Apply Map.upd (...) x' y' to both the sides of `submap_of` in the Induction hypothesis
        //
        assert (Map.upd (seq_to_map (Seq.upd (Seq.tail s) (i-1) (Some (x, y))) default_v) x' y' `submap_of`
                Map.upd (Map.upd (seq_to_map (Seq.tail s) default_v) x y) x' y');
        //
        //i.e.
        //
        assert (m1 `submap_of` Map.upd (Map.upd (seq_to_map (Seq.tail s) default_v) x y) x' y');

        //
        //We want the right side to be Map.upd (Map.upd (seq_to_map (Seq.tail s) default_v) x' y') x y
        //
        //We get there by proving that x' =!= x, and then the two updates can be commuted
        //
        //To get that x' =!= x, we appeal to the fact that
        //  in the updated sequence the keys are distinct and i =!= 0
        //

        assert (Seq.index (Seq.upd s i (Some (x, y))) 0 == Some (x', y'));
        assert (Seq.index (Seq.upd s i (Some (x, y))) i == Some (x, y));
        assert (x =!= x');
        assert (Map.equal (Map.upd (Map.upd (seq_to_map (Seq.tail s) default_v) x y) x' y')
                          (Map.upd (Map.upd (seq_to_map (Seq.tail s) default_v) x' y') x y))        
    end


/// The main stateful API

let create #k #v h x n =
  let store = A.malloc None n in
  let g_ref = ghost_alloc_pt (empty_repr (G.reveal x)) in
  let arr = {
    store_len = n;
    store = store;
    g_repr = g_ref;
    default_v = x;
    store_len_pf = () } in
  let s = A.intro_varray_pts_to arr.store in
  seq_to_map_create k (U32.v n) (G.reveal x);
  intro_pure (seq_props h s /\ submap_of (seq_to_map s arr.default_v) (empty_repr (G.reveal x)));
  assert_spinoff (ghost_pts_to g_ref full_perm (empty_repr (G.reveal x)) ==
                  ghost_pts_to arr.g_repr full_perm (empty_repr (G.reveal x)));
  change_equal_slprop (ghost_pts_to g_ref full_perm (empty_repr (G.reveal x)))
                      (ghost_pts_to arr.g_repr full_perm (empty_repr (G.reveal x)));
  intro_exists (G.reveal s) (store_contents_pred arr (empty_repr (G.reveal x)));
  return arr

let get #k #v #h #m a i =
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
        seq_to_map_ith s a.default_v (U32.v (h i `U32.rem` a.store_len));
        return (Some v)
      end
      else return None in
  let s = A.intro_varray_pts_to a.store in
  intro_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m);
  intro_exists (G.reveal s) (store_contents_pred a m);
  return r

let put #k #v #h #m a i x =
  let s = witness_exists () in
  A.elim_varray_pts_to a.store s;
  elim_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m);
  A.upd a.store (h i `U32.rem` a.store_len) (Some (i, x));
  ghost_write_pt a.g_repr (Map.upd m i x);
  assert (seq_props #k #v h (Seq.upd s (U32.v (h i `U32.rem` a.store_len)) (Some (i, x))));
  seq_to_map_upd #k #v s a.default_v (U32.v (h i `U32.rem` a.store_len)) i x;
  let s = A.intro_varray_pts_to a.store in
  intro_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` Map.upd m i x);
  intro_exists (G.reveal s) (store_contents_pred a (Map.upd m i x))

let free #k #v #h #m a =
  let s = witness_exists () in
  A.elim_varray_pts_to a.store s;
  ghost_free_pt a.g_repr;
  A.free a.store;
  elim_pure (seq_props h s /\ seq_to_map s a.default_v `submap_of` m)
