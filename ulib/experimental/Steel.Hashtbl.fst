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
open Steel.ST.Effect.Ghost
open Steel.ST.Effect.Atomic
open Steel.ST.Effect
open Steel.ST.Util

module G = FStar.Ghost
module Seq = FStar.Seq
module Map = FStar.PartialMap
module U32 = FStar.UInt32
module R = Steel.ST.GhostReference
module A = Steel.ST.Array

#set-options "--ide_id_info_off --print_implicits"

noeq
type tbl #k #v #contents (#vp:vp_t k v contents) (h:hash_fn k) (finalizer:finalizer_t vp) = {
  store_len    : n:u32{U32.v n > 0};
  store        : A.array (option (k & v));
  g_repr       : R.ref (Map.t k contents);
  g_borrows    : R.ref (Map.t k v);
  store_len_pf : squash (A.length store == U32.v store_len);
}

let seq_props (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v))) : prop =  
  0 < Seq.length s /\ UInt.size (Seq.length s) 32 /\
  
  (forall (i:nat{i < Seq.length s}).
     Some? (Seq.index s i) ==> (let Some (x, _) = Seq.index s i in
                                U32.v (h x) `UInt.mod` Seq.length s == i))

let seq_keys_distinct (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) : prop =
  forall (i j:(k:nat{k < Seq.length s})).{:pattern Seq.index s i; Seq.index s j}
    (i =!= j /\ Some? (Seq.index s i) /\ Some? (Seq.index s j)) ==>
    (fst (Some?.v (Seq.index s i)) =!= fst (Some?.v (Seq.index s j)))

let seq_props_implies_seq_keys_distinct (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v)))
  : Lemma (requires seq_props h s) (ensures seq_keys_distinct s)
  = ()

let store_and_repr_related
  (#k:eqtype)
  (#v #contents:Type0)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  : prop
  = forall (i:nat{i < Seq.length s}).
      match Seq.index s i with
      | None -> True
      | Some (k, _) -> Map.contains k m

let store_and_borrows_related
  (#k:eqtype)
  (#v:Type0)
  (s:Seq.seq (option (k & v)))
  (borrows:Map.t k v)
  : prop
  = forall (x:k). Map.contains x borrows ==>
             (exists (i:nat{i < Seq.length s}) (y:v).
                Seq.index s i == Some (x, y) /\
                Map.sel x borrows == Some y)

assume val seq_map (#a #b:Type) (f:a -> b) (s:Seq.seq a) : Seq.seq b

module CE = FStar.Algebra.CommMonoid.Equiv
module SeqPerm = FStar.Seq.Permutation

let star_eq : CE.equiv vprop =
  CE.EQ equiv (fun _ -> admit ()) (fun _ _ -> admit ()) (fun _ _ _ -> admit ())

let vprop_monoid : CE.cm vprop star_eq =
  CE.CM emp star (fun _ -> admit ()) (fun _ _ _ -> admit ()) (fun _ _ -> admit ()) (fun _ _ _ _ -> admit ())

let value_vprops_mapping_fn
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (m:repr k contents)
  (borrows:Map.t k v)
  : option (k & v) -> vprop
  = fun e ->
    match e with
    | None -> emp
    | Some (i, x) ->
      (match Map.sel i m, Map.sel i borrows with
       | None, _ -> pure False
       | _, Some _ -> emp
       | Some c, None -> vp i x c)

let value_vprops_seq
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : Seq.seq vprop
  = seq_map (value_vprops_mapping_fn vp m borrows) s

let value_vprops
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : vprop
  = SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m borrows)

[@@__reduce__]
let store_contents_pred
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (arr:tbl h finalizer)
  (m:repr k contents)
  (borrows:Map.t k v)
  : Seq.seq (option (k & v)) -> vprop
  = fun s ->
    A.pts_to arr.store s
      `star`
    R.pts_to arr.g_repr full_perm m
      `star`
    R.pts_to arr.g_borrows full_perm borrows
      `star`
    pure (seq_props h s /\
          store_and_repr_related s m /\
          store_and_borrows_related s borrows)
      `star`
    value_vprops vp s m borrows

[@@__reduce__]
let tperm arr m borrows = exists_ (store_contents_pred arr m borrows)


assume val admit__ (#opened:_) (#a:Type) (#p:pre_t) (#q:post_t a) (_:unit)
  : STAtomicF a opened p q True (fun _ -> False)

let create #k #v #contents #vp h finalizer n = admit__ ()

assume val rewrite_equiv (#opened:_) (p q:vprop)
  : STGhost unit opened p (fun _ -> q) (requires equiv p q) (ensures fun _ -> True)

assume val seq_map_len (#a #b:Type) (f:a -> b) (s:Seq.seq a)
  : Lemma (ensures Seq.length (seq_map f s) == Seq.length s)
          [SMTPat (Seq.length (seq_map f s))]

let get #k #v #contents #vp #h #finalizer #m #borrows a i =
  let s = elim_exists () in  
  elim_pure (seq_props h s /\
             store_and_repr_related s m /\
             store_and_borrows_related s borrows);
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in
  let vopt = A.read a.store idx in
  let r = match vopt with
          | None -> Absent
          | Some (i', x) ->
            if i <> i' then Missing i'
            else Present x in
  (match vopt returns STT unit _ (fun _ -> get_post m borrows a i r) with
   | None ->
     intro_pure (seq_props h s /\
                 store_and_repr_related s m /\
                 store_and_borrows_related s borrows);
     intro_exists (G.reveal s) (store_contents_pred a m borrows);
     rewrite (tperm a m borrows) (get_post m borrows a i r)
   | Some (i', x) ->
     if i <> i'
     then begin
       intro_pure (map_contains_prop i' m);
       intro_pure (seq_props h s /\
                   store_and_repr_related s m /\
                   store_and_borrows_related s borrows);
       intro_exists (G.reveal s) (store_contents_pred a m borrows);
       rewrite (tperm a m borrows
                  `star`
                pure (map_contains_prop i' m))
               (get_post m borrows a i r)
     end
     else begin
       let vs0 = value_vprops_seq vp s m borrows in
       let vs0_prefix = Seq.slice vs0 0 (U32.v idx) in
       let vs0_idx = Seq.create 1 (Seq.index vs0 (U32.v idx)) in
       let vs0_suffix = Seq.slice vs0 (U32.v idx + 1) (Seq.length vs0) in
       assert (Seq.equal vs0
                         (Seq.append vs0_prefix
                                     (Seq.append vs0_idx vs0_suffix)));
       SeqPerm.foldm_snoc_append vprop_monoid vs0_prefix
                                              (Seq.append vs0_idx vs0_suffix);
       SeqPerm.foldm_snoc_append vprop_monoid vs0_idx vs0_prefix;
       assume (equiv (SeqPerm.foldm_snoc vprop_monoid vs0)
                     (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                        `star`
                      (SeqPerm.foldm_snoc vprop_monoid vs0_idx
                         `star`
                       SeqPerm.foldm_snoc vprop_monoid vs0_suffix)));

       rewrite_equiv (SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m borrows))
                     (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                        `star`
                      (SeqPerm.foldm_snoc vprop_monoid vs0_idx
                         `star`
                       SeqPerm.foldm_snoc vprop_monoid vs0_suffix));

       let upd_borrows = Map.upd i x borrows in

       let vs1 = value_vprops_seq vp s m upd_borrows in
       let vs1_prefix = Seq.slice vs1 0 (U32.v idx) in
       let vs1_idx = Seq.create 1 (Seq.index vs1 (U32.v idx)) in
       let vs1_suffix = Seq.slice vs1 (U32.v idx + 1) (Seq.length vs1) in

       assert (Seq.equal vs1
                         (Seq.append vs1_prefix
                                     (Seq.append vs1_idx vs1_suffix)));

       SeqPerm.foldm_snoc_append vprop_monoid vs1_prefix
                                              (Seq.append vs1_idx vs1_suffix);
       SeqPerm.foldm_snoc_append vprop_monoid vs1_idx vs1_prefix;
       assume (equiv (SeqPerm.foldm_snoc vprop_monoid vs1)
                     (SeqPerm.foldm_snoc vprop_monoid vs1_prefix
                        `star`
                      (SeqPerm.foldm_snoc vprop_monoid vs1_idx
                         `star`
                       SeqPerm.foldm_snoc vprop_monoid vs1_suffix)));
       assume (Seq.index vs1 (U32.v idx) == emp);
       assume (SeqPerm.foldm_snoc vprop_monoid vs1_idx == emp);
       assume (equiv (SeqPerm.foldm_snoc vprop_monoid vs1)
                     (SeqPerm.foldm_snoc vprop_monoid vs1_prefix
                        `star`
                      SeqPerm.foldm_snoc vprop_monoid vs1_suffix));

       assume (Seq.equal vs0_prefix vs1_prefix /\
               Seq.equal vs0_suffix vs1_suffix);

       rewrite (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                  `star`
                SeqPerm.foldm_snoc vprop_monoid vs0_suffix)
               (SeqPerm.foldm_snoc vprop_monoid vs1_prefix
                  `star`
                SeqPerm.foldm_snoc vprop_monoid vs1_suffix);

       rewrite_equiv (SeqPerm.foldm_snoc vprop_monoid vs1_prefix
                        `star`
                      SeqPerm.foldm_snoc vprop_monoid vs1_suffix)
                     (SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m (Map.upd i x borrows)));

       let Some c = Map.sel i m in
       assume (Seq.index vs0 (U32.v idx) == vp i x c);
       assume (equiv (SeqPerm.foldm_snoc vprop_monoid vs0_idx) (vp i x c));
       rewrite_equiv (SeqPerm.foldm_snoc vprop_monoid vs0_idx) (vp i x c);
       R.write a.g_borrows (Map.upd i x borrows);
       intro_pure (seq_props h s /\
                   store_and_repr_related s m /\
                   store_and_borrows_related s (Map.upd i x borrows));
       intro_exists (G.reveal s) (store_contents_pred a m (Map.upd i x borrows));
       rewrite (tperm a m (Map.upd i x borrows)
                  `star`
                vp i x c)
               (get_post m borrows a i r)
     end);

  return r

let rec seq_to_map_create (k:eqtype) (v:Type0) (n:nat)
  : Lemma (Map.equal (seq_to_map (Seq.create n None))
                     (Map.empty k v))
  = if n = 0 then ()
    else begin
      assert (Seq.equal #(option (k & v)) (Seq.tail (Seq.create n None))
                                          (Seq.create (n-1) None));
      seq_to_map_create k v (n-1)
    end

let rec seq_to_map_ith (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (i:nat{i < Seq.length s})
  : Lemma
      (requires
        seq_keys_distinct s /\
        Some? (Seq.index s i))
      (ensures (let open Map in
                let Some (x, y) = Seq.index s i in
                let m = seq_to_map s in
                contains x m /\
                sel x m == Some y))
      (decreases i)
  = if i = 0 then () else seq_to_map_ith (Seq.tail s) (i-1)

let rec seq_to_map_domain (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) (x:k)
  : Lemma
      (ensures
        Map.contains x (seq_to_map s) ==>  //if x is in the seq_to_map map,
        (exists (i:nat{i < Seq.length s}).
           Some? (Seq.index s i) /\
           fst (Some?.v (Seq.index s i)) == x))  //then it must be in the sequence
      (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else seq_to_map_domain (Seq.tail s) x

let rec seq_to_map_upd (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v)))
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
