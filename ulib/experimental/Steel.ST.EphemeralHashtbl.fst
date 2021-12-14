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

module Steel.ST.EphemeralHashtbl

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
module R = Steel.ST.Reference
module GR = Steel.ST.GhostReference
module A = Steel.ST.Array
module BV = Steel.ST.BitVector


/// `store` is the concrete store implemented as an array
///
/// `bv_borrows` is a bitvector, if the key in the cell `i` of the store is borrowed,
///   the `ith` bit in `bv_borrows` is set
///
/// The hashing scheme we use is as follows:
///   for key `k`, its slot in the array is `(h k) mod n`

noeq
type tbl #k #v #contents (#vp:vp_t k v contents) (h:hash_fn k) (finalizer:finalizer_t vp) = {
  store_len    : n:u32{U32.v n > 0};
  store        : A.array (option (k & v));
  bv_borrows   : BV.bv_t store_len;
  g_repr       : GR.ref (Map.t k contents);
  g_borrows    : GR.ref (Map.t k v);
  store_len_pf : squash (A.length store == U32.v store_len);
}


/// Property of the logical view of the store
///
/// For each (Some (k, v)) in the sequence, (h k) mod n == i

let seq_props (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v))) : prop =  
  0 < Seq.length s /\ UInt.size (Seq.length s) 32 /\
  
  (forall (i:nat{i < Seq.length s}).
     Some? (Seq.index s i) ==> (let Some (x, _) = Seq.index s i in
                                U32.v (h x) `UInt.mod` Seq.length s == i))

/// Using seq_props, we can derive that all the keys in the sequence are distinct

let seq_keys_distinct (#k:eqtype) (#v:Type0) (s:Seq.seq (option (k & v))) : prop =
  forall (i j:(k:nat{k < Seq.length s})).{:pattern Seq.index s i; Seq.index s j}
    (i =!= j /\ Some? (Seq.index s i) /\ Some? (Seq.index s j)) ==>
    (fst (Some?.v (Seq.index s i)) =!= fst (Some?.v (Seq.index s j)))

let seq_props_implies_keys_distinct (#k:eqtype) (#v:Type0) (h:hash_fn k) (s:Seq.seq (option (k & v)))
  : Lemma (requires seq_props h s) (ensures seq_keys_distinct s)
  = ()

/// For each (Some (k, v)) in the sequence, k must be in the repr map

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

/// Relation between the store, the bitvector, and the borrows map

let store_and_bv_and_borrows_related
  (#k:eqtype)
  (#v:Type0)
  (bv:BV.repr)
  (s:Seq.seq (option (k & v)))
  (borrows:Map.t k v)
  : prop
  = forall (i:nat{i < Seq.length s /\ i < Seq.length bv}).
      match Seq.index s i with
      | None -> ~ (Seq.index bv i)
      | Some (x, y) ->
        if Seq.index bv i
        then Map.sel x borrows == Some y
        else ~ (Map.contains x borrows)

module CE = FStar.Algebra.CommMonoid.Equiv
module SeqPerm = FStar.Seq.Permutation


/// Setup for maintaining the value vprops in the table invariant
///
/// High-level idea is that, we take the store sequence,
///   map it to a sequence of vprops,
///   and fold the vprop monoid (with `star` as the multiplication) on this sequence
///
/// Each value contributes a `vp i x c`, unless it is in the borrows map

let vprop_monoid : CE.cm vprop Steel.Effect.Common.req = Steel.Effect.Common.rm

/// Function to map over the store sequence

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

/// The corresponding sequence of vprops for a store sequence

[@@__reduce__]
let value_vprops_seq
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : Seq.seq vprop
  = Seq.map_seq (value_vprops_mapping_fn vp m borrows) s

/// Value vprops

[@@__reduce__]
let value_vprops
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : vprop
  = SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m borrows)

let pure_invariant
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (arr:tbl h finalizer)
  (m:repr k contents)
  (borrows:Map.t k v)
  (bv:BV.repr)
  (s:Seq.seq (option (k & v)))
  : prop
  = seq_props h s /\
    store_and_repr_related s m /\
    store_and_bv_and_borrows_related bv s borrows

/// The main invariant is defined as two existentials,
///   one for the store, and one for the bitvector

[@@__reduce__]
let store_contents_pred_seq
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (arr:tbl h finalizer)
  (m:repr k contents)
  (borrows:Map.t k v)
  (bv:BV.repr)
  : Seq.seq (option (k & v)) -> vprop
  = fun s ->
    A.pts_to arr.store full_perm s
      `star`
    GR.pts_to arr.g_repr full_perm m
      `star`
    GR.pts_to arr.g_borrows full_perm borrows
      `star`
    pure (pure_invariant arr m borrows bv s)
      `star`
    value_vprops vp s m borrows

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
  : BV.repr -> vprop
  = fun bv ->
    BV.pts_to arr.bv_borrows full_perm bv
      `star`
    exists_ (store_contents_pred_seq arr m borrows bv)


/// Main invariant

[@@__reduce__]
let tperm arr m borrows = exists_ (store_contents_pred arr m borrows)


/// map_seq lemmas, with smt pats on them

let map_seq_len (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a)
  : Lemma (ensures Seq.length (Seq.map_seq f s) == Seq.length s)
          [SMTPat (Seq.length (Seq.map_seq f s))]
  = Seq.map_seq_len f s

let map_seq_index (#a #b:Type) (f:a -> Tot b) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : Lemma (ensures Seq.index (Seq.map_seq f s) i == f (Seq.index s i))
          [SMTPat (Seq.index (Seq.map_seq f s) i)]
  = Seq.map_seq_index f s i

let map_seq_append (#a #b:Type) (f:a -> Tot b) (s1 s2:Seq.seq a)
  : Lemma (ensures (Seq.map_seq f (Seq.append s1 s2) ==
                    Seq.append (Seq.map_seq f s1) (Seq.map_seq f s2)))
          [SMTPat (Seq.map_seq f (Seq.append s1 s2))]
  = Seq.map_seq_append f s1 s2


/// Helper function to pack a tperm assertion

let pack_tperm (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  (a:tbl h finalizer)
  (bv:BV.repr)
  : STGhost unit opened
      (A.pts_to a.store full_perm s
         `star`
       GR.pts_to a.g_repr full_perm m
         `star`
       GR.pts_to a.g_borrows full_perm borrows
         `star`
       value_vprops vp s m borrows
         `star`
       BV.pts_to a.bv_borrows full_perm bv)
      (fun _ -> tperm a m borrows)
      (requires pure_invariant a m borrows bv s)
      (ensures fun _ -> True)
  = intro_pure (pure_invariant a m borrows bv s);
    intro_exists s (store_contents_pred_seq a m borrows bv);
    intro_exists bv (store_contents_pred a m borrows)

let create #k #v #contents #vp h finalizer n =
  let store = A.alloc #(option (k & v)) None n in
  let bv_borrows = BV.alloc n in
  let g_repr = GR.alloc (G.hide (Map.empty k contents)) in
  let g_borrows = GR.alloc (G.hide (Map.empty k v)) in
  let arr : tbl #k #v #contents #vp h finalizer = {
    store_len = n;
    store = store;
    bv_borrows = bv_borrows;
    g_repr = g_repr;
    g_borrows = g_borrows;
    store_len_pf = () } in
  
  rewrite (A.pts_to store _ (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           BV.pts_to bv_borrows _ (Seq.create (U32.v n) false)
             `star`
           GR.pts_to g_repr full_perm (Map.empty k contents)
             `star`
           GR.pts_to g_borrows full_perm (Map.empty k v))
          (A.pts_to arr.store _ (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           BV.pts_to arr.bv_borrows _ (Seq.create (U32.v n) false)
             `star`
           GR.pts_to arr.g_repr full_perm (Map.empty k contents)
             `star`
           GR.pts_to arr.g_borrows full_perm (Map.empty k v));

  //
  //The value vprops at this point are all emp
  //
  //A lemma that tells us that folding a monoid over a sequence of units
  //  is monoid-equivalent to the unit
  //
  SeqPerm.foldm_snoc_unit_seq
    vprop_monoid
    (value_vprops_seq vp (Seq.create (U32.v n) None)
                         (Map.empty k contents)
                         (Map.empty k v));
  rewrite_equiv emp (value_vprops vp (Seq.create (U32.v n) None)
                                     (Map.empty k contents)
                                     (Map.empty k v));

  pack_tperm (Seq.create (U32.v n) None)
             (Map.empty k contents)
             (Map.empty k v)
             arr
             (Seq.create (U32.v n) false);

  return arr

/// Makes it easy to write subsequences

let seq_until (#a:Type) (s:Seq.seq a) (idx:nat{idx < Seq.length s})
  : Seq.seq a
  = Seq.slice s 0 idx

let seq_at (#a:Type) (s:Seq.seq a) (idx:nat{idx < Seq.length s})
  : Seq.seq a
  = Seq.create 1 (Seq.index s idx)

let seq_from (#a:Type) (s:Seq.seq a) (idx:nat{idx < Seq.length s})
  : Seq.seq a
  = Seq.slice s (idx + 1) (Seq.length s)

let elim_equiv_laws ()
  : Lemma (
          (forall x. x `equiv` x) /\
          (forall x y. x `equiv` y ==> y `equiv` x) /\
          (forall x y z. (x `equiv` y /\ y `equiv` z) ==> x `equiv` z)
          )
  = let open Steel.Effect.Common in
    assert (req.eq == equiv);
    CE.elim_eq_laws req

/// This is one of the workhorse of this library
///
/// It splits value vprops for a store sequence into `star` of value vprops for subsequences
///
/// Since `get`, `put`, `with_key` manipualte one entry at a time,
///   we split the sequence at that i (prefix, at i, suffix)

let value_vprops_split3
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:Map.t k contents)
  (borrows:Map.t k v)
  (i:nat{i < Seq.length s})
  : Lemma (value_vprops vp s m borrows
             `equiv`
           (value_vprops vp (seq_until s i) m borrows
              `star`
            value_vprops vp (seq_at s i) m borrows
              `star`
            value_vprops vp (seq_from s i) m borrows))
  = elim_equiv_laws ();
    Classical.forall_intro_3 star_associative;

    assert (Seq.equal s (Seq.append (seq_until s i)
                                    (Seq.append (seq_at s i) (seq_from s i))));
    let vps s = value_vprops_seq vp s m borrows in
    
    calc (equiv) {
      value_vprops vp s m borrows;
      (equiv) { }
      value_vprops vp (Seq.append (seq_until s i)
                                  (Seq.append (seq_at s i) (seq_from s i))) m borrows;
      (equiv) { SeqPerm.foldm_snoc_append vprop_monoid
                  (vps (seq_until s i))
                  (Seq.append
                     (vps (seq_at s i))
                     (vps (seq_from s i))) }
      value_vprops vp (seq_until s i) m borrows
        `star`
      value_vprops vp (Seq.append (seq_at s i) (seq_from s i)) m borrows;
      (equiv) { SeqPerm.foldm_snoc_append vprop_monoid
                  (vps (seq_at s i))
                  (vps (seq_from s i));
                star_congruence
                  (value_vprops vp (seq_until s i) m borrows)
                  (value_vprops vp (Seq.append (seq_at s i) (seq_from s i)) m borrows)
                  (value_vprops vp (seq_until s i) m borrows)
                  (value_vprops vp (seq_at s i) m borrows `star` value_vprops vp (seq_from s i) m borrows) }
      value_vprops vp (seq_until s i) m borrows
        `star`
      (value_vprops vp (seq_at s i) m borrows
         `star`
       value_vprops vp (seq_from s i) m borrows);
    }

/// Once we have split value vprops into (prefix, at i, suffix),
///   in all the three (`get`, `put`, `with_key`), the action happens at (at i)
///
/// The value vprops for prefix and suffix remain same
///
/// We have three lemmas, one for each of the functions to prove that
///
/// The lemmas prove equality of value vprops before and after
///   what each of the functions do to the arrays and maps


let value_vprops_prefix_suffix_get
  (#k:eqtype)
  (#v #contents:Type0)
  (h:hash_fn k)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  (idx:nat{idx < Seq.length s})
  : Lemma (requires Some? (Seq.index s idx) /\
                    seq_props h s)
          (ensures (let Some (i, x) = Seq.index s idx in
                    let upd_borrows = Map.upd i x borrows in
                    value_vprops vp (seq_until s idx) m borrows ==
                    value_vprops vp (seq_until s idx) m upd_borrows /\
                    value_vprops vp (seq_from s idx) m borrows ==
                    value_vprops vp (seq_from s idx) m upd_borrows))
  = let Some (i, x) = Seq.index s idx in
    let upd_borrows = Map.upd i x borrows in
    assert (Seq.equal (value_vprops_seq vp (seq_until s idx) m borrows)
                      (value_vprops_seq vp (seq_until s idx) m upd_borrows));
    assert (Seq.equal (value_vprops_seq vp (seq_from s idx) m borrows)
                      (value_vprops_seq vp (seq_from s idx) m upd_borrows))

let value_vprops_prefix_suffix_put
  (#k:eqtype)
  (#v #contents:Type0)
  (h:hash_fn k)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  (idx:nat{idx < Seq.length s})
  (x:k) (y:v) (c:G.erased contents)
  : Lemma (requires seq_props h s /\
                    seq_props h (Seq.upd s idx (Some (x, y))))
          (ensures (let s1 = Seq.upd s idx (Some (x, y)) in
                    let m1 = Map.upd x (G.reveal c) m in
                    let borrows1 = Map.remove x borrows in
                    value_vprops vp (seq_until s idx) m borrows ==
                    value_vprops vp (seq_until s1 idx) m1 borrows1 /\
                    value_vprops vp (seq_from s idx) m borrows ==
                    value_vprops vp (seq_from s1 idx) m1 borrows1))
  = let s1 = Seq.upd s idx (Some (x, y)) in
    let m1 = Map.upd x (G.reveal c) m in
    let borrows1 = Map.remove x borrows in
    assert (Seq.index s1 idx == Some (x, y));
    assert (Seq.equal (value_vprops_seq vp (seq_until s idx) m borrows)
                      (value_vprops_seq vp (seq_until s1 idx) m1 borrows1));
    assert (Seq.equal (value_vprops_seq vp (seq_from s idx) m borrows)
                      (value_vprops_seq vp (seq_from s1 idx) m1 borrows1))

let value_vprops_prefix_suffix_with_key
  (#k:eqtype)
  (#v #contents:Type0)
  (h:hash_fn k)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  (idx:nat{idx < Seq.length s})
  (c:G.erased contents)
  : Lemma (requires Some? (Seq.index s idx) /\
                    seq_props h s)
          (ensures (let Some (i, _) = Seq.index s idx in
                    let m1 = Map.upd i (G.reveal c) m in
                    value_vprops vp (seq_until s idx) m borrows ==
                    value_vprops vp (seq_until s idx) m1 borrows /\
                    value_vprops vp (seq_from s idx) m borrows ==
                    value_vprops vp (seq_from s idx) m1 borrows))
  = let Some (i, _) = Seq.index s idx in
    let m1 = Map.upd i (G.reveal c) m in
    assert (Seq.equal (value_vprops_seq vp (seq_until s idx) m borrows)
                      (value_vprops_seq vp (seq_until s idx) m1 borrows));
    assert (Seq.equal (value_vprops_seq vp (seq_from s idx) m borrows)
                      (value_vprops_seq vp (seq_from s idx) m1 borrows))

/// A common utility that we use in all APIs
///
/// It first splits the value vprops intro (prefix, at i, suffix)
///
/// Then, given a vprop p, such that vprop seq at i is proven to be p by the client,
///   it rewrites the (at i) part with p

let unpack_value_vprops (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:Map.t k contents)
  (borrows:Map.t k v)
  (idx:U32.t{U32.v idx < Seq.length s})
  (p:vprop)
  : STGhost unit opened
      (value_vprops vp s m borrows)
      (fun _ ->
       value_vprops vp (seq_until s (U32.v idx)) m borrows
         `star`
       p
         `star`
       value_vprops vp (seq_from s (U32.v idx)) m borrows)
      (requires Seq.index (value_vprops_seq vp s m borrows) (U32.v idx) == p)
      (ensures fun _ -> True)
  = value_vprops_split3 vp s m borrows (U32.v idx);
    rewrite_equiv _
      (value_vprops vp (seq_until s (U32.v idx)) m borrows
         `star`
       value_vprops vp (seq_at s (U32.v idx)) m borrows
         `star`
       value_vprops vp (seq_from s (U32.v idx)) m borrows);
    SeqPerm.foldm_snoc_singleton vprop_monoid p;
    assert (Seq.equal (value_vprops_seq vp (Seq.create 1 (Seq.index s (U32.v idx))) m borrows)
                      (Seq.create 1 p));
    rewrite_equiv (value_vprops vp (seq_at s (U32.v idx)) m borrows) p

/// A wrapper over two rewrites
///  (used to rewrite the prefix and suffix parts of value vprops)

let rewrite_value_vprops_prefix_and_suffix (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s1 s2:Seq.seq (option (k & v)))
  (m1 m2:Map.t k contents)
  (borrows1 borrows2:Map.t k v)
  (idx:U32.t{Seq.length s1 == Seq.length s2 /\ U32.v idx < Seq.length s1})
  : STGhost unit opened
      (value_vprops vp (seq_until s1 (U32.v idx)) m1 borrows1
         `star`
       value_vprops vp (seq_from s1 (U32.v idx)) m1 borrows1)
      (fun _ ->
       value_vprops vp (seq_until s2 (U32.v idx)) m2 borrows2
         `star`
       value_vprops vp (seq_from s2 (U32.v idx)) m2 borrows2)
      (requires value_vprops vp (seq_until s1 (U32.v idx)) m1 borrows1 ==
                value_vprops vp (seq_until s2 (U32.v idx)) m2 borrows2 /\
                value_vprops vp (seq_from s1 (U32.v idx)) m1 borrows1 ==
                value_vprops vp (seq_from s2 (U32.v idx)) m2 borrows2)
      (ensures fun _ -> True)
  = rewrite
      (value_vprops vp (seq_until s1 (U32.v idx)) m1 borrows1
         `star`
       value_vprops vp (seq_from s1 (U32.v idx)) m1 borrows1)
      (value_vprops vp (seq_until s2 (U32.v idx)) m2 borrows2
         `star`
       value_vprops vp (seq_from s2 (U32.v idx)) m2 borrows2)


/// The opposite direction of unpack_value_vprops

let pack_value_vprops (#opened:_)
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:Map.t k contents)
  (borrows:Map.t k v)
  (idx:U32.t{U32.v idx < Seq.length s})
  (p:vprop)
  : STGhost unit opened
      (value_vprops vp (seq_until s (U32.v idx)) m borrows
         `star`
       p
         `star`
       value_vprops vp (seq_from s (U32.v idx)) m borrows)
      (fun _ -> value_vprops vp s m borrows)
      (requires Seq.index (value_vprops_seq vp s m borrows) (U32.v idx) == p)
      (ensures fun _ -> True)
  = SeqPerm.foldm_snoc_singleton vprop_monoid p;
    assert (Seq.equal (value_vprops_seq vp (Seq.create 1 (Seq.index s (U32.v idx))) m borrows)
                      (Seq.create 1 p));
    rewrite_equiv p (value_vprops vp (seq_at s (U32.v idx)) m borrows);
    value_vprops_split3 vp s m borrows (U32.v idx);
    rewrite_equiv
      (value_vprops vp (seq_until s (U32.v idx)) m borrows
         `star`
       value_vprops vp (seq_at s (U32.v idx)) m borrows
         `star`
       value_vprops vp (seq_from s (U32.v idx)) m borrows)
      (value_vprops vp s m borrows)

/// `get`

let get #k #v #contents #vp #h #finalizer #m #borrows a i =
  let bv = elim_exists () in
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows bv s);
  A.pts_to_length a.store s;
  BV.pts_to_length a.bv_borrows bv;
  let idx = h i `U32.rem` a.store_len in
  let vopt = A.read a.store idx in
  let r = match vopt with
          | None -> Absent
          | Some (i', x) ->
            if i <> i' then Missing i'
            else Present x in
  (match vopt with
   | None ->  //Nothing at the slot, return Absent
     pack_tperm s m borrows a bv;
     rewrite (tperm a m borrows) (get_post m borrows a i r)
   | Some (i', x) ->
     if i <> i'
     then begin  //A different key, return Missing
       intro_pure (map_contains_prop i' m);
       pack_tperm s m borrows a bv;
       rewrite (tperm a m borrows
                  `star`
                pure (map_contains_prop i' m))
               (get_post m borrows a i r)
     end
     else begin
       //
       //Unpack value vprops to get (vp i x c)
       //
       //Rewrite prefix and suffix
       //
       //Rewrite (at i) with empty
       //
       //Pack value vprops
       //
       unpack_value_vprops vp s m borrows idx (vp i x (Some?.v (Map.sel i m)));

       value_vprops_prefix_suffix_get h vp s m borrows (U32.v idx);
       rewrite_value_vprops_prefix_and_suffix vp s s m m
         borrows (Map.upd i x borrows) idx;

       pack_value_vprops vp s m (Map.upd i x borrows) idx emp;

       BV.bv_set a.bv_borrows idx;

       GR.write a.g_borrows (Map.upd i x borrows);

       pack_tperm s m (Map.upd i x borrows) a (Seq.upd bv (U32.v idx) true);

       rewrite (tperm a m (Map.upd i x borrows)
                 `star`
                vp i x (Some?.v (Map.sel i m)))
               (get_post m borrows a i r)
     end);
     return r

/// `put`

let put #k #v #contents #vp #h #finalizer #m #borrows a i x c =
  let bv = elim_exists () in
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows bv s);
  A.pts_to_length a.store s;
  BV.pts_to_length a.bv_borrows bv;
  let idx = h i `U32.rem` a.store_len in
  let vopt = A.read a.store idx in

  A.write a.store idx (Some (i, x));
  GR.write a.g_repr (Map.upd i (G.reveal c) m);
  GR.write a.g_borrows (Map.remove i borrows);

  (match vopt with
   | None ->
     //
     //Unpack value vprops
     //
     //Rewrite prefix and suffix
     //
     //Rewrite (at i) with (vp i x c)
     //
     //Pack value vprops
     //
     unpack_value_vprops vp s m borrows idx emp;

     value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
     rewrite_value_vprops_prefix_and_suffix vp
       s (Seq.upd s (U32.v idx) (Some (i, x)))
       m (Map.upd i (G.reveal c) m)
       borrows (Map.remove i borrows)
       idx;

     pack_value_vprops vp
       (Seq.upd s (U32.v idx) (Some (i, x)))
       (Map.upd i (G.reveal c) m)
       (Map.remove i borrows)
       idx
       (vp i x c);

     pack_tperm
       (Seq.upd s (U32.v idx) (Some (i, x)))
       (Map.upd i (G.reveal c) m)
       (Map.remove i borrows)
       a
       bv
   | Some (i', x') ->
     let b = BV.bv_is_set a.bv_borrows idx in
     if b
     then begin
       //Since the bv is set, we don't have (vp i x c),
       //so unpack with emp, and pack with the new (vp i x c)
       BV.bv_unset a.bv_borrows idx;
       
       unpack_value_vprops vp s m borrows idx emp;

       value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
       rewrite_value_vprops_prefix_and_suffix vp
         s (Seq.upd s (U32.v idx) (Some (i, x)))
         m (Map.upd i (G.reveal c) m)
         borrows (Map.remove i borrows)
         idx;

       pack_value_vprops vp
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i (G.reveal c) m)
         (Map.remove i borrows)
         idx
         (vp i x c);

       pack_tperm
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i (G.reveal c) m)
         (Map.remove i borrows)
         a
         (Seq.upd bv (U32.v idx) false)
     end
     else begin
       //
       //Unpack with older (vp i x c)
       //
       //Call the finalizer
       //
       //Pack with the new (vp i x c)
       //
       unpack_value_vprops vp s m borrows idx (vp i' x' (Some?.v (Map.sel i' m)));
       intro_exists (Some?.v (Map.sel i' m)) (vp i' x');
       finalizer i' x';

       value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
       rewrite_value_vprops_prefix_and_suffix vp
         s (Seq.upd s (U32.v idx) (Some (i, x)))
         m (Map.upd i (G.reveal c) m)
         borrows (Map.remove i borrows)
         idx;

       pack_value_vprops vp
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i (G.reveal c) m)
         (Map.remove i borrows)
         idx
         (vp i x c);

       pack_tperm
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i (G.reveal c) m)
         (Map.remove i borrows)
         a
         bv
     end)

/// `with_key`

let with_key #k #v #contents #vp #h #finalizer #m #borrows a i #f_pre #f_post $f =
  let bv = elim_exists () in
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows bv s);
  A.pts_to_length a.store s;
  BV.pts_to_length a.bv_borrows bv;

  let idx = h i `U32.rem` a.store_len in
  let vopt = A.read a.store idx in

  match vopt returns STT (get_result k (G.erased contents)) _ (with_key_post m borrows a i f_pre f_post) with
  | None ->  //Nothing in the slot, return Absent
    pack_tperm s m borrows a bv;
    rewrite_with_tactic
      (f_pre `star` tperm a m borrows)
      (tperm a m borrows `star` f_pre);
    let r = Absent in
    rewrite (tperm a m borrows `star` f_pre) (with_key_post m borrows a i f_pre f_post r);
    return r
  | Some (i', x) ->
    if i' = i then begin
      //Unpack with (vp i x c)
      //Call f
      //Pack with (vp i x c'), where f returns c'
      unpack_value_vprops vp s m borrows idx (vp i x (Some?.v (Map.sel i m)));

      let c = f x (Some?.v (Map.sel i m)) in

      value_vprops_prefix_suffix_with_key h vp s m borrows (U32.v idx) c;
      rewrite_value_vprops_prefix_and_suffix vp s s
        m (Map.upd i (G.reveal c) m)
        borrows borrows idx;

      pack_value_vprops vp s (Map.upd i (G.reveal c) m) borrows idx (vp i x (G.reveal c));

      GR.write a.g_repr (Map.upd i (G.reveal c) m);
      pack_tperm s (Map.upd i (G.reveal c) m) borrows a bv;
      rewrite_with_tactic
        (f_post (Some?.v (Map.sel i m)) c `star` tperm a (Map.upd i (G.reveal c) m) borrows)
        (tperm a (Map.upd i (G.reveal c) m) borrows `star` f_post (Some?.v (Map.sel i m)) c);
      let r = Present c in
      rewrite
        (tperm a (Map.upd i (G.reveal c) m) borrows `star` f_post (Some?.v (Map.sel i m)) c)
        (with_key_post m borrows a i f_pre f_post r);
      return r
    end
    else begin  //A different key in the slot, return (Missing i')
      intro_pure (map_contains_prop i' m);
      pack_tperm s m borrows a bv;
      rewrite_with_tactic  //AC reasoning
        (f_pre `star` (pure (map_contains_prop i' m) `star` tperm a m borrows))
        (tperm a m borrows `star` f_pre `star` pure (map_contains_prop i' m));
      let r = Missing i' in
      rewrite
        (tperm a m borrows `star` f_pre `star` pure (map_contains_prop i' m))
        (with_key_post m borrows a i f_pre f_post r);
      return r
    end


/// A utility function to iterate over the array and finalize the values
///
/// The induction is over an `s_ind` that starts being same as `s`,
///   but each finalized entry is set to None in `s_ind`
///
/// So then, the value vprops are specified using s_ind

let rec finalize_values
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#s:G.erased (Seq.seq (option (k & v))))
  (#m:G.erased (repr k contents))
  (#bv:G.erased BV.repr)
  (a:tbl h finalizer)
  (borrows:G.erased (Map.t k v))
  (i:U32.t{U32.v a.store_len = Seq.length s /\ U32.v i <= U32.v a.store_len})
  (s_ind:G.erased (Seq.seq (option (k & v))))
  : ST unit (A.pts_to a.store full_perm s
               `star`
             BV.pts_to a.bv_borrows full_perm bv
               `star`
             value_vprops vp s_ind m borrows)
            (fun _ -> A.pts_to a.store full_perm s
                     `star`
                   BV.pts_to a.bv_borrows full_perm bv)
            (requires store_and_repr_related s m /\
                      store_and_bv_and_borrows_related bv s borrows /\
                      Seq.length s == Seq.length s_ind /\
                      (forall (j:nat{j < U32.v i}). Seq.index s_ind j == None) /\
                      (forall (j:nat{U32.v i <= j /\ j < Seq.length s}).
                         Seq.index s_ind j == Seq.index s j))
            (ensures fun _ -> True)
                        
  = A.pts_to_length a.store s;
    BV.pts_to_length a.bv_borrows bv;
    if i = a.store_len
    then begin  //Done
      SeqPerm.foldm_snoc_unit_seq vprop_monoid (value_vprops_seq vp s_ind m borrows);
      rewrite_equiv (value_vprops vp s_ind m borrows) emp
    end
    else begin
      let vopt = A.read a.store i in
      match vopt with
      | None -> finalize_values a borrows (U32.add i 1ul) s_ind  //Move on
      | Some (i', x) ->
        let b = BV.bv_is_set a.bv_borrows i in
        if b
        then begin  //This entry is borrowed, we don't have permission
          unpack_value_vprops vp s_ind m borrows i emp;

          rewrite_value_vprops_prefix_and_suffix vp
            s_ind (Seq.upd s_ind (U32.v i) None)
            m m borrows borrows i;

          pack_value_vprops vp (Seq.upd s_ind (U32.v i) None) m borrows i emp;
          finalize_values a borrows (U32.add i 1ul) (Seq.upd s_ind (U32.v i) None)
        end
        else begin  //finalize, set s_ind at idx to None, and iterate
          unpack_value_vprops vp s_ind m borrows i (vp i' x (Some?.v (Map.sel i' m)));

          intro_exists (Some?.v (Map.sel i' m)) (vp i' x);
          finalizer i' x;

          rewrite_value_vprops_prefix_and_suffix vp
            s_ind (Seq.upd s_ind (U32.v i) None)
            m m borrows borrows i;

          pack_value_vprops vp (Seq.upd s_ind (U32.v i) None) m borrows i emp;
          finalize_values a borrows (U32.add i 1ul) (Seq.upd s_ind (U32.v i) None)
        end
    end

/// `free`

let free #k #v #contents #vp #h #finalizer m borrows a =
  let bv = elim_exists () in
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows bv s);
  A.pts_to_length a.store s;
  finalize_values a borrows 0ul s;
  intro_exists (G.reveal s) (A.pts_to a.store full_perm);
  A.free a.store;
  BV.free a.bv_borrows;
  GR.free a.g_repr;
  GR.free a.g_borrows
