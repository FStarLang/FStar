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
/// The hashing scheme we use is as follows:
///   for key `k`, its slot in the array is `(h k) mod n`

noeq
type tbl #k #v #contents (vp:vp_t k v contents) (h:hash_fn k) = {
  store_len    : n:u32{U32.v n > 0};
  store        : A.array (option (k & v));
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
  (#v:Type0)
  (#contents:Type)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  : prop
  = forall (i:nat{i < Seq.length s}).
      match Seq.index s i with
      | None -> True
      | Some (k, _) -> Map.contains k m

/// For each (Some (k, v)) in the sequence,
///   either borrows does not contain k, or it maps k to v

let store_and_borrows_related
  (#k:eqtype)
  (#v:Type0)
  (s:Seq.seq (option (k & v)))
  (borrows:Map.t k v)
  : prop
  = forall (i:nat{i < Seq.length s}).
      match Seq.index s i with
      | None -> True
      | Some (k, x) ->
        Map.sel k borrows == None \/
        Map.sel k borrows == Some x

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
  (#v:Type0)
  (#contents:Type)
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
  (#v:Type0)
  (#contents:Type)
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
  (#v:Type0)
  (#contents:Type)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : vprop
  = SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m borrows)

let pure_invariant
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (arr:tbl vp h)
  (m:repr k contents)
  (borrows:Map.t k v)
  (s:Seq.seq (option (k & v)))
  : prop
  = seq_props h s /\
    store_and_repr_related s m /\
    store_and_borrows_related s borrows

/// The main invariant is defined as an existential for the store sequence

[@@__reduce__]
let store_contents_pred
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (arr:tbl vp h)
  (m:repr k contents)
  (borrows:Map.t k v)
  : Seq.seq (option (k & v)) -> vprop
  = fun s ->
    A.pts_to arr.store full_perm s
      `star`
    GR.pts_to arr.g_repr full_perm m
      `star`
    GR.pts_to arr.g_borrows full_perm borrows
      `star`
    pure (pure_invariant arr m borrows s)
      `star`
    value_vprops vp s m borrows

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
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  (a:tbl vp h)
  : STGhost unit opened
      (A.pts_to a.store full_perm s
         `star`
       GR.pts_to a.g_repr full_perm m
         `star`
       GR.pts_to a.g_borrows full_perm borrows
         `star`
       value_vprops vp s m borrows)
      (fun _ -> tperm a m borrows)
      (requires pure_invariant a m borrows s)
      (ensures fun _ -> True)
  = intro_pure (pure_invariant a m borrows s);
    intro_exists s (store_contents_pred a m borrows)

let create #k #v #contents vp h n =
  let store = A.alloc #(option (k & v)) None n in
  let g_repr = GR.alloc (G.hide (Map.empty k contents)) in
  let g_borrows = GR.alloc (G.hide (Map.empty k v)) in
  let arr : tbl #k #v #contents vp h = {
    store_len = n;
    store = store;
    g_repr = g_repr;
    g_borrows = g_borrows;
    store_len_pf = () } in

  //
  //rewrite in terms of projections from the arr record
  //
  rewrite (A.pts_to store _ (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           GR.pts_to g_repr full_perm (Map.empty k contents)
             `star`
           GR.pts_to g_borrows full_perm (Map.empty k v))
          (A.pts_to arr.store _ (Seq.create #(option (k & v)) (U32.v n) None)
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
             arr;

  return arr

/// Similar to create, except that the repr map is a const map

let create_v #k #v #contents vp h n c =
  let store = A.alloc #(option (k & v)) None n in
  let g_repr = GR.alloc (G.hide (Map.const k (G.reveal c))) in
  let g_borrows = GR.alloc (G.hide (Map.empty k v)) in
  let arr : tbl #k #v #contents vp h = {
    store_len = n;
    store = store;
    g_repr = g_repr;
    g_borrows = g_borrows;
    store_len_pf = () } in

  //
  //rewrite in terms of projections from the arr record
  //
  rewrite (A.pts_to store _ (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           GR.pts_to g_repr full_perm (Map.const k (G.reveal c))
             `star`
           GR.pts_to g_borrows full_perm (Map.empty k v))
          (A.pts_to arr.store _ (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           GR.pts_to arr.g_repr full_perm (Map.const k (G.reveal c))
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
                         (Map.const k (G.reveal c))
                         (Map.empty k v));
  rewrite_equiv emp (value_vprops vp (Seq.create (U32.v n) None)
                                     (Map.const k (G.reveal c))
                                     (Map.empty k v));

  pack_tperm (Seq.create (U32.v n) None)
             (Map.const k (G.reveal c))
             (Map.empty k v)
             arr;

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

/// This is one of the workhorses of this library
///
/// It splits value vprops for a store sequence into `star` of value vprops for subsequences
///
/// Since `get`, `put`, `with_key` manipulate one entry at a time,
///   we split the sequence at that i (prefix, at i, suffix)

let value_vprops_split3
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
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
///   in all the API (`get`, `put`, `ghost_put`, `remove`), the action happens at (at i)
///
/// The value vprops for prefix and suffix remain same
///
/// We have lemmas for each of the functions to prove that
///
/// The lemmas prove equality of value vprops before and after
///   what each of the functions do to the arrays and maps


let value_vprops_prefix_suffix_get
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
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
  (#v:Type0)
  (#contents:Type)
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

let value_vprops_prefix_suffix_remove
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (h:hash_fn k)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)){seq_props h s})
  (m:repr k contents)
  (borrows:Map.t k v)
  (idx:nat)
  (i:k{U32.v (h i) `UInt.mod` Seq.length s == idx})
  : Lemma (requires Some? (Seq.index s idx))
          (ensures (let s1 = Seq.upd s idx None in
                    value_vprops vp (seq_until s idx) m borrows ==
                    value_vprops vp (seq_until s1 idx) m (Map.remove i borrows) /\
                    value_vprops vp (seq_from s idx) m borrows ==
                    value_vprops vp (seq_from s1 idx) m (Map.remove i borrows)))
  = let s1 = Seq.upd s idx None in
    let borrows1 = Map.remove i borrows in
    assert (Seq.equal (value_vprops_seq vp (seq_until s idx) m borrows)
                      (value_vprops_seq vp (seq_until s1 idx) m borrows1));
    assert (Seq.equal (value_vprops_seq vp (seq_from s idx) m borrows)
                      (value_vprops_seq vp (seq_from s1 idx) m borrows1))


/// A common utility that we use in all APIs
///
/// It first splits the value vprops intro (prefix, at i, suffix)
///
/// Then, given a vprop p, such that vprop seq at i is proven to be p by the client,
///   it rewrites the (at i) part with p

let unpack_value_vprops (#opened:_)
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
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
  (#v:Type0)
  (#contents:Type)
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
  (#v:Type0)
  (#contents:Type)
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

let get #k #v #contents #vp #h #m #borrows a i =
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows s);
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in
  let vopt = A.read a.store idx in
  let r = match vopt with
          | None -> Absent
          | Some (i', x) ->
            if i <> i' then Missing i'
            else Present x in
  (match vopt with
   | None ->  //Nothing at the slot, return Absent
     pack_tperm s m borrows a;
     rewrite (tperm a m borrows) (get_post m borrows a i r)
   | Some (i', x) ->
     if i <> i'
     then begin  //A different key, return Missing
       intro_pure (map_contains_prop i' m);
       pack_tperm s m borrows a;
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

       GR.write a.g_borrows (Map.upd i x borrows);

       pack_tperm s m (Map.upd i x borrows) a;

       rewrite (tperm a m (Map.upd i x borrows)
                 `star`
                vp i x (Some?.v (Map.sel i m)))
               (get_post m borrows a i r)
     end);
     return r


/// `put` helper, `put` writes to the ghost and concrete state
///   and calls it to establish the invariant

let put_vprops_aux (#opened:_)
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (arr:tbl vp h)
  (m:repr k contents)
  (borrows:Map.t k v)
  (s:Seq.seq (option (k & v)))
  (i:k)
  (x:v)
  (c:contents)
  (idx:U32.t)
  (_:squash (Seq.length s == A.length arr.store /\ idx == h i `U32.rem` arr.store_len))
  : STGhost unit opened
      (A.pts_to arr.store full_perm (Seq.upd s (U32.v idx) (Some (i, x)))
         `star`
       GR.pts_to arr.g_repr full_perm (Map.upd i c m)
         `star`
       GR.pts_to arr.g_borrows full_perm (Map.remove i borrows)
         `star`
       value_vprops vp s m borrows
         `star`
       vp i x c)
      (fun _ -> tperm arr (Map.upd i c m) (Map.remove i borrows))
      (requires pure_invariant arr m borrows s)
      (ensures fun _ -> True)
  = let vopt = Seq.index s (U32.v idx) in
    match vopt with
    | None ->
      //
      //The sequence slot earlier was None, meaning no entry
      //
      //This means there was nothing in the value vprops
      //
      //Unpack value vprops with emp at i
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
        arr
  
   | Some (i', x') ->

     //
     //The sequence slot was set earlier
     //
     //Whether we have the corresponding vp permission depends on the borrows entry
     //

     let bopt = Map.sel i' borrows in
     match bopt with
     | None ->

       //
       //borrows does not contains i;
       //
       //unpack with (vp ...) at i' and pack with (vp ...) at i
       //
       //note that both i and i' map to the same slot
       //

       unpack_value_vprops vp s m borrows idx (vp i' x' (Some?.v (Map.sel i' m)));
       drop (vp i' x' (Some?.v (Map.sel i' m)));

       value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
       rewrite_value_vprops_prefix_and_suffix vp
         s (Seq.upd s (U32.v idx) (Some (i, x)))
         m (Map.upd i c m)
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
         (Map.upd i c m)
         (Map.remove i borrows)
         arr

     | _ ->

       //
       //borrow contains i', so we unpack with emp and pack with (vp ...)
       //

       unpack_value_vprops vp s m borrows idx emp;

       value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
       rewrite_value_vprops_prefix_and_suffix vp
         s (Seq.upd s (U32.v idx) (Some (i, x)))
         m (Map.upd i c m)
         borrows (Map.remove i borrows)
         idx;

       pack_value_vprops vp
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i c m)
         (Map.remove i borrows)
         idx
         (vp i x c);

       pack_tperm
         (Seq.upd s (U32.v idx) (Some (i, x)))
         (Map.upd i c m)
         (Map.remove i borrows)
         arr

/// `put`

let put #k #v #contents #vp #h #m #borrows a i x c =
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows s);
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in

  A.write a.store idx (Some (i, x));
  GR.write a.g_repr (Map.upd i (G.reveal c) m);
  GR.write a.g_borrows (Map.remove i borrows);

  put_vprops_aux a m borrows s i x c idx ()

/// `ghost_put`

let ghost_put #_ #k #v #contents #vp #h #m #borrows a i x c =
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows s);
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in

  GR.write a.g_repr (Map.upd i (G.reveal c) m);
  GR.write a.g_borrows (Map.remove i borrows);

  //reestablish the invariant

  let vopt = Seq.index s (U32.v idx) in
  match vopt returns STGhostT _
                              _
                              _
                              (fun _ -> tperm a (Map.upd i (G.reveal c) m) (Map.remove i borrows)) with
  | None ->
    //
    //The sequence slot was not set
    //
    //So we can't keep the input vp permission, drop it
    //
    drop (vp i x c);
    assert (Seq.equal (value_vprops_seq vp s m borrows)
                      (value_vprops_seq vp s (Map.upd i (G.reveal c) m) (Map.remove i borrows)));
    rewrite (value_vprops vp s m borrows)
            (value_vprops vp s (Map.upd i (G.reveal c) m) (Map.remove i borrows));
    pack_tperm s (Map.upd i (G.reveal c) m) (Map.remove i borrows) a
  | Some (i', _) ->
    let b = i' <> i in
    if b returns STGhostT _
                          _
                          _
                          (fun _ -> tperm a (Map.upd i (G.reveal c) m) (Map.remove i borrows))
    then begin
      //
      //The sequence slot is set, but contains a different key
      //
      //Again, drop the input vp
      //
      drop (vp i x c);
      assert (Seq.equal (value_vprops_seq vp s m borrows)
                        (value_vprops_seq vp s (Map.upd i (G.reveal c) m) (Map.remove i borrows)));
      rewrite (value_vprops vp s m borrows)
              (value_vprops vp s (Map.upd i (G.reveal c) m) (Map.remove i borrows));
      pack_tperm s (Map.upd i (G.reveal c) m) (Map.remove i borrows) a
    end
    else begin
      //
      //The sequence slot is set and contains the same key
      //
      //We also know that borrows contains the key (the precondition)
      //
      //So, unpack with emp and pack with vp at i
      unpack_value_vprops vp s m borrows idx emp;

      value_vprops_prefix_suffix_put h vp s m borrows (U32.v idx) i x c;
      rewrite_value_vprops_prefix_and_suffix vp
        s s
        m (Map.upd i (G.reveal c) m)
        borrows (Map.remove i borrows)
        idx;

      pack_value_vprops vp
        s
        (Map.upd i (G.reveal c) m)
        (Map.remove i borrows)
        idx
        (vp i x c);

      pack_tperm
        s
        (Map.upd i (G.reveal c) m)
        (Map.remove i borrows)
        a
    end


/// `remove` helper to reestablish the invariant

let remove_vprops_aux (#opened:_)
  (#k:eqtype)
  (#v:Type0)
  (#contents:Type)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (arr:tbl vp h)
  (m:repr k contents)
  (borrows:Map.t k v)
  (s:Seq.seq (option (k & v)))
  (i:k)
  (idx:U32.t)
  (_:squash (Seq.length s == A.length arr.store /\ idx == h i `U32.rem` arr.store_len))
  : STGhost unit opened
      (A.pts_to arr.store full_perm (Seq.upd s (U32.v idx) None)
         `star`
       GR.pts_to arr.g_repr full_perm m
         `star`
       GR.pts_to arr.g_borrows full_perm (Map.remove i borrows)
         `star`
       value_vprops vp s m borrows)
      (fun _ -> tperm arr m (Map.remove i borrows))
      (requires pure_invariant arr m borrows s)
      (ensures fun _ -> True)
  = let vopt = Seq.index s (U32.v idx) in
    match vopt returns STGhostT _ _ _ (fun _ -> tperm arr m (Map.remove i borrows)) with
    | None ->
      //
      //The sequence slot was already None
      //
      //Just rewrite, since we did not have any vp
      //
      assert (Seq.equal s (Seq.upd s (U32.v idx) None));
      assert (Seq.equal (value_vprops_seq vp s m borrows)
                        (value_vprops_seq vp s m (Map.remove i borrows)));
      rewrite (value_vprops vp s m borrows)
              (value_vprops vp (Seq.upd s (U32.v idx) None) m (Map.remove i borrows));
      pack_tperm (Seq.upd s (U32.v idx) None) m (Map.remove i borrows) arr
    | Some (i', x') ->
      //
      //The sequence slot was set
      //
      //Whether or not we had vp depends on the membership of i' in borrows
      //
      let r = Map.contains i' borrows in
      match r returns STGhostT _ _ _ (fun _ -> tperm arr m (Map.remove i borrows)) with
      | true ->
        //
        //Again, no vp, since borrows contains i', rewrite
        //
        assert (Seq.equal (value_vprops_seq vp s m borrows)
                          (value_vprops_seq vp (Seq.upd s (U32.v idx) None) m (Map.remove i borrows)));
        rewrite (value_vprops vp s m borrows)
                (value_vprops vp (Seq.upd s (U32.v idx) None) m (Map.remove i borrows));
        pack_tperm (Seq.upd s (U32.v idx) None) m (Map.remove i borrows) arr
      | _ ->
        //
        //borrows did not have i'
        //
        //unpack with vp at i', pack with emp (we know that i and i' map to idx)
        //
        unpack_value_vprops vp s m borrows idx (vp i' x' (Some?.v (Map.sel i' m)));
        drop (vp i' x' (Some?.v (Map.sel i' m)));

        value_vprops_prefix_suffix_remove h vp s m borrows (U32.v idx) i;
        rewrite_value_vprops_prefix_and_suffix vp
          s (Seq.upd s (U32.v idx) None)
          m m
          borrows (Map.remove i borrows)
          idx;
        pack_value_vprops vp
          (Seq.upd s (U32.v idx) None)
          m
          (Map.remove i borrows)
          idx
          emp;
        pack_tperm (Seq.upd s (U32.v idx) None) m (Map.remove i borrows) arr

/// `remove`

let remove #k #v #contents #vp #h #m #borrows a i =
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows s);
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in

  A.write a.store idx None;
  GR.write a.g_borrows (Map.remove i borrows);
  remove_vprops_aux a m borrows s i idx ()

/// `free`

let free #k #v #contents #vp #h #m #borrows a =
  let s = elim_exists () in
  elim_pure (pure_invariant a m borrows s);
  A.pts_to_length a.store s;
  (intro_exists (G.reveal s) (A.pts_to a.store full_perm);
   A.free a.store);
  GR.free a.g_repr;
  GR.free a.g_borrows;
  drop _
