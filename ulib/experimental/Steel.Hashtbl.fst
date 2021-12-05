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

[@@__reduce__]
let value_vprops_seq
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:repr k contents)
  (borrows:Map.t k v)
  : Seq.seq vprop
  = Seq.seq_map (value_vprops_mapping_fn vp m borrows) s

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

assume val foldm_snoc_unit_seq (#a:Type) (#eq:_) (m:CE.cm a eq) (s:Seq.seq a)
  : Lemma (requires forall (i:nat{i < Seq.length s}). Seq.index s i == m.unit)
          (ensures eq.eq m.unit (SeqPerm.foldm_snoc m s))

assume val rewrite_equiv (#opened:_) (p q:vprop)
  : STGhost unit opened p (fun _ -> q) (requires equiv p q \/ equiv q p) (ensures fun _ -> True)

let create #k #v #contents #vp h finalizer n =
  let store = A.alloc #(option (k & v)) None n in
  let g_repr = R.alloc (G.hide (Map.empty k contents)) in
  let g_borrows = R.alloc (G.hide (Map.empty k v)) in
  let arr : tbl #k #v #contents #vp h finalizer = {
    store_len = n;
    store = store;
    g_repr = g_repr;
    g_borrows = g_borrows;
    store_len_pf = () } in
  rewrite (A.pts_to store (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           R.pts_to g_repr full_perm (Map.empty k contents)
             `star`
           R.pts_to g_borrows full_perm (Map.empty k v))
          (A.pts_to arr.store (Seq.create #(option (k & v)) (U32.v n) None)
             `star`
           R.pts_to arr.g_repr full_perm (Map.empty k contents)
             `star`
           R.pts_to arr.g_borrows full_perm (Map.empty k v));
  foldm_snoc_unit_seq
    vprop_monoid
    (value_vprops_seq vp (Seq.create #(option (k & v)) (U32.v n) None)
                         (Map.empty k contents)
                         (Map.empty k v));
  rewrite_equiv emp (value_vprops vp (Seq.create #(option (k & v)) (U32.v n) None)
                                     (Map.empty k contents)
                                     (Map.empty k v));
  intro_pure (seq_props h (Seq.create #(option (k & v)) (U32.v n) None) /\
              store_and_repr_related (Seq.create #(option (k & v)) (U32.v n) None) (Map.empty k contents) /\
              store_and_borrows_related (Seq.create #(option (k & v)) (U32.v n) None) (Map.empty k v));  
  intro_exists (Seq.create #(option (k & v)) (U32.v n) None)
               (store_contents_pred arr (Map.empty k contents) (Map.empty k v));
  return arr

let star_equiv (p q r:vprop)
  : Lemma (requires q `equiv` r)
          (ensures (p `star` q) `equiv` (p `star` r))
  = equiv_refl p;
    star_congruence p q p r

let value_vprop_seq_upd_borrows
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
                    let s0 = value_vprops_seq vp s m borrows in
                    let s1 = value_vprops_seq vp s m (Map.upd i x borrows) in
                    Seq.equal (Seq.slice s0 0 idx)
                              (Seq.slice s1 0 idx) /\
                    Seq.equal (Seq.slice s0 (idx+1) (Seq.length s))
                              (Seq.slice s1 (idx+1) (Seq.length s))))
  = ()

let seq_split3 (#a:Type) (s:Seq.seq a) (i:nat{i < Seq.length s})
  : (s':(Seq.seq a & Seq.seq a & Seq.seq a){
     let s1, s2, s3 = s' in
     Seq.equal s (Seq.append s1 (Seq.append s2 s3))})
  = Seq.slice s 0 i,
    Seq.create 1 (Seq.index s i),
    Seq.slice s (i+1) (Seq.length s)

let foldm_snoc_split3 (s s1 s2 s3:Seq.seq vprop)
  : Lemma (requires Seq.equal s (Seq.append s1 (Seq.append s2 s3)))
          (ensures SeqPerm.foldm_snoc vprop_monoid s
                     `equiv`
                   (SeqPerm.foldm_snoc vprop_monoid s1
                      `star`
                    (SeqPerm.foldm_snoc vprop_monoid s2
                       `star`
                     SeqPerm.foldm_snoc vprop_monoid s3)))
  = SeqPerm.foldm_snoc_append vprop_monoid s1 (Seq.append s2 s3);
    SeqPerm.foldm_snoc_append vprop_monoid s2 s3;
    star_equiv (SeqPerm.foldm_snoc vprop_monoid s1)
               (SeqPerm.foldm_snoc vprop_monoid (Seq.append s2 s3))
               (SeqPerm.foldm_snoc vprop_monoid s2
                  `star`
                SeqPerm.foldm_snoc vprop_monoid s3);
    equiv_trans (SeqPerm.foldm_snoc vprop_monoid s)
                (SeqPerm.foldm_snoc vprop_monoid s1
                   `star`
                 (SeqPerm.foldm_snoc vprop_monoid (Seq.append s2 s3)))
                (SeqPerm.foldm_snoc vprop_monoid s1
                   `star`
                 (SeqPerm.foldm_snoc vprop_monoid s2
                    `star`
                  SeqPerm.foldm_snoc vprop_monoid s3))

let equiv_helper_q_emp (p q r:vprop)
  : Lemma (requires q `equiv` emp)
          (ensures (p `star` (q `star` r)) `equiv` (p `star` r))
  = equiv_refl r;
    star_congruence q r emp r;
    equiv_refl p;
    star_congruence p (q `star` r) p (emp `star` r);
    cm_identity r;
    star_congruence p (emp `star` r) p r;
    equiv_trans (p `star` (q `star` r))
                (p `star` (emp `star` r))
                (p `star` r)

#push-options "--warn_error -271"
let get #k #v #contents #vp #h #finalizer #m #borrows a i =
  let equiv_trans (p q r:vprop)
    : Lemma (requires p `equiv` q /\ q `equiv` r)
            (ensures p `equiv` r)
            [SMTPat ()]
    = equiv_trans p q r in
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
  (match vopt returns STGhostT unit Set.empty _ (fun _ -> get_post m borrows a i r) with
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
       let vs0_prefix, vs0_idx, vs0_suffix = seq_split3 vs0 (U32.v idx) in
       foldm_snoc_split3 vs0 vs0_prefix vs0_idx vs0_suffix;
       rewrite_equiv (SeqPerm.foldm_snoc vprop_monoid (value_vprops_seq vp s m borrows))
                     (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                        `star`
                      (SeqPerm.foldm_snoc vprop_monoid vs0_idx
                         `star`
                       SeqPerm.foldm_snoc vprop_monoid vs0_suffix));

       let upd_borrows = Map.upd i x borrows in

       let vs1 = value_vprops_seq vp s m upd_borrows in
       let vs1_prefix, vs1_idx, vs1_suffix = seq_split3 vs1 (U32.v idx) in
  
       calc (equiv) {
         value_vprops vp s m upd_borrows;
         (equiv) { foldm_snoc_split3 vs1 vs1_prefix vs1_idx vs1_suffix }
         SeqPerm.foldm_snoc vprop_monoid vs1_prefix
           `star`
         (SeqPerm.foldm_snoc vprop_monoid vs1_idx
            `star`
          SeqPerm.foldm_snoc vprop_monoid vs1_suffix);
         (equiv) { value_vprop_seq_upd_borrows h vp s m borrows (U32.v idx);
                   Classical.forall_intro equiv_refl }
         SeqPerm.foldm_snoc vprop_monoid vs0_prefix
           `star`
         (SeqPerm.foldm_snoc vprop_monoid vs1_idx
            `star`
          SeqPerm.foldm_snoc vprop_monoid vs0_suffix);
         (equiv) { assert (Seq.index vs1 (U32.v idx) == emp);
                   SeqPerm.foldm_snoc_singleton vprop_monoid emp;
                   equiv_helper_q_emp (SeqPerm.foldm_snoc vprop_monoid vs0_prefix)
                                      (SeqPerm.foldm_snoc vprop_monoid vs1_idx)
                                      (SeqPerm.foldm_snoc vprop_monoid vs0_suffix) }
         SeqPerm.foldm_snoc vprop_monoid vs0_prefix
           `star`
         SeqPerm.foldm_snoc vprop_monoid vs0_suffix;
       };
       equiv_sym (value_vprops vp s m upd_borrows)
                 (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                    `star`
                  SeqPerm.foldm_snoc vprop_monoid vs0_suffix);
       rewrite_equiv (SeqPerm.foldm_snoc vprop_monoid vs0_prefix
                          `star`
                      SeqPerm.foldm_snoc vprop_monoid vs0_suffix)
                     (value_vprops vp s m (Map.upd i x borrows));
       let Some c = Map.sel i m in
       assert (Seq.index vs0 (U32.v idx) == vp i x c);
       SeqPerm.foldm_snoc_singleton vprop_monoid (vp i x c);
       assert (equiv (SeqPerm.foldm_snoc vprop_monoid vs0_idx) (vp i x c));
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
#pop-options

let put #k #v #contents #vp #h #finalizer #m #borrows a i x c = admit__ ()

assume val value_vprops_split3
  (#k:eqtype)
  (#v #contents:Type0)
  (vp:vp_t k v contents)
  (s:Seq.seq (option (k & v)))
  (m:Map.t k contents)
  (borrows:Map.t k v)
  (i:nat{i < Seq.length s})
  : Lemma (let s1 = Seq.slice s 0 i in
           let s2 = Seq.create 1 (Seq.index s i) in
           let s3 = Seq.slice s (i+1) (Seq.length s) in
           value_vprops vp s m borrows
             `equiv`
           (value_vprops vp s1 m borrows
              `star`
            value_vprops vp s2 m borrows
              `star`
            value_vprops vp s3 m borrows))

let value_vprop_seq_rem_borrows
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
          (ensures (let Some (i, _) = Seq.index s idx in
                    value_vprops vp (Seq.slice s 0 idx) m borrows ==
                    value_vprops vp (Seq.slice s 0 idx) m (Map.remove i borrows) /\
                    value_vprops vp (Seq.slice s (idx+1) (Seq.length s)) m borrows ==
                    value_vprops vp (Seq.slice s (idx+1) (Seq.length s)) m (Map.remove  i borrows)))
  = let Some (i, _) = Seq.index s idx in
    assert (Seq.equal (value_vprops_seq vp (Seq.slice s 0 idx) m borrows)
                      (value_vprops_seq vp (Seq.slice s 0 idx) m (Map.remove i borrows)));
    assert (Seq.equal (value_vprops_seq vp (Seq.slice s (idx+1) (Seq.length s)) m borrows)
                      (value_vprops_seq vp (Seq.slice s (idx+1) (Seq.length s)) m (Map.remove i borrows)))

let ghost_put #_ #k #v #contents #vp #h #finalizer #m #borrows a i x c =
  let s = elim_exists () in
  A.pts_to_length a.store s;
  let idx = h i `U32.rem` a.store_len in
  elim_pure (seq_props h s /\
             store_and_repr_related s m /\
             store_and_borrows_related s borrows);
  value_vprops_split3 vp s m borrows (U32.v idx);
  rewrite_equiv (value_vprops vp s m borrows)
                (value_vprops vp (Seq.slice s 0 (U32.v idx)) m borrows
                   `star`
                 value_vprops vp (Seq.create 1 (Seq.index s (U32.v idx))) m borrows
                   `star`
                 value_vprops vp (Seq.slice s (U32.v idx+1) (Seq.length s)) m borrows);
  SeqPerm.foldm_snoc_singleton vprop_monoid emp;
  rewrite_equiv (value_vprops vp (Seq.create 1 (Seq.index s (U32.v idx))) m borrows) emp;
  value_vprop_seq_rem_borrows h vp s m borrows (U32.v idx);
  rewrite (value_vprops vp (Seq.slice s 0 (U32.v idx)) m borrows
             `star`
           value_vprops vp (Seq.slice s (U32.v idx+1) (Seq.length s)) m borrows)
          (value_vprops vp (Seq.slice s 0 (U32.v idx)) m (Map.remove i borrows)
             `star`
           value_vprops vp (Seq.slice s (U32.v idx+1) (Seq.length s)) m (Map.remove i borrows));
  SeqPerm.foldm_snoc_singleton vprop_monoid (vp i x c);
  rewrite_equiv (vp i x c)
                (value_vprops vp (Seq.create 1 (Seq.index s (U32.v idx))) m (Map.remove i borrows));
  value_vprops_split3 vp s m (Map.remove i borrows) (U32.v idx);
  rewrite_equiv (value_vprops vp (Seq.slice s 0 (U32.v idx)) m (Map.remove i borrows)
                   `star`
                 value_vprops vp (Seq.create 1 (Seq.index s (U32.v idx))) m (Map.remove i borrows)
                   `star`
                 value_vprops vp (Seq.slice s (U32.v idx+1) (Seq.length s)) m (Map.remove i borrows))
                (value_vprops vp s m (Map.remove i borrows));
  R.write a.g_borrows (Map.remove i borrows);
  intro_pure (seq_props h s /\
              store_and_repr_related s m /\
              store_and_borrows_related s (Map.remove i borrows));
  intro_exists (G.reveal s) (store_contents_pred a m (Map.remove i borrows))

assume val foldm_snoc_empty (#a:_) (#eq:_) (m:CE.cm a eq)
  : Lemma (SeqPerm.foldm_snoc m Seq.empty == m.unit)

let rec finalize_values
  (#k:eqtype)
  (#v #contents:Type0)
  (#vp:vp_t k v contents)
  (#h:hash_fn k)
  (#finalizer:finalizer_t vp)
  (#s:G.erased (Seq.seq (option (k & v))))
  (#m:G.erased (repr k contents))
  (n:U32.t)
  (a:tbl h finalizer)
  (i:U32.t{U32.v n = Seq.length s /\ U32.v i <= U32.v n})
  (s_ind:G.erased (Seq.seq (option (k & v))))
  : ST unit (A.pts_to a.store s
               `star`
             value_vprops vp s_ind m (Map.empty k v))
            (fun _ -> A.pts_to a.store s)
            (requires store_and_repr_related s m /\
                      Seq.length s == Seq.length s_ind /\
                      (forall (j:nat{j < U32.v i}). Seq.index s_ind j == None) /\
                      (forall (j:nat{U32.v i <= j /\ j < Seq.length s}).
                         Seq.index s_ind j == Seq.index s j))
            (ensures fun _ -> True)
                        
  = A.pts_to_length a.store s;
    if i = n
    then begin
      foldm_snoc_unit_seq vprop_monoid (value_vprops_seq vp s_ind m (Map.empty k v));
      rewrite_equiv (value_vprops vp s_ind m (Map.empty k v)) emp
    end
    else begin
      let vopt = A.read a.store i in
      match vopt with
      | None ->
        finalize_values n a (U32.add i 1ul) s_ind
      | Some (i', x) ->
        value_vprops_split3 vp s_ind m (Map.empty k v) (U32.v i);
        rewrite_equiv (value_vprops vp s_ind m (Map.empty k v))
                      (value_vprops vp (Seq.slice s_ind 0 (U32.v i)) m (Map.empty k v)
                         `star`
                       value_vprops vp (Seq.create 1 (Seq.index s_ind (U32.v i))) m   (Map.empty k v)
                         `star`
                       value_vprops vp (Seq.slice s_ind (U32.v i+1) (Seq.length s_ind)) m (Map.empty k v));
        SeqPerm.foldm_snoc_singleton vprop_monoid (vp i' x (Some?.v (Map.sel i' m)));
        rewrite_equiv (value_vprops vp (Seq.create 1 (Seq.index s_ind (U32.v i))) m   (Map.empty k v))
                      (vp i' x (Some?.v (Map.sel i' m)));
        intro_exists (Some?.v (Map.sel i' m)) (vp i' x);
        finalizer i' x;
        SeqPerm.foldm_snoc_singleton vprop_monoid emp;
        rewrite_equiv emp (value_vprops vp (Seq.create 1 (Seq.index (Seq.upd s_ind (U32.v i) None) (U32.v i))) m (Map.empty k v));
        rewrite (value_vprops vp (Seq.slice s_ind 0 (U32.v i)) m (Map.empty k v))
                (value_vprops vp (Seq.slice (Seq.upd s_ind (U32.v i) None) 0 (U32.v i)) m (Map.empty k v));
        rewrite (value_vprops vp (Seq.slice s_ind (U32.v i+1) (Seq.length s_ind)) m (Map.empty k v))
                (value_vprops vp (Seq.slice (Seq.upd s_ind (U32.v i) None) (U32.v i+1) (Seq.length s_ind)) m (Map.empty k v));
        value_vprops_split3 vp (Seq.upd s_ind (U32.v i) None) m (Map.empty k v) (U32.v i);
        rewrite_equiv (value_vprops vp (Seq.slice (Seq.upd s_ind (U32.v i) None) 0 (U32.v i)) m (Map.empty k v)
                         `star`
                       value_vprops vp (Seq.create 1 (Seq.index (Seq.upd s_ind (U32.v i) None) (U32.v i))) m   (Map.empty k v)
                         `star`
                       value_vprops vp (Seq.slice (Seq.upd s_ind (U32.v i) None) (U32.v i+1) (Seq.length s_ind)) m (Map.empty k v))
                      (value_vprops vp (Seq.upd s_ind (U32.v i) None) m (Map.empty k v));
        finalize_values n a (U32.add i 1ul) (Seq.upd s_ind (U32.v i) None)
    end

let free #k #v #contents #vp #h #finalizer #m a =
  let s = elim_exists () in
  elim_pure (seq_props h s /\
             store_and_repr_related s m /\
             store_and_borrows_related s (Map.empty k v));
  A.pts_to_length a.store s;
  finalize_values a.store_len a 0ul s;
  intro_exists (G.reveal s) (A.pts_to a.store);
  A.free a.store;
  R.free a.g_repr;
  R.free a.g_borrows
