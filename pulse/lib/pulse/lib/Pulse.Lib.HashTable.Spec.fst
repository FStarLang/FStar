(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.HashTable.Spec
#lang-pulse
module US = FStar.SizeT

open FStar.Ghost

[@@ Pulse.Lib.Pervasives.Rust_derive "Clone"]
noeq
type cell ([@@@ Pulse.Lib.Pervasives.Rust_generics_bounds ["PartialEq"; "Copy"; "Clone"]] kt : eqtype)
          ([@@@ Pulse.Lib.Pervasives.Rust_generics_bounds ["Clone"]] vt : Type) =
  | Clean
  | Zombie
  | Used : k:kt -> v:vt -> cell kt vt

// Pure view of the hash table
type spec_t (k:eqtype) v = k -> option v

let lookup_spec #k #v (spec:spec_t k v) (key:k) : option v =
  spec key

noeq
type repr_t (k:eqtype) (v:Type) = {
   sz:pos;
   seq:Seq.lseq (cell k v) sz;
   hashf: k -> nat
}

let canonical_index (#kt:eqtype) #vt (key:kt) (repr:repr_t kt vt) : nat =
  repr.hashf key % repr.sz

let (@@) #kt #vt (r:repr_t kt vt) (i:nat{ i < r.sz }) = Seq.index r.seq i

let (++) #k #v (htf : spec_t k v) (key, value) : spec_t k v =
  fun k' ->
    if key = k' then Some value else htf k'

let (--) #k #v (htf : spec_t k v) key : spec_t k v =
  fun k' ->
    if key = k' then None else htf k'

// starting at idx, walk until you find kv pair (k,v) at index idx'
// return Some (idx',v) else None if took sz steps and did not find
let rec walk_get_idx #kt #vt (repr : repr_t kt vt) (idx:nat) (k:kt) (off:nat{off<=repr.sz}) 
  : Tot (o:(option (vt & nat))
          {match o with 
           | Some (v,i) -> i<repr.sz /\ repr @@ i == Used k v
           | None -> true})
        (decreases repr.sz - off) =
  if off = repr.sz then None
  else
  let idx' = (idx + off) % repr.sz in
  match repr @@ idx' with
  | Clean -> None
  | Used k' v ->
    if k = k'
    then Some (v,idx')
    else walk_get_idx repr idx k (off+1)
  | Zombie ->
    walk_get_idx repr idx k (off + 1)

let rec walk_get_idx_upd #kt #vt (repr1 repr2:repr_t kt vt) (idx:nat) (k:kt) (off:nat{off <= repr1.sz})
  (idx':nat { idx' < repr1.sz /\ Used? (repr1 @@ idx') })
  (v:vt)
  : Lemma
      (requires (let Used k' v' = repr1 @@ idx' in
                 repr2 == { repr1 with seq = Seq.upd repr1.seq idx' (Used k' v) }))
      (ensures (let Used k' v' = repr1 @@ idx' in
                let o1 = walk_get_idx repr1 idx k off in
                let o2 = walk_get_idx repr2 idx k off in
                match o1, o2 with
                | None, None -> True
                | Some (_, i1), Some (v2, i2) ->
                  i1 == i2 /\ Seq.index repr2.seq i2 == Used k v2
                | _ -> False))
      (decreases repr1.sz - off) =
  
  if off = repr1.sz then ()
  else
    let idx'' = (idx + off) % repr1.sz in
    match repr1 @@ idx'' with
    | Clean -> ()
    | Used k' v' ->
      if k' = k then ()
      else walk_get_idx_upd repr1 repr2 idx k (off+1) idx' v
    | Zombie -> walk_get_idx_upd repr1 repr2 idx k (off+1) idx' v


// perform a walk from idx but do not return idx' where k was found
let walk #kt #vt (repr : repr_t kt vt) (idx:nat) (k : kt) (off:nat{off <= repr.sz}) : option vt
  = match walk_get_idx repr idx k off with 
    | Some (v,_) -> Some v
    | _ -> None

// perform a walk starting at the cacnonical index of k
let lookup_repr #kt #vt (repr : repr_t kt vt) (k : kt) : option vt =
  let idx = canonical_index k repr in
  walk repr idx k 0

// perform a walk starting at the canonical index of k
// but do not return idx' where k was found
let lookup_repr_index #kt #vt (repr : repr_t kt vt) (k : kt)
  : option (vt & nat)
  = let idx = canonical_index k repr in
    walk_get_idx repr idx k 0

type spec_submap_repr #kt #vt
  (spec : spec_t kt vt)
  (repr : repr_t kt vt)
: Type0
= forall k. Some? (lookup_spec spec k) ==> lookup_repr repr k == lookup_spec spec k

type repr_submap_spec #kt #vt
  (spec : spec_t kt vt)
  (repr : repr_t kt vt)
: Type0
= forall k. Some? (lookup_repr repr k) ==> lookup_repr repr k == lookup_spec spec k

type unique_keys #kt #vt
  (spec : spec_t kt vt)
  (repr : repr_t kt vt)
: Type0
= forall i k v. repr @@ i == Used k v ==> lookup_repr_index repr k == Some (v, i)

// FIXME: missing a bunch more interesting properties
type pht_models #kt #vt
  (spec : spec_t kt vt)
  (repr : repr_t kt vt)
: Type0
= spec_submap_repr spec repr /\
  repr_submap_spec spec repr /\
  unique_keys spec repr

(* This is the main hash table type *)
noeq
type pht_t (kt:eqtype) (vt:Type) = {
  // spec is the pure, very high-level view of the hash table
  // as a partial map from keys to values. We mark it erased
  // so it does not show up in extraction. Another possibility
  // is to have a keyt -> GTot (option vt) function. Is that better
  // somehow? Does it also get erased? (I think so, but double check)
  spec : Ghost.erased (spec_t kt vt);
  repr : repr_t kt vt;
  inv : squash (pht_models spec repr /\ US.fits repr.sz);
}

let upd_ #kt #vt (repr : repr_t kt vt) idx k v : repr_t kt vt =
 { repr with seq=Seq.upd repr.seq idx (Used k v) }

let del_ #kt #vt (repr : repr_t kt vt) idx : repr_t kt vt =
 { repr with seq=Seq.upd repr.seq idx Zombie }

let repr_related #kt #vt (r1 r2:repr_t kt vt) =
  r1.hashf == r2.hashf /\ r1.sz == r2.sz

let repr_t_sz kt vt sz = r:repr_t kt vt { r.sz == sz}

let lemma_clean_upd_lookup_walk #kt #vt #sz
      (spec1 spec2 : spec_t kt vt) 
      (repr1 repr2 : repr_t_sz kt vt sz)
      idx k v (k':_{k =!= k'})
  : Lemma (requires
      repr_related repr1 repr2 
      /\ (forall i. i < repr1.sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ None? (lookup_repr repr1 k)
      /\ pht_models spec1 repr1
      /\ repr1 @@ idx == Clean
      /\ repr2 == upd_ repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' repr1 in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases repr1.sz - off) 
  = if off = sz then ()
    else if (idx' + off) % sz = idx then
      aux (off+1)
    else begin
      match repr1 @@ ((idx' + off) % sz) with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then ()
        else aux (off+1)
      | Zombie ->
        aux (off+1)
    end
  in
  aux 0

let lemma_used_upd_lookup_walk #kt #vt #sz
      (spec1 spec2 : spec_t kt vt)
      (repr1 repr2 : repr_t_sz kt vt sz)
      idx k (k':_{k =!= k'})
      (v v' : vt)
  : Lemma (requires
         repr_related repr1 repr2
      /\ (forall i. i < repr1.sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ pht_models spec1 repr1
      /\ repr1 @@ idx == Used k v'
      /\ repr2 @@ idx == Used k v
      /\ repr2 == upd_ repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' repr1 in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
  = if off = repr1.sz then ()
    else if (idx' + off) % sz = idx then
      match repr1 @@ idx with
      | Used k'' _ ->
        if k' = k'' then ()
        else aux (off+1)
    else begin
      match repr1 @@ ((idx' + off) % repr1.sz) with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then ()
        else aux (off+1)
      | Zombie ->
        aux (off+1)
    end
  in
  aux 0

let lemma_del_lookup_walk #kt #vt #sz 
      (spec1 spec2 : spec_t kt vt)
      (repr1 repr2 : repr_t_sz kt vt sz)
      upos k v (k':_{k =!= k'})
  : Lemma (requires
      repr_related repr1 repr2 /\
      (forall i. i < sz /\ i <> upos ==> repr1 @@ i == repr2 @@ i) /\
      pht_models spec1 repr1 /\
      repr1 @@ upos == Used k v /\
      repr2 @@ upos == Zombie /\
      spec2 == spec1 -- k)
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' repr1 in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
  =
    if off = sz then ()
    else if (idx' + off) % sz = upos then
      aux (off+1)
    else begin
      match repr1 @@ (idx' + off) % sz with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then ()
        else aux (off+1)
      | Zombie ->
        aux (off+1)
    end
  in
  aux 0

let lemma_zombie_upd_lookup_walk #kt #vt #sz
      (spec spec' : spec_t kt vt)
      (repr repr' : repr_t_sz kt vt sz)
      idx k v (k':_{k =!= k'})
  : Lemma (requires
      repr_related repr repr'
      /\ (forall i. i < sz /\ i <> idx ==> repr @@ i == repr' @@ i)
      /\ pht_models spec repr
      /\ repr' == upd_ repr idx k v
      /\ repr @@ idx == Zombie
      /\ spec' == spec ++ (k,v))
      (ensures lookup_repr repr k' == lookup_repr repr' k')
= let idx' = canonical_index k' repr in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr idx' k' off == lookup_repr repr k'
               /\ walk repr' idx' k' off == lookup_repr repr' k')
        (ensures walk repr idx' k' off == walk repr' idx' k' off)
        (decreases sz - off) 
  = if off = sz then ()
    else if (idx' + off) % sz = idx then
      aux (off+1)
    else begin
      match repr @@ ((idx' + off) % sz) with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then ()
        else aux (off+1)
      | Zombie ->
        aux (off+1)
    end
  in
  aux 0

let strong_used_not_by #kt #kv (repr : repr_t kt kv) (k : kt) (i : nat{i < repr.sz}): prop =
  (Used? (repr @@ i) /\ Used?.k (repr @@ i) <> k)

let used_not_by #kt #kv (repr : repr_t kt kv) (k : kt) (i : nat{i < repr.sz}): prop =
  strong_used_not_by repr k i \/ Zombie? (repr @@ i)
  
let all_used_not_by #kt #kv (repr : repr_t kt kv) (idx : (n:nat{n < repr.sz})) (len : nat) (k : kt) : prop =
  forall (i:nat{i < len}). used_not_by repr k ((idx+i) % repr.sz)

let strong_all_used_not_by #kt #kv (repr : repr_t kt kv) (idx : (n:nat{n < repr.sz})) (len : nat) (k : kt) : prop =
  forall (i:nat{i < len}). strong_used_not_by repr k ((idx+i) % repr.sz)

let aunb_extend #kt #kv (repr : repr_t kt kv) (idx : (n:nat{n < repr.sz})) (off : nat) (k : kt)
  : Lemma (requires all_used_not_by repr idx off k /\ used_not_by repr k ((idx+off) % repr.sz))
          (ensures  all_used_not_by repr idx (off+1) k)
  = ()

let aunb_shrink #kt #kv (repr : repr_t kt kv) (idx : (n:nat{n < repr.sz})) (off : nat) (k : kt)
  : Lemma (requires all_used_not_by repr idx off k /\ off > 0)
          (ensures  all_used_not_by repr ((idx+1) % repr.sz) (off-1) k)
  = let sz = repr.sz in
    let sidx = (idx+1) % sz in
    let open FStar.Math.Lemmas in
    let aux (i:nat{i < off-1}) : Lemma (used_not_by repr k ((sidx+i)%sz)) =
      assert (used_not_by repr k ((idx+(i+1)) % repr.sz));
      calc (==) {
        (sidx + i) % sz;
        == {}
        (((idx + 1) % sz) + i) % sz;
        == { lemma_mod_twice (idx+1) sz;
             assert (sidx % sz = (idx+1) % sz);
             modulo_add sz i sidx (idx+1) }
        (idx + 1 + i) % sz;
      };
      assert (used_not_by repr k ((sidx+i) % sz));
      ()
    in
    Classical.forall_intro #(i:nat{i < off-1}) aux;
    ()

#push-options "--z3rlimit 20"
let lemma_walk_from_canonical_all_used #kt #kv (repr : repr_t kt kv) (off : nat{off < repr.sz}) k v 
  : Lemma (requires all_used_not_by repr (canonical_index k repr) off k
                 /\ repr @@ ((canonical_index k repr + off) % repr.sz) == Used k v)
          (ensures lookup_repr repr k == Some v)
= let sz = repr.sz in
  let cidx = canonical_index k repr in
  let rec aux (off':nat{off' <= off}) (_ : squash (all_used_not_by repr ((cidx+off')%sz) (off-off') k))
    : Lemma (ensures walk repr cidx k off' == Some v)
            (decreases off - off')
    = if off' = off then () else begin
        Math.Lemmas.modulo_distributivity (cidx+off') 1 sz;
        assert (sz >= 2); // Note: we can only be here if off>0, which means sz>1
        Math.Lemmas.modulo_lemma 1 sz;
        assert (1 % sz == 1);
        assert (((cidx + off') % sz + 1) % sz == (cidx+off'+1) % sz);
        aunb_shrink repr ((cidx+off')%sz) (off-off') k;
        aux (off'+1) ()
      end
  in
  Math.Lemmas.modulo_lemma cidx sz;
  assert (cidx % sz == cidx); // hint for z3
  aux 0 ();
  assert (lookup_repr repr k == walk repr cidx k 0);
  assert (lookup_repr repr k == Some v);
  ()
#pop-options

let lemma_clean_upd #kt #vt spec (repr : repr_t kt vt) (off:nat{off < repr.sz}) k v 
  : Lemma
       (requires pht_models spec repr
              /\ None? (lookup_repr repr k)
              /\ repr @@ (canonical_index k repr + off) % repr.sz == Clean
              /\ all_used_not_by repr (canonical_index k repr) off k)
       (ensures pht_models (spec ++ (k,v)) (upd_ repr ((canonical_index k repr + off) % repr.sz) k v))
  = let sz = repr.sz in
    let spec' = spec ++ (k,v) in
    let idx = (canonical_index k repr + off) % sz in
    let repr' = upd_ repr idx k v in
    let aux1 (k':kt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_clean_upd_lookup_walk #_ #_ #repr.sz spec spec' repr repr' idx k v k' 
    in
    let aux2 (k':kt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_clean_upd_lookup_walk #_ #_ #repr.sz spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':kt) (v':vt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k = k' then 
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_clean_upd_lookup_walk #_ #_ #repr.sz spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_used_upd #kt #vt #sz spec (repr : repr_t_sz kt vt sz) (off:nat{off < sz}) k (v v' : vt) 
  : Lemma
       (requires pht_models spec repr
              /\ Some? (lookup_repr repr k)
              /\ repr @@ (canonical_index k repr + off)%sz == Used k v'
              /\ all_used_not_by repr (canonical_index k repr) off k)
       (ensures pht_models (spec ++ (k,v)) (upd_ repr ((canonical_index k repr + off)%sz) k v))
  = let spec' = spec ++ (k,v) in
    let idx = (canonical_index k repr + off) % sz in
    let repr' = upd_ repr idx k v in
    let aux1 (k':kt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v' 
    in
    let aux2 (k':kt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v'
    in
    let aux3 (i':nat{i'<sz}) (k':kt) (v'':vt) : Lemma (requires (repr' @@ i' == Used k' v''))
                                                              (ensures (lookup_repr_index repr' k' == Some (v'', i')))
    = if k' = k then begin
        assert (lookup_repr_index repr k == Some (v',idx)); // this assert is necessary
        lemma_walk_from_canonical_all_used repr' off k v;
        ()
      end
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_zombie_upd #kt #vt #sz spec (repr : repr_t_sz kt vt sz) (off:nat{off < sz}) k v 
  : Lemma
       (requires pht_models spec repr
              /\ None? (lookup_repr repr k)
              /\ repr @@ (canonical_index k repr + off) % sz == Zombie
              /\ all_used_not_by repr (canonical_index k repr) off k)
       (ensures pht_models (spec ++ (k,v)) (upd_ repr ((canonical_index k repr + off) % sz) k v))
  = let spec' = spec ++ (k,v) in
    let idx = (canonical_index k repr + off) % sz in
    let repr' = upd_ repr idx k v in
    
    let aux (i:nat{i < off}) : Lemma (used_not_by repr' k ((canonical_index k repr + i) % sz)) =
      calc (==>) {
        (canonical_index k repr + i) % sz == idx;
        ==> {}
        (canonical_index k repr + i) % sz == (canonical_index k repr + off) % sz;
        ==> { Math.Lemmas.lemma_mod_plus_injective sz (canonical_index k repr) i off }
        i == off;
      }
    in
    Classical.forall_intro aux;
    assert (all_used_not_by repr' (canonical_index k repr) off k);

    let aux1 (k':kt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then begin
        lemma_walk_from_canonical_all_used repr' off k v;
        ()
      end else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k' 
    in
    let aux2 (k':kt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':kt) (v':vt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' off k v
      else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_del #kt #vt #sz spec (repr : repr_t_sz kt vt sz) idx k v 
  : Lemma
       (requires pht_models spec repr
              /\ Some? (lookup_repr repr k)
              /\ repr @@ idx == Used k v)
       (ensures pht_models (spec -- k) (del_ repr idx))
  = let spec' = spec -- k in
    let repr' = del_ repr idx in
    let aux1 (k':kt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then 
        ()
      else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux2 (k':kt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then begin
        let Some (v', i') = lookup_repr_index repr' k' in
        assert (i' <> idx);
        assert (lookup_repr_index repr k == Some (v', i'));
        assert (lookup_repr_index repr k == Some (v, idx));
        ()
      end else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':kt) (v':vt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k' = k then begin
        assert (i' <> idx);
        assert (lookup_repr_index repr k == Some (v', i'));
        assert (lookup_repr_index repr k == Some (v, idx));
        ()
      end else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let not_full #kt #vt (r:repr_t kt vt) : Type0 =
  exists i. ~(Used? (r @@ i ))

#set-options "--split_queries always"
#restart-solver
#push-options "--z3rlimit_factor 4"
let rec insert_repr_walk #kt #vt #sz (#spec : erased (spec_t kt vt)) 
  (repr : repr_t_sz kt vt sz{pht_models spec repr /\ not_full repr}) (k : kt) (v : vt) 
  (off:nat{off <= sz})
  (cidx:nat{cidx = canonical_index k repr})
  (_ : squash (strong_all_used_not_by repr cidx off k))
  (_ : squash (walk repr cidx k off == lookup_repr repr k))
  : Tot (repr':repr_t_sz kt vt sz{
          pht_models (spec ++ (k,v)) repr' /\
          repr_related repr repr'
        })
        (decreases sz - off)
  = if off = sz then (
      // Impossible! table was not full
      let aux (i:nat{i < sz}) : Lemma (Used? (repr @@ i)) =
        assert (all_used_not_by repr cidx sz k);
        let off = (i - cidx) % sz in
        calc (==) {
          (cidx + off) % sz;
          == {}
          (cidx + ((i - cidx) % sz)) % sz;
          == { Math.Lemmas.modulo_lemma cidx sz }
          (cidx % sz + ((i - cidx) % sz)) % sz;
          == { Math.Lemmas.modulo_distributivity cidx (i-cidx) sz }
          i % sz;
          == { Math.Lemmas.modulo_lemma i sz }
          i;
        };
        assert (Used? (repr @@ i));
        ()
      in
      Classical.forall_intro aux;
      false_elim () (* unreachable *)
    )
    else
    let idx = (cidx+off) % sz in
    match repr @@ idx with
    | Used k' v' ->
      if k = k'
      then begin
        (**)lemma_used_upd spec repr off k v v';
        upd_ repr idx k v
      end else begin
        assert (all_used_not_by repr cidx (off+1) k);
        insert_repr_walk #kt #vt #sz #spec repr k v (off+1) cidx () ()
      end
    
    | Clean ->
      (**)lemma_clean_upd spec repr off k v;
      upd_ repr idx k v
    
    | Zombie ->
      match lookup_repr_index repr k with 
        | Some (v_old,i) -> (
          (**)lemma_del spec repr i k v_old;
          // Don't need these asserts
          let cidx = canonical_index k repr in
          assert (all_used_not_by repr cidx off k);
          // GM: Removing this assert, not needed now it seems
          //assert (if idx >= cidx then i > idx || i <= cidx else i > idx /\ i <= cidx);
          assert (all_used_not_by (del_ repr i) cidx off k);
          (**)lemma_zombie_upd #_ #_ #sz (spec -- k) (del_ repr i) off k v;
          upd_ (del_ repr i) idx k v
        )
        | None -> (
          (**)lemma_zombie_upd spec repr off k v;
          upd_ repr idx k v
        )
#pop-options

let insert_repr #kt #vt #sz
                (#spec : erased (spec_t kt vt))
                (repr : repr_t_sz kt vt sz{pht_models spec repr})
                (k : kt) 
                (v : vt)
: Pure (r':repr_t_sz kt vt sz{
        pht_models (spec ++ (k,v)) r' /\
        repr_related repr r'
       })
       (requires not_full repr)
       (ensures fun _ -> True)
= let cidx = canonical_index k repr in
  let res = insert_repr_walk #kt #vt #sz #spec repr k v 0 cidx () () in
  res

#push-options "--z3rlimit_factor 2"
let rec delete_repr_walk #kt #vt #sz (#spec : erased (spec_t kt vt)) 
  (repr : repr_t_sz kt vt sz{pht_models spec repr}) (k : kt)
  (off:nat{off <= sz}) (cidx:nat{cidx = canonical_index k repr})
  (_ : squash (all_used_not_by repr cidx off k))
  (_ : squash (walk repr cidx k off == lookup_repr repr k))
  : Tot (repr':repr_t_sz kt vt sz{
          pht_models (spec -- k) repr' /\
          repr_related repr repr'
        })
        (decreases sz - off)
  = if off = sz then
    repr // If we reach this, the element was not in the table
    else
    let idx = (cidx+off) % sz in
    match repr @@ idx with
    | Used k' v' ->
      if k = k'
      then begin
        (**)lemma_del spec repr idx k v';
        del_ repr idx
      end else begin
        assert (all_used_not_by repr cidx (off+1) k);
        delete_repr_walk #kt #vt #sz #spec repr k (off+1) cidx () ()
      end

    | Clean -> repr

    | Zombie -> delete_repr_walk #kt #vt #sz #spec repr k (off+1) cidx () ()
#pop-options

let delete_repr #kt #vt #sz (#spec : erased (spec_t kt vt))
              (repr : repr_t_sz kt vt sz{pht_models spec repr})
              (k : kt)
: r':repr_t_sz kt vt sz{
    pht_models (spec -- k) r' /\
    repr_related repr r'
  }
= let cidx = canonical_index k repr in
  let res = delete_repr_walk #kt #vt #sz #spec repr k 0 cidx () () in
  res

// TODO: This states we can only insert on a non-full table,
// but that's only if the key we want to insert is not already present,
// so it's stronger than it should be. This is anyway perhaps not important
// for this pure implementation, as the Pulse implementation could always
// keep one cell free and trivially satisfy this invariant.
let insert #kt #vt (ht : pht_t kt vt{not_full ht.repr}) (k : kt) (v : vt)
: ht':(pht_t kt vt){ht'.spec == Ghost.hide (ht.spec ++ (k,v)) }
=
  { ht with spec = Ghost.hide (ht.spec ++ (k,v));
            repr = insert_repr #_ #_ #ht.repr.sz #ht.spec ht.repr k v;
            inv = () }

let delete #kt #vt (ht : pht_t kt vt) (k : kt)
: ht':(pht_t kt vt){ht'.spec == Ghost.hide (ht.spec -- k) }
=
  { ht with spec = Ghost.hide (ht.spec -- k);
            repr = delete_repr #_ #_ #ht.repr.sz #ht.spec ht.repr k;
            inv = () }

let lookup #kt #vt (ht : pht_t kt vt) (k : kt)
: o:(option vt){o == lookup_spec ht.spec k}
=
  lookup_repr ht.repr k

let lookup_index #kt #vt (ht : pht_t kt vt) (k : kt)
: option (vt & nat)
=
  lookup_repr_index ht.repr k

// let lookup_index_us #kt #vt (ht : pht_t kt vt) (k : kt)
// : option (vt & US.t)
// = let o = lookup_repr_index ht.repr k in
//   match o with
//   | Some (v,i) -> Some (v, US.uint_to_t i)
//   | None -> None

let lookup_index_us #kt #vt (ht : pht_t kt vt) (k : kt)
: option US.t
= let o = lookup_repr_index ht.repr k in
  match o with
  | Some (_, i) -> Some (US.uint_to_t i)
  | None -> None

let upd_pht (#kt:eqtype) (#vt:Type) (pht:pht_t kt vt) idx (k:kt) (v:vt)
  (_:squash (lookup_index_us pht k == Some idx)) : pht_t kt vt =
  let spec' = Ghost.hide (pht.spec ++ (k, v)) in
  let repr' = upd_ pht.repr (US.v idx) k v in

  let Used k v' = pht.repr @@ US.v idx in

  let cidx = canonical_index #kt #vt k pht.repr in
  walk_get_idx_upd pht.repr repr' cidx k 0 (US.v idx) v;
  assert (lookup_repr_index repr' k == Some (v, US.v idx));

  introduce forall (k':kt { k' =!= k }). lookup_repr repr' k' == lookup_repr pht.repr k'
  with  lemma_used_upd_lookup_walk #_ #_ #pht.repr.sz pht.spec spec' pht.repr repr' (US.v idx) k k' v v';

  { pht with spec = spec';
             repr = repr';
             inv = () }

#push-options "--z3rlimit_factor 3"
let eliminate_strong_all_used_not_by #kt #vt (r:repr_t kt vt) (k:kt) (i:nat{i < r.sz})
  : Lemma 
    (requires strong_all_used_not_by r (canonical_index k r) r.sz k)
    (ensures Used? (r @@ i) /\ Used?.k (r @@ i) <> k)
  = let j = canonical_index k r in
    if (j < i) 
    then (
        assert (i == (j + (i-j)) % r.sz);
        assert (Used? (r @@ i))
    )
    else (
      let k = ((r.sz - j) + i) in
      assert (i == (j + k) % r.sz);
      if (k < r.sz) then (
        assert (Used? (r @@ i))
      )
      else (
        assert (i == (j + 0) % r.sz);
        assert (Used? (r @@ ((j + 0) % r.sz)))
      )
    )
#pop-options

let full_not_full #kt #vt (r:repr_t kt vt) (k:kt)
  : Lemma 
    (requires
      not_full r /\
      strong_all_used_not_by r (canonical_index k r) r.sz k)
    (ensures False)
  = eliminate exists (i:nat { i < r.sz }). ~(Used? (r @@ i))
    returns False
    with _ . (
      assert (~(Used? (r@@i)));
      eliminate_strong_all_used_not_by r k i
    )
