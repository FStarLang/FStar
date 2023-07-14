module LinearScanHashTable

open FStar.Ghost

noeq
type cell (kt : Type) (vt : Type) =
  | Clean
  | Zombie
  | Used : k:kt -> v:vt -> cell kt vt

noeq
type pht_sig = {
  keyt : eqtype;
  valt : Type0;
  hashf : keyt -> nat;
}

// Pure view of the hash table
type spec_t (s : pht_sig) = s.keyt -> option s.valt

let lookup_spec (#s:pht_sig) (spec:spec_t s) (k : s.keyt) : option s.valt =
  spec k

type repr_t (s : pht_sig) (sz : pos) =
  Seq.lseq (cell s.keyt s.valt) sz
  
let canonical_index #s (k : s.keyt) (sz : pos) : n:nat{n < sz} =
  (s.hashf k) % sz

let (@@) = Seq.index

let (++) #s (htf : spec_t s) (k, v) : spec_t s =
  fun k' ->
    if k = k' then Some v else htf k'

let (--) #s (htf : spec_t s) k : spec_t s =
  fun k' ->
    if k = k' then None else htf k'

// starting at idx, walk until you find kv pair (k,v) at index idx'
// return Some (idx',v) else None if took sz steps and did not find
let rec walk_get_idx #s #sz (repr : repr_t s sz) (idx:nat) (k:s.keyt) (off:nat{off<=sz}) 
  : Tot (o:(option (s.valt & nat))
          {match o with 
           | Some (v,i) -> i<sz /\ repr @@ i == Used k v
           | None -> true})
        (decreases sz - off) =
  if off = sz then None
  else
  let idx' = (idx + off) % sz in
  match repr @@ idx' with
  | Clean -> None
  | Used k' v ->
    if k = k'
    then Some (v,idx')
    else walk_get_idx repr idx k (off+1)
  | Zombie ->
    walk_get_idx repr idx k (off + 1)

// perform a walk from idx but do not return idx' where k was found
let walk #s #sz (repr : repr_t s sz) (idx:nat) (k : s.keyt) (off:nat{off <= sz}) : option s.valt 
  = match walk_get_idx repr idx k off with 
    | Some (v,_) -> Some v
    | _ -> None

// perform a walk starting at the cacnonical index of k
let lookup_repr (#s : pht_sig) #sz (repr : repr_t s sz) (k : s.keyt) : option s.valt =
  let idx = canonical_index k sz in
  walk repr idx k 0

// perform a walk starting at the cacnonical index of k
// but do not return idx' where k was found
let lookup_repr_index (#s : pht_sig) #sz (repr : repr_t s sz) (k : s.keyt) 
  : (option (s.valt & nat))
  = let idx = canonical_index k sz in
    walk_get_idx repr idx k 0

type spec_submap_repr (s : pht_sig) (sz : pos)
  (spec : spec_t s)
  (repr : Seq.lseq (cell s.keyt s.valt) sz)
: Type0
= forall k. Some? (lookup_spec spec k) ==> lookup_repr repr k == lookup_spec spec k

type repr_submap_spec (s : pht_sig) (sz : pos)
  (spec : spec_t s)
  (repr : Seq.lseq (cell s.keyt s.valt) sz)
: Type0
= forall k. Some? (lookup_repr repr k) ==> lookup_repr repr k == lookup_spec spec k

type unique_keys (s : pht_sig) (sz : pos)
  (spec : spec_t s)
  (repr : Seq.lseq (cell s.keyt s.valt) sz)
: Type0
= forall i k v. repr @@ i == Used k v ==> lookup_repr_index repr k == Some (v, i)

// FIXME: missing a bunch more interesting properties
type pht_models (s : pht_sig) (sz : pos)
  (spec : spec_t s)
  (repr : Seq.lseq (cell s.keyt s.valt) sz)
: Type0
= spec_submap_repr s sz spec repr /\
  repr_submap_spec s sz spec repr /\
  unique_keys s sz spec repr

noeq
type pht (s : pht_sig) = {
  sz : pos;
  // spec is the pure, very high-level view of the hash table
  // as a partial map from keys to values. We mark it erased
  // so it does not show up in extraction. Another possibility
  // is to have a keyt -> GTot (option s.valt) function. Is that better
  // somehow? Does it also get erased? (I think so, but double check)
  spec : Ghost.erased (spec_t s);
  repr : Seq.lseq (cell s.keyt s.valt) sz;
  inv : squash (pht_models s sz spec repr);
}

let lookup #s (ht : pht s) (k : s.keyt) : option s.valt =
  lookup_repr ht.repr k
  
let upd_ #s #sz (repr : repr_t s sz) idx k v : repr_t s sz =
  Seq.upd repr idx (Used k v)

let del_ #s #sz (repr : repr_t s sz) idx : repr_t s sz =
  Seq.upd repr idx Zombie

let lemma_some_repr_none_spec #s #sz (spec: spec_t s) (repr : repr_t s sz) idx k v 
  : Lemma (requires Some? (lookup_repr repr k) /\
                    None? (lookup_spec spec k))
          (ensures False)
= admit() // PROVEME: hopefully straightforward via a walk of repr

let lemma_some_index_none_repr #s #sz (spec: spec_t s) (repr : repr_t s sz) idx k v 
  : Lemma (requires repr @@ idx == Used k v /\
                    None? (lookup_repr repr k))
          (ensures False)
= admit() // PROVEME: hopefully straightforward via a walk of repr
 

let lemma_clean_upd_lookup_walk #s #sz (spec1 spec2 : spec_t s) (repr1 repr2 : repr_t s sz) idx k v (k':_{k =!= k'})
  : Lemma (requires
      (forall i. i < sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ None? (lookup_repr repr1 k)
      /\ pht_models s sz spec1 repr1
      /\ repr1 @@ idx == Clean
      /\ repr2 == upd_ repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' sz in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
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

let lemma_used_upd_lookup_walk #s #sz (spec1 spec2 : spec_t s) (repr1 repr2 : repr_t s sz) idx k (k':_{k =!= k'}) (v v' : s.valt)
  : Lemma (requires
      (forall i. i < sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ pht_models s sz spec1 repr1
      /\ repr1 @@ idx == Used k v'
      /\ repr2 @@ idx == Used k v
      /\ repr2 == upd_ repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' sz in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
  = if off = sz then ()
    else if (idx' + off) % sz = idx then
      match repr1 @@ idx with
      | Used k'' _ ->
        if k' = k'' then ()
        else aux (off+1)
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

let lemma_del_lookup_walk #s #sz (spec1 spec2 : spec_t s) (repr1 repr2 : repr_t s sz) upos k v (k':_{k =!= k'})
  : Lemma (requires
      (forall i. i < sz /\ i <> upos ==> repr1 @@ i == repr2 @@ i) /\
      pht_models s sz spec1 repr1 /\
      repr1 @@ upos == Used k v /\
      repr2 @@ upos == Zombie /\
      spec2 == spec1 -- k)
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' sz in
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

let lemma_zombie_upd_lookup_walk #s #sz (spec spec' : spec_t s) (repr repr' : repr_t s sz) idx k v (k':_{k =!= k'})
  : Lemma (requires
      (forall i. i < sz /\ i <> idx ==> repr @@ i == repr' @@ i)
      /\ pht_models s sz spec repr
      /\ repr' == upd_ repr idx k v
      /\ repr @@ idx == Zombie
      /\ spec' == spec ++ (k,v))
      (ensures lookup_repr repr k' == lookup_repr repr' k')
= let idx' = canonical_index k' sz in
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

let used_not_by #s #sz (repr : repr_t s sz) (k : s.keyt) (i : nat{i < sz}): prop =
  Used? (repr @@ i) /\ Used?.k (repr @@ i) <> k
  
let all_used_not_by #s #sz (repr : repr_t s sz) (idx1 idx2 : (n:nat{n < sz})) (k : s.keyt) : prop =
  // funny! draw a picture to see why this makes sense
  if idx2 >= idx1 then
    forall i. idx1 <= i /\ i < idx2 ==> used_not_by repr k i
  else (forall i. idx1 <= i ==> used_not_by repr k i)
    /\ (forall i. i < idx2 ==> used_not_by repr k i)

let lemma_walk_from_canonical_all_used #s #sz (repr : repr_t s sz) idx k v 
  : Lemma (requires all_used_not_by repr (canonical_index k sz) idx k
                 /\ repr @@ idx == Used k v)
          (ensures lookup_repr repr k == Some v)
= let cidx = canonical_index k sz in
  let rec aux (off:nat{off < sz})
    : Lemma (requires all_used_not_by repr ((cidx+off)%sz) idx k)
            (ensures walk repr cidx k off == Some v)
            (decreases idx + sz - off)
    = if (cidx+off) % sz = idx then () else begin
       assume (off+1 < sz); // FIXME: prove that we never reach this
       assume (all_used_not_by repr ((cidx+(off+1))%sz) idx k); // FIXME: Modular arith
       aux (off+1)
     end
  in
  aux 0

let lemma_clean_upd #s #sz spec (repr : repr_t s sz) idx k v 
  : Lemma
       (requires pht_models s sz spec repr
              /\ None? (lookup_repr repr k)
              /\ repr @@ idx == Clean
              /\ all_used_not_by repr (canonical_index k sz) idx k)
       (ensures pht_models s sz (spec ++ (k,v)) (upd_ repr idx k v))
  = let spec' = spec ++ (k,v) in
    let repr' = upd_ repr idx k v in
    let aux1 (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_clean_upd_lookup_walk spec spec' repr repr' idx k v k' 
    in
    let aux2 (k':s.keyt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_clean_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':s.keyt) (v':s.valt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k = k' then 
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_clean_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_used_upd #s #sz spec (repr : repr_t s sz) idx k (v v' : s.valt) 
  : Lemma
       (requires pht_models s sz spec repr
              /\ Some? (lookup_repr repr k)
              /\ repr @@ idx == Used k v'
              /\ all_used_not_by repr (canonical_index k sz) idx k)
       (ensures pht_models s sz (spec ++ (k,v)) (upd_ repr idx k v))
  = let spec' = spec ++ (k,v) in
    let repr' = upd_ repr idx k v in
    let aux1 (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v' 
    in
    let aux2 (k':s.keyt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v'
    in
    let aux3 (i':nat{i'<sz}) (k':s.keyt) (v'':s.valt) : Lemma (requires (repr' @@ i' == Used k' v''))
                                                              (ensures (lookup_repr_index repr' k' == Some (v'', i')))
    = if k' = k then begin
        assert (lookup_repr_index repr k == Some (v',idx)); // this assert is necessary
        lemma_walk_from_canonical_all_used repr' idx k v;
        ()
      end
      else
        lemma_used_upd_lookup_walk spec spec' repr repr' idx k k' v v'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_zombie_upd #s #sz spec (repr : repr_t s sz) idx k v 
  : Lemma
       (requires pht_models s sz spec repr
              /\ None? (lookup_repr repr k)
              /\ repr @@ idx == Zombie
              /\ all_used_not_by repr (canonical_index k sz) idx k)
       (ensures pht_models s sz (spec ++ (k,v)) (upd_ repr idx k v))
  = let spec' = spec ++ (k,v) in
    let repr' = upd_ repr idx k v in
    let aux1 (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k' 
    in
    let aux2 (k':s.keyt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':s.keyt) (v':s.valt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k' = k then
        lemma_walk_from_canonical_all_used repr' idx k v
      else
        lemma_zombie_upd_lookup_walk spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let lemma_del #s #sz spec (repr : repr_t s sz) idx k v 
  : Lemma
       (requires pht_models s sz spec repr
              /\ Some? (lookup_repr repr k)
              /\ repr @@ idx == Used k v)
       (ensures pht_models s sz (spec -- k) (del_ repr idx))
  = let spec' = spec -- k in
    let repr' = del_ repr idx in
    let aux1 (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then 
        ()
      else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux2 (k':s.keyt) : Lemma (requires (Some? (lookup_repr repr' k')))
                                 (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    = if k' = k then 
        lemma_some_repr_none_spec spec' repr' idx k v
      else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    let aux3 (i':nat{i'<sz}) (k':s.keyt) (v':s.valt) : Lemma (requires (repr' @@ i' == Used k' v'))
                                                             (ensures (lookup_repr_index repr' k' == Some (v', i')))
    = if k' = k then begin
        assert (lookup_repr_index repr k == Some (v,idx)); // this assert is necessary
        lemma_some_index_none_repr spec' repr' i' k' v'
      end else 
        lemma_del_lookup_walk spec spec' repr repr' idx k v k'
    in
    Classical.forall_intro (Classical.move_requires aux1);
    Classical.forall_intro (Classical.move_requires aux2);
    Classical.forall_intro_3 (Classical.move_requires_3 aux3)

let insert_repr #s #sz (#spec : erased (spec_t s)) (repr : repr_t s sz{pht_models s sz spec repr}) (k : s.keyt) (v : s.valt)
: r':repr_t s sz{pht_models s sz (spec ++ (k,v)) r'}
= let cidx = canonical_index k sz in
  let rec walk_ (off:nat{off <= sz}) (_ : squash (all_used_not_by repr cidx ((cidx+off) % sz) k))
                                     (_ : squash (walk repr cidx k off == lookup_repr repr k))
    : Tot (repr':repr_t s sz{pht_models s sz (spec ++ (k,v)) repr'})
          (decreases sz - off)
    = if off = sz then admit () // FIXME: table full, need side condition
      else
      let idx = (cidx+off) % sz in
      match repr @@ idx with
      | Used k' v' ->
        if k = k'
        then begin
          (**)lemma_used_upd spec repr idx k v v';
          upd_ repr idx k v
        end else begin
          assume (all_used_not_by repr cidx ((cidx+off+1) % sz) k); // FIXME: modular arithmetic?
          walk_ (off+1) () ()
        end
      | Clean ->
        (**)lemma_clean_upd spec repr idx k v;
        upd_ repr idx k v
      | Zombie ->
        match lookup_repr_index repr k with 
          | Some (v_old,i) -> (
            (**)lemma_del spec repr i k v_old;
            // Don't need these asserts
            let cidx = canonical_index k sz in
            assert (all_used_not_by repr cidx idx k);
            assert (if idx >= cidx then i > idx || i <= cidx else i > idx /\ i <= cidx);
            assert (all_used_not_by (del_ repr i) cidx idx k);
            (**)lemma_zombie_upd (spec -- k) (del_ repr i) idx k v;
            upd_ (del_ repr i) idx k v
          )
          | None -> (
            (**)lemma_zombie_upd spec repr idx k v;
            upd_ repr idx k v
          )
  in
  let res = walk_ 0 () () in
  res

let delete_repr #s #sz (#spec : erased (spec_t s)) (repr : repr_t s sz{pht_models s sz spec repr}) (k : s.keyt) (v : s.valt)
: r':repr_t s sz{pht_models s sz (spec -- k) r'}
= let cidx = canonical_index k sz in
  let rec walk_ (off:nat{off <= sz}) (_ : squash (all_used_not_by repr cidx ((cidx+off) % sz) k))
                                     (_ : squash (walk repr cidx k off == lookup_repr repr k))
    : Tot (repr':repr_t s sz{pht_models s sz (spec -- k) repr'})
          (decreases sz - off)
    = if off = sz then admit () // FIXME: table full, need side condition
      else
      let idx = (cidx+off) % sz in
      match repr @@ idx with
      | Used k' v' ->
        if k = k'
        then begin
          (**)lemma_del spec repr idx k v';
          del_ repr idx
        end else begin
          assume (all_used_not_by repr cidx ((cidx+off+1) % sz) k); // FIXME: modular arithmetic?
          walk_ (off+1) () ()
        end
      | _ -> begin 
          assume (all_used_not_by repr cidx ((cidx+off+1) % sz) k); // FIXME: modular arithmetic?
          walk_ (off+1) () ()
        end
  in
  let res = walk_ 0 () () in
  res

let insert #s (ht : pht s) (k : s.keyt) (v : s.valt)
: ht':(pht s){ht'.spec == Ghost.hide (ht.spec ++ (k,v)) }
=
  { ht with spec = Ghost.hide (ht.spec ++ (k,v));
            repr = insert_repr #_ #_ #ht.spec ht.repr k v;
            inv = () }

let delete #s (ht : pht s) (k : s.keyt) (v : s.valt)
: ht':(pht s){ht'.spec == Ghost.hide (ht.spec -- k) }
=
  { ht with spec = Ghost.hide (ht.spec -- k);
            repr = delete_repr #_ #_ #ht.spec ht.repr k v;
            inv = () }
(*
noeq
type table kt vt = {
  sz : pos;
  contents : A.larray (cell kt vt) sz;
  s_contents : Ghost.erased (persistent_table kt vt);
  lk : LK.lock (A.pts_to contents 
  consistent : squash (models contents s_contents)
}

*)
