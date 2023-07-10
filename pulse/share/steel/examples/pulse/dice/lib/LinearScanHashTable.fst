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
  valt : Type;
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

let rec walk #s #sz (repr : repr_t s sz) (idx:nat) (k : s.keyt) (off:nat{off <= sz}) : Tot (option s.valt) (decreases sz - off) =
  if off = sz then None
  else
  match repr @@ ((idx + off) % sz) with
  | Clean -> None
  | Used k' v ->
    if k = k'
    then Some v
    else walk repr idx k (off+1)
  | Zombie ->
    walk repr idx k (off + 1)

let lookup_repr (#s : pht_sig) #sz (repr : repr_t s sz) (k : s.keyt) : option s.valt =
  let idx = canonical_index k sz in
  walk repr idx k 0

// FIXME: missing a bunch more interesting properties
type pht_models (s : pht_sig) (sz : pos)
  (spec : spec_t s)
  (repr : Seq.lseq (cell s.keyt s.valt) sz)
: Type0
=    (forall k. Some? (lookup_spec spec k) ==> lookup_repr repr k == lookup_spec spec k) // spec `submap` repr
  ///\ (forall k. Some? (lookup_repr repr k) ==> lookup_repr repr k == lookup_spec spec k) // repr `submap` spec
  // ALSO MISSING: only one occurrence of any given key
    // .... or... that if (k,v) is in the sequence at index i then
    // lookup_repr finds index i.
    
    // e.g.
    // lookup_repr : repr -> k -> option v 
    // lookup_repr_index : repr -> k -> option (v & nat)
    //   forall i. repr @@ i == (k, _)   ==>    lookup_repr_index repr k == Some (_, i)

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
  
let upd1 #s #sz (repr : repr_t s sz) idx k v : repr_t s sz =
  Seq.upd repr idx (Used k v)
  
let clean_upd_lookup_walk #s #sz (spec1 spec2 : spec_t s) (repr1 repr2 : repr_t s sz) idx k v (k':_{k =!= k'})
  : Lemma (requires
      (forall i. i < sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ None? (lookup_repr repr1 k)
      /\ pht_models s sz spec1 repr1
      /\ repr1 @@ idx == Clean
      // /\ repr2 @@ idx == Used k v // reundandant, given precondition below
      /\ repr2 == upd1 repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' sz in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
  =
    if off = sz then ()
    else if (idx' + off) % sz = idx then
      begin 
        assert (None? (walk repr1 idx' k' off));
        assert (None? (lookup_repr repr1 k'));
        assert (None? (lookup_spec spec1 k'));
        assert (None? (lookup_spec spec2 k'));
        assume (None? (lookup_repr repr2 k')); // FIXME: requires backwards containment / no dups in pht_models
        assert (None? (walk repr2 idx' k' off));
        ()
      end
    else begin
      match repr1 @@ ((idx' + off) % sz) with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then
          ()
        else
        if k = k'' then (
          // NOTE: this requires the backwards containment in
          // pht_models: otherwise there may very well be
          // extraneous Used k v cells in repr1.

          // Not only that, but even with that property, we would
          // not be ruling out any other extraneous duplicate occurrence
          // of k within the sequence. So we cannot prove this without
          // more hypotheses.
          admit()
        )
        else aux (off+1)
      | Zombie ->
        aux (off+1)
    end
  in
  aux 0

let used_upd_lookup_walk #s #sz (spec1 spec2 : spec_t s) (repr1 repr2 : repr_t s sz) idx k (k':_{k =!= k'}) (v v' : s.valt)
  : Lemma (requires
      (forall i. i < sz /\ i <> idx ==> repr1 @@ i == repr2 @@ i)
      /\ pht_models s sz spec1 repr1
      /\ repr1 @@ idx == Used k v'
      /\ repr2 @@ idx == Used k v // reundandant, given precondition below
      /\ repr2 == upd1 repr1 idx k v
      /\ spec2 == spec1 ++ (k,v))
      (ensures lookup_repr repr1 k' == lookup_repr repr2 k')
= let idx' = canonical_index k' sz in
  let rec aux (off:nat{off <= sz}) : Lemma
        (requires walk repr1 idx' k' off == lookup_repr repr1 k'
               /\ walk repr2 idx' k' off == lookup_repr repr2 k')
        (ensures walk repr1 idx' k' off == walk repr2 idx' k' off)
        (decreases sz - off) 
  =
    if off = sz then ()
    else if (idx' + off) % sz = idx then
      match repr1 @@ idx with
      | Used k'' _ ->
        if k' = k'' then
          begin
            assert (k =!= k');
            assert (k =!= k'');
            assert (repr1 @@ idx == Used k'' v');
            assert (repr1 @@ idx == Used k v');
            assert (k == k'');
            ()
          end
        else
        if k = k'' then (
          // NOTE: this requires the backwards containment in
          // pht_models: otherwise there may very well be
          // extraneous Used k v cells in repr1.

          // Not only that, but even with that property, we would
          // not be ruling out any other extraneous duplicate occurrence
          // of k within the sequence. So we cannot prove this without
          // more hypotheses.
          admit()
        )
        else aux (off+1)
    else begin
      match repr1 @@ ((idx' + off) % sz) with
      | Clean -> ()
      | Used k'' v'' ->
        if k' = k'' then
          ()
        else
        if k = k'' then (
          // NOTE: this requires the backwards containment in
          // pht_models: otherwise there may very well be
          // extraneous Used k v cells in repr1.

          // Not only that, but even with that property, we would
          // not be ruling out any other extraneous duplicate occurrence
          // of k within the sequence. So we cannot prove this without
          // more hypotheses.
          admit()
        )
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
  else
       (forall i. idx1 <= i ==> used_not_by repr k i)
    /\ (forall i. i < idx2 ==> used_not_by repr k i)

let lem_walk_from_canonical_all_used #s #sz
   (repr : repr_t s sz) idx k v 
  : Lemma (requires all_used_not_by repr (canonical_index k sz) idx k
                 /\ repr @@ idx == Used k v)
          (ensures lookup_repr repr k == Some v)
= 
  let cidx = canonical_index k sz in
  let rec aux (off:nat{off < sz})
    : Lemma (requires all_used_not_by repr ((cidx+off)%sz) idx k)
            (ensures walk repr cidx k off == Some v)
            (decreases idx + sz - off)
    = if (cidx+off) % sz = idx then () else begin
       assert (used_not_by repr k ((cidx+off)%sz));
       assume (off+1 < sz); // FIXME: prove that we never reach this
       assume (all_used_not_by repr ((cidx+(off+1))%sz) idx k); // FIXME: Modular arith
       aux (off+1)
     end
  in
  aux 0

let clean_upd #s #sz spec (repr : repr_t s sz{pht_models s sz spec repr}) idx k v 
  : Lemma
       (requires None? (lookup_repr repr k)
              /\ repr @@ idx == Clean
              /\ all_used_not_by repr (canonical_index k sz) idx k)
       (ensures pht_models s sz (spec ++ (k,v)) (upd1 repr idx k v))
  = let spec' = spec ++ (k,v) in
    let repr' = upd1 repr idx k v in
    let aux (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    =
      if k' = k then
        lem_walk_from_canonical_all_used repr' idx k v
      else (
        assert (Some? (lookup_spec spec k'));
        let Some v' = lookup_spec spec k' in
        assert (lookup_repr repr k' == Some v');
        assert (lookup_spec spec' k' == Some v');
        clean_upd_lookup_walk spec spec' repr repr' idx k v k';
        ()
      )
    in
    Classical.forall_intro (Classical.move_requires aux)

let used_upd #s #sz spec (repr : repr_t s sz{pht_models s sz spec repr}) idx k (v v' : s.valt) 
  : Lemma
       (requires Some? (lookup_repr repr k)
              /\ repr @@ idx == Used k v'
              /\ all_used_not_by repr (canonical_index k sz) idx k)
       (ensures pht_models s sz (spec ++ (k,v)) (upd1 repr idx k v))
  = let spec' = spec ++ (k,v) in
    let repr' = upd1 repr idx k v in
    let aux (k':s.keyt) : Lemma (requires (Some? (lookup_spec spec' k')))
                                (ensures (lookup_repr repr' k' == lookup_spec spec' k'))
    =
      if k' = k then
        lem_walk_from_canonical_all_used repr' idx k v
      else (
        assert (Some? (lookup_spec spec k'));
        let Some v_ = lookup_spec spec k' in
        assert (lookup_repr repr k' == Some v_);
        assert (lookup_spec spec' k' == Some v_);
        used_upd_lookup_walk spec spec' repr repr' idx k k' v v';
        ()
      )
    in
    Classical.forall_intro (Classical.move_requires aux)

let insert_repr #s #sz (#spec : erased (spec_t s)) (repr : repr_t s sz{pht_models s sz spec repr}) (k : s.keyt) (v : s.valt)
: r':repr_t s sz{pht_models s sz (spec ++ (k,v)) r'}
=
  let cidx = canonical_index k sz in
  let rec walk_ (off:nat{off <= sz}) (_ : squash (all_used_not_by repr cidx ((cidx+off) % sz) k))
                                     (_ : squash (walk repr cidx k off == lookup_repr repr k))
    : Tot (repr':repr_t s sz{pht_models s sz (spec ++ (k,v)) repr'})
          (decreases sz - off)
    =
      if off = sz then admit() // FIXME: table full, need side condition
      else
      let idx = (cidx+off) % sz in
      match repr @@ idx with
      | Used k' v' ->
        if k = k'
        then begin
          // Need different lemma, rewriting existing slot: this should be
          // similar to the Clean case, where we accumulate a all_used_not_by proof
          // and then use it to show that the two walks are the same.
          assert (repr @@ idx == Used k' v');
          used_upd spec repr idx k v v';
          upd1 repr idx k v
        end else begin 
          assert (all_used_not_by repr cidx ((cidx+off) % sz) k);
          assert (used_not_by repr k idx);
          assume (all_used_not_by repr cidx ((cidx+off+1) % sz) k); // FIXME: modular arithmetic?
          walk_ (off+1) () ()
        end

      | Clean ->
        clean_upd spec repr idx k v;
        upd1 repr idx k v

      | Zombie ->
        // needs separate lemma: the logic is tricky, we need to 
        // insert here, and keep going to find an older occurrence
        // of the key and delete it (mark it as a zombie)
        // e.g., assume A and C hash to the same bucket and the table is:
        //
        //  A
        //  zombie
        //  C
        //
        // And we try to insert C: we cannot just put it in the zombie,
        // we need to delete the one below too.
        admit ()
  in
  let res = walk_ 0 () () in
  res

let insert #s (ht : pht s) (k : s.keyt) (v : s.valt)
: ht':(pht s){ht'.spec == Ghost.hide (ht.spec ++ (k,v)) }
=
  { ht with spec = Ghost.hide (ht.spec ++ (k,v));
            repr = insert_repr #_ #_ #ht.spec ht.repr k v;
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
