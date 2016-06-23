(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi IntLib --admit_fsi Parameters --verify_module FsumWide --z3timeout 15;
  other-files:FStar.Classical.fst FStar.PredicateExtensionality.fst FStar.Set.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst
  --*)

module FsumLemmas

open FStar.Ghost

val helper_lemma_1:
  a_idx:nat -> i:nat -> len:nat -> x:erased nat -> 
  Lemma (requires (i < len /\ a_idx + len <= reveal x)) (ensures (a_idx+i < reveal x))
let helper_lemma_1 a_idx i len v = ()  

val helper_lemma_2_1:
  a:int -> b:int -> c:int -> d:int ->
  Lemma ((a+b)+(c+d) = a + b + c + d)
let helper_lemma_2_1 a b c d = ()

val helper_lemma_2_2:
  a:int -> b:int -> c:int -> d:int ->
  Lemma (a+c+b+d = a + b + c + d)
let helper_lemma_2_2 a b c d = ()

val helper_lemma_2:
  a:int -> b:int -> c:int -> d:int ->
  Lemma ((a+b)+(c+d) = (a + c) + (b + d))
let helper_lemma_2 a b c d = 
  ()

val helper_lemma_3: ctr:nat -> len:nat{len > ctr} ->
  Lemma (ensures (forall (i:nat). (i >= ctr /\ i < len) ==> (i = ctr \/ (i >= ctr+1 /\ i < len))))
let helper_lemma_3 ctr len = ()

val auxiliary_lemma_0: a:nat -> b:nat -> Lemma (requires (a>=b/\a-b<>0)) (ensures (a>=b+1))
let auxiliary_lemma_0 a b = ()

val auxiliary_lemma_1: len:nat -> ctr:nat{ctr < len} -> 
  Lemma 
    (forall (i:nat). ((i>=ctr+1 /\ i < len) \/ i = ctr) ==> (i >= ctr /\ i < len))
let auxiliary_lemma_1 len ctr = ()

val auxiliary_lemma_2: idx:nat -> ctr:nat -> len:nat{ctr<len} -> len_a:nat{idx+len<=len_a} ->
  Lemma (ensures (forall (i:nat). (i>=ctr+1 /\ i < len) ==> (i<>ctr/\ i < len_a - idx)))
let auxiliary_lemma_2 idx ctr len len_a = ()    

val auxiliary_lemma_3: idx:nat -> ctr:nat -> len:nat{ctr<len} -> len_a:nat{idx+len<=len_a} -> f:(i:nat{i<>ctr/\i<len_a-idx} -> GTot bool) ->
  Lemma 
    (requires (forall (i:nat). (i<>ctr/\ i < len_a - idx) ==> f i))
    (ensures (forall (i:nat). (i>=ctr+1 /\ i < len) ==> f i))
let auxiliary_lemma_3 idx ctr len len_a f = ()    

val auxiliary_lemma_4: len:nat -> ctr:nat{ctr < len} -> f:(i:nat{(i>=ctr+1 /\ i < len)\/i=ctr} -> GTot bool) ->
  Lemma 
    (requires ((forall (i:nat). (i>=ctr+1 /\ i < len) ==> f i) /\ f ctr))
    (ensures (forall (i:nat). (i >= ctr /\ i < len) ==> f i))
let auxiliary_lemma_4 len ctr f = ()    

val auxiliary_lemma_5: ctr:nat -> len:erased nat -> a_idx:nat ->
  Lemma
    (forall (i:int). ((i>=a_idx /\ i <> ctr+a_idx /\ i < reveal len) <==> (i-a_idx >=0 /\ i-a_idx <> ctr /\ i-a_idx < reveal len-a_idx)) /\ ((i-a_idx)+a_idx) = i /\ ((i+a_idx)-a_idx = i))
let auxiliary_lemma_5 ctr len a_idx = ()

val auxiliary_lemma_6: len:nat -> ctr:nat -> Lemma (requires (len-ctr<>0/\len>=ctr)) (ensures (ctr+1<=len))
let auxiliary_lemma_6 len ctr = ()

val auxiliary_lemma_7: ctr:nat -> len:nat{ctr < len} -> Lemma (forall (i:nat). (i >= ctr /\ i < len) ==> (i = ctr \/ (i >= ctr+1 /\ i < len)))
let auxiliary_lemma_7 ctr len = ()
