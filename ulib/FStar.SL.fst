module FStar.SL

open FStar.Heap

type predicate = heap -> Type0

type empty_heap (h:heap) = 
  (h == emp)

let singleton_heap (#a:Type0) (h:heap) (r:ref a) : GTot heap =
  restrict h (Set.singleton (addr_of r))

type same (h1:heap) (h2:heap) =
  (forall (a:Type0) (r:ref a). (h1 `contains` r) <==> (h2 `contains` r)) /\
  (forall (a:Type0) (r:ref a). ((h1 `contains` r) /\ (h2 `contains` r)) ==> (sel h1 r == sel h2 r))

type points_to (#a:Type0) (r:ref a) (v:a) (h:heap) =
  ((sel h r == v) /\ (same h (singleton_heap h r))) 
  
type star (p:predicate) (q:predicate) (h:heap) =
  (exists h1 h2. (p h1) /\ (q h2) /\ (disjoint h1 h2) /\ (same h (join h1 h2)))

val lemma_frame_rule: p:predicate -> q:predicate -> r:predicate -> h0:heap -> h1:heap -> h2:heap
  -> Lemma (requires (p h0 ==> q h1) /\ (disjoint h1 h2) /\ (p h0) /\ (r h2))
           (ensures (star p r (join h0 h2)) ==> (star q r (join h1 h2)))
let lemma_frame_rule p q r h0 h1 h2 = ()

val lemma_alloc_rule: #a:Type0 -> h:heap -> v:a
  -> Lemma (requires (empty_heap h))
           (ensures (let (r, h') = alloc h v true in
		     points_to r v h'))
let lemma_alloc_rule #a h v = ()	   

val lemma_sequencing_rule: p:predicate -> h:heap
 -> Lemma (requires (p h) /\ disjoint h emp)
          (ensures (star p (empty_heap) (join h emp)))
let lemma_sequencing_rule p h = ()
