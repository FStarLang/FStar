module FStar.SL

open FStar.Heap

(* Assertions in separation logic *)
type predicate = heap -> Type0

type empty_heap (h:heap) = 
  (h == emp)

let singleton_heap (#a:Type0) (h:heap) (r:ref a) : GTot heap =
  restrict h (Set.singleton (addr_of r))

type same (h_1:heap) (h_2:heap) =
  (forall (a:Type0) (r:ref a). (h_1 `contains` r <==> h_2 `contains` r)) /\
  (forall (a:Type0) (r:ref a). (h_1 `contains` r /\ h_2 `contains` r) ==> (sel h_1 r == sel h_2 r))
  
type points_to (#a:Type0) (r:ref a) (v:a) (h:heap) =
  (sel h r == v /\ same h (singleton_heap h r))
  
type disjoint (h_1:heap) (h_2:heap) =
  (forall (a:Type0) (r:ref a). (h_1 `contains` r <==> r `unused_in` h_2)) /\
  (forall (a:Type0) (r:ref a). (h_2 `contains` r <==> r `unused_in` h_1)) 

type star (h_1:heap) (h_2:heap) (p:predicate) (q:predicate) =
  (p h_1 /\ q h_2 /\ disjoint h_1 h_2)

let heap_alloc (h:heap) (v:'a) = alloc h v true

let heap_write (h:heap) (r:ref 'a) (v:'a) = upd h r v

val lemma_frame_rule: h_0:heap -> h_1:heap -> h_2:heap -> p:predicate -> q:predicate -> r:predicate -> Lemma 
  (requires (q h_1) /\ star h_0 h_2 p r) 
  (ensures (star h_1 h_2 q r))
let lemma_frame_rule h_0 h_1 h_2 p q r = admit()
   
val lemma_alloc_rule: #a:Type0 -> v:a -> h:heap -> Lemma
  (requires empty_heap h )
  (ensures (let (r_1, h_1) = (heap_alloc h v) in 
	    points_to r_1 v h_1))
let lemma_alloc_rule #a v h = ()

assume val lemma_disjoint_emp: h:heap -> Lemma
  (requires True)
  (ensures disjoint h emp)

val lemma_sequencing_rule: h_1:heap -> p:predicate -> Lemma
  (requires p h_1)
  (ensures (star h_1 emp p empty_heap))
let lemma_sequencing_rule h_1 p = 
  lemma_disjoint_emp h_1

val lemma_write_rule: #a:Type -> h:heap -> r:ref a -> v:a -> Lemma
  (requires (let v' = sel h r in 
             points_to r v' h))
  (ensures (let h' = heap_write h r v in
	     points_to r v h'))
let lemma_write_rule #a h r v = admit()

let example_1 (h:heap) = 
  let (r, h_1) = heap_alloc h 3 in
  (r, heap_write h_1 r 4)

val lemma_example_1: h:heap -> Lemma
  (requires empty_heap h)
  (ensures (let (r, h_1) = (example_1 h) in 
	    star h_1 emp (points_to r 4) empty_heap)) 
let lemma_example_1 h = 
  let (r, h_1) = example_1 h in
  lemma_sequencing_rule h_1 (points_to r 4)

let example_2 (h_1:heap) (h_2:heap) =
  let (r_1, hh_1) = heap_alloc h_1 3 in
  let (r_2, hh_2) = heap_alloc h_2 9 in 
  let h1 = heap_write hh_1 r_1 4 in
  let h2 = heap_write hh_2 r_2 0 in
  (r_1, r_2, h1, h2)

val lemma_star_is_assoc: h_1:heap -> h_2:heap -> p:predicate -> q:predicate -> Lemma
  (requires star h_1 h_2 p q)
  (ensures star h_2 h_1 q p)
let lemma_star_is_assoc = admit()

val lemma_example_2: h_1:heap -> h_2:heap -> Lemma
  (requires empty_heap h_1 /\ empty_heap h_2)
  (ensures (let (r_1, r_2, h1, h2) = example_2 h_1 h_2 in
	    star h1 h2 (points_to r_1 4) (points_to r_2 0)))
let lemma_example_2 h_1 h_2 =
  let (r_1, r_2, h1, h2) = example_2 h_1 h_2 in
  lemma_alloc_rule 3 h_1 ;
  let (_ , h11) = (heap_alloc h_1 3) in
  lemma_sequencing_rule h11 (points_to r_1 3);
  let (_, h22) = (heap_alloc h_2 4) in
  lemma_alloc_rule 4 h_2;
  lemma_star_is_assoc h11 emp (points_to r_1 3) (empty_heap);
  lemma_frame_rule emp h22 h11 (empty_heap) (points_to r_2 4) (points_to r_1 3)
