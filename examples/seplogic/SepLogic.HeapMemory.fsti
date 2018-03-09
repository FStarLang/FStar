module SepLogic.HeapMemory

module S  = FStar.Set
module TS = FStar.TSet

let set  = Set.set
let tset = TSet.set

val heap : Type u#1
val memory : Type u#1

val ref (a:Type0) : Type0
val addr_of : #a:Type0 -> ref a -> GTot nat

val heap_next_addr : heap -> GTot nat
val heap_memory : heap -> GTot memory

let hpred = heap -> Type0
let mpred = memory -> Type0

val disjoint_heaps : heap -> heap -> Type0
val disjoint_memories : memory -> memory -> Type0

val disjoint_heaps_memories (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_memories (heap_memory h0) (heap_memory h1))
          [SMTPat (disjoint_memories (heap_memory h0) (heap_memory h1))]

val emp : memory
val ( |> ) : #a:Type0 -> r:ref a -> x:a -> memory
val ( <*> ) : m0:memory -> m1:memory{disjoint_memories m0 m1} -> memory

val join_tot: h0:heap -> h1:heap{disjoint_heaps h0 h1} -> Tot heap

val sep_join_tot (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1))
          (ensures  (heap_memory (join_tot h0 h1) == ((heap_memory h0) <*> (heap_memory h1))))
          [SMTPat (heap_memory (join_tot h0 h1))]

val hcontains : #a:Type0 -> heap -> ref a -> Type0
val mcontains : #a:Type0 -> memory -> ref a -> Type0

val hcontains_mcontains (#a:Type0) (r:ref a) (h:heap)
  : Lemma (h `hcontains` r <==> (heap_memory h) `mcontains` r)
          [SMTPat ((heap_memory h) `mcontains` r)]

val points_to_mcontains (#a:Type0) (r:ref a) (x:a)
  : Lemma ((r |> x) `mcontains` r)
          [SMTPat ((r |> x) `mcontains` r)]

val sel_tot : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> Tot a
val upd_tot : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> x:a -> Tot heap

val points_to_sel (#a:Type) (r:ref a) (x:a) (h:heap)
  : Lemma (requires (h `hcontains` r /\ heap_memory h == (r |> x)))    //F* doesn't see that (h `hcontains` r) follows from (heap_memory h == (r |> x))
          (ensures  (sel_tot h r == x))
          [SMTPat (heap_memory h);
           SMTPat (r |> x);
           SMTPat (sel_tot h r)]

val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a) (h:heap)
  : Lemma  (requires (h `hcontains` r /\ heap_memory h == (r |> x)))  //F* doesn't see that (h `hcontains` r) follows from (heap_memory h == (r |> x))
           (ensures  (heap_memory ((upd_tot h r v)) == (r |> v)))
           [SMTPat (heap_memory h);
            SMTPat (r |> x);
            SMTPat (upd_tot h r v)]

val hfresh : #a:Type0 -> ref a -> hpred
val mfresh : #a:Type0 -> ref a -> mpred

val hfres_mfresh (#a:Type0) (r:ref a) (h:heap)
  : Lemma (hfresh r h <==> mfresh r (heap_memory h))
          [SMTPat (mfresh r (heap_memory h))]

val alloc : #a:Type0 -> h:heap -> a -> Tot (ref a * heap) 

val alloc_fresh (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,_) = alloc h0 x in
           hfresh r h0)
          [SMTPat (alloc h0 x)]

val alloc_contains (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in 
           h1 `hcontains` r)
          [SMTPat (alloc h0 x)]

val alloc_sel_tot (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in
           sel_tot h1 r == x)
          [SMTPat (alloc h0 x)]

val alloc_emp_points_to (#a:Type0) (h0:heap) (x:a)
  : Lemma (requires (heap_memory h0 == emp))
          (ensures  (let (r,h1) = alloc h0 x in
                     heap_memory h1 == (r |> x)))
          [SMTPat (alloc h0 x)]






(*
//let hpred = heap -> Type0

val emp :heap

// val join_tot: h1:heap -> h2:heap -> Tot heap

// val join_tot_comm (h0:heap) (h1:heap)
//   : Lemma (join_tot h0 h1 == join_tot h1 h0)

val disjoint : #a:Type0 -> #b:Type0 -> ref a -> ref b -> Type0

val disjoint_comm (#a:Type0) (#b:Type0) (r0:ref a) (r1:ref b)
  : Lemma (requires (disjoint r0 r1))
          (ensures  (disjoint r1 r0))

val disjoint_heaps : heap -> heap -> Type0

// val disjoint_heaps_emp (h0 h1:heap)
//   : Lemma (requires (emp h1)) 
//           (ensures  (disjoint_heaps h0 h1))
//           [SMTPat (disjoint_heaps h0 h1); 
//            SMTPat (emp h1)]

val disjoint_heaps_comm (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1))
          (ensures  (disjoint_heaps h1 h0))

val ( |> ) :#a:Type0 -> r:ref a -> x:a -> heap
val ( <*> ) :heap -> heap -> heap

// val ( |> ) : #a:Type0 -> r:ref a -> x:a -> hpred
// val ( <*> ) : hpred -> hpred -> hpred

// val sep_interp (p q:hpred) (h:heap)
//   : Lemma ((p <*> q) h <==> (exists h0 h1. disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ q h1))

val sep_emp (h:heap)
  :Lemma (requires True)
         (ensures (h <*> emp) == h)
         [SMTPat (h <*> emp)]

val sep_comm (h1 h2:heap)
  :Lemma (requires True)
         (ensures ((h1 <*> h2) == (h2 <*> h1)))
	 [SMTPat (h1 <*> h2)]

val sep_assoc (h1 h2 h3:heap)
  :Lemma (requires True)
         (ensures (h1 <*> (h2 <*> h3)) == (h2 <*> (h1 <*> h3)))
	 [SMTPatOr [[SMTPat (h1 <*> (h2 <*> h3))]; [SMTPat (h2 <*> (h1 <*> h3))]]]
         
*)

// val fresh : #a:Type0 -> ref a -> hpred
// val contains : #a:Type0 -> heap -> ref a -> Type0

// val points_to_contains (#a:Type0) (r:ref a) (x:a) (h:heap)
//   : Lemma (requires ((r |> x) h))
//           (ensures  (h `contains` r))
//           [SMTPat ((r |> x) h);
//            SMTPat (h `contains` r)]

// val points_to_ext (#a:Type0) (r:ref a) (x y:a) (h:heap)
//   : Lemma (requires ((r |> x) h /\ (r |> y) h))
//           (ensures  (x == y))

// val points_to_disj (#a:Type0) (#b:Type0) (r:ref a) (s:ref b) (x:a) (y:b) (h:heap)
//     : Lemma (requires ((r |> x <*> s |> y) h))
//             (ensures  (disjoint r s))
//             [SMTPat ((r |> x <*> s |> y) h);
//              SMTPat (disjoint r s)]

// val join_tot_contains (#a:Type0) (r:ref a) (h0 h1:heap) 
//   : Lemma (requires (h1 `contains` r /\ disjoint_heaps h0 h1))
//           (ensures  (contains (join_tot h0 h1) r))
//           [SMTPat (contains (join_tot h0 h1) r)]

// val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a
// val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> x:a -> Tot heap

// val points_to_sel (#a:Type) (r:ref a) (x:a) (h:heap)
//   : Lemma (requires (r |> x) h)
//           (ensures  (sel_tot h r == x))
//           [SMTPat ((r |> x) h);
//            SMTPat (sel_tot h r)]

// val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a) (h:heap)
//   : Lemma  (requires (r |> x) h)
//            (ensures  ((r |> v) (upd_tot h r v)))
//            [SMTPat ((r |> x) h);
//             SMTPat (upd_tot h r v)]

// val restrict: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot heap
// val minus: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot heap

// val minus_not_contains (#a:Type0) (r:ref a) (h:heap)
//   : Lemma (requires (h `contains` r))
//           (ensures  (~((h `minus` r) `contains` r)))
//           [SMTPat ((h `minus` r) `contains` r);
//            SMTPat (h `contains` r)]

// val restrict_points_to (#a:Type0) (r:ref a) (h:heap)
//   : Lemma (requires (h `contains` r))
//           (ensures  (exists x . (r |> x) (restrict h r)))
//           [SMTPat (restrict h r);
//            SMTPat (h `contains` r)]

// val disjoint_heaps_restrict_minus (#a:Type0) (r:ref a) (h:heap)
//   : Lemma (requires (h `contains` r))
//           (ensures  (disjoint_heaps (restrict h r) (minus h r)))
//           [SMTPat (disjoint_heaps (restrict h r) (minus h r))]

// val disjoint_heaps_minus_1 (#a:Type0) (r:ref a) (x:a) (h:heap)
//   : Lemma (requires ((r |> x) h))
//           (ensures  (disjoint_heaps (minus h r) h))
//           [SMTPat (disjoint_heaps (minus h r) h);
//            SMTPat ((r |> x) h)]

// val disjoint_heaps_minus_2 (#a:Type0) (r:ref a) (x0 x1:a) (h0:heap) (h1:heap)
//   : Lemma (requires ((r |> x0) h0 /\ (r |> x1) h1))
//           (ensures  (disjoint_heaps (minus h0 r) h1))
//           [SMTPat (disjoint_heaps (minus h0 r) h1);
//            SMTPat ((r |> x0) h0);
//            SMTPat ((r |> x1) h1)]

// val join_tot_restrict_minus (#a:Type0) (r:ref a) (h:heap)
//   : Lemma (requires (h `contains` r))
//           (ensures  (join_tot (restrict h r) (minus h r) == h))
//           [SMTPat (join_tot (restrict h r) (minus h r))]

// val join_tot_minus_restrict (#a:Type0) (r:ref a) (h:heap)
//   : Lemma (requires (h `contains` r))
//           (ensures  (join_tot (minus h r) h == restrict h r))
//           [SMTPat (join_tot (minus h r) h);
//            SMTPat (restrict h r)]

// val points_to_join_tot_minus (#a:Type0) (r:ref a) (x y:a) (h h':heap)
//   : Lemma (requires ((r |> x) h /\ (r |> y) h'))
//           (ensures  ((r |> y) (join_tot (minus h r) h')))
//           [SMTPat ((r |> x) h);
//            SMTPat ((r |> y) (join_tot (minus h r) h'))]

// val points_to_join_tot_restrict (#a:Type0) (r:ref a) (x y:a) (h h':heap)
//   : Lemma (requires ((r |> x) h /\ (r |> y) h'))
//           (ensures  ((r |> y) (restrict (join_tot (minus h r) h') r)))
//           [SMTPat ((r |> x) h);
//            SMTPat ((r |> y) (restrict (join_tot (minus h r) h') r))]
