module SepLogic.Heap

module S  = FStar.Set
module TS = FStar.TSet

let set  = Set.set
let tset = TSet.set

val heap : Type u#1
val memory : Type u#1

val emp : memory

val ref (a:Type0) : Type0
val addr_of : #a:Type0 -> ref a -> GTot nat

val heap_memory : heap -> GTot memory

let hpred = heap -> Type0
let mpred = memory -> Type0

val disjoint_heaps : heap -> heap -> Type0
val disjoint_memories : memory -> memory -> Type0

val disjoint_heaps_comm (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_heaps h1 h0)

val disjoint_memories_emp (m:memory)
  : Lemma (disjoint_memories m emp)
          [SMTPat (disjoint_memories m emp)]

val disjoint_memories_comm (m0 m1:memory)
  : Lemma (disjoint_memories m0 m1 <==> disjoint_memories m1 m0)

val disjoint_heaps_memories (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_memories (heap_memory h0) (heap_memory h1))
          [SMTPat (disjoint_memories (heap_memory h0) (heap_memory h1))]

val join : h0:heap -> h1:heap{disjoint_heaps h0 h1} -> Tot heap

val join_comm (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ disjoint_heaps h1 h0))
          (ensures  (join h0 h1 == join h1 h0))

val ( |> ) : #a:Type0 -> r:ref a -> x:a -> memory
val ( <*> ) : m0:memory -> m1:memory{disjoint_memories m0 m1} -> memory

val sep_join (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1))
          (ensures  (heap_memory (join h0 h1) == ((heap_memory h0) <*> (heap_memory h1))))
          [SMTPat (heap_memory (join h0 h1))]

val split_heap : (m0:memory) 
              -> (m1:memory{disjoint_memories m0 m1})
              -> (h:heap{heap_memory h == (m0 <*> m1)}) 
              -> heap * heap

val split_heap_disjoint (m0 m1:memory) (h:heap)
  : Lemma (requires (disjoint_memories m0 m1 /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     disjoint_heaps h0 h1))
          [SMTPat (split_heap m0 m1 h)]

val split_heap_join (m0 m1:memory) (h:heap)
  : Lemma (requires (disjoint_memories m0 m1 /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     h == join h0 h1))
          [SMTPat (split_heap m0 m1 h)]

val split_heap_memories (m0 m1:memory) (h:heap)
  : Lemma (requires (disjoint_memories m0 m1 /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     heap_memory h0 == m0 /\ heap_memory h1 == m1))
          [SMTPat (split_heap m0 m1 h)]

val points_to_addr_of_disjoint (#a:Type0) (#b:Type0) (r:ref a) (s:ref b) (x:a) (y:b)
  : Lemma (requires (addr_of r =!= addr_of s))
          (ensures  (disjoint_memories (r |> x) (s |> y)))
          [SMTPat (disjoint_memories (r |> x) (s |> y))]

val hcontains : #a:Type0 -> heap -> ref a -> Type0
val mcontains : #a:Type0 -> memory -> ref a -> Type0

val hcontains_mcontains (#a:Type0) (r:ref a) (h:heap)
  : Lemma (h `hcontains` r <==> (heap_memory h) `mcontains` r)
          [SMTPat ((heap_memory h) `mcontains` r)]

val points_to_mcontains (#a:Type0) (r:ref a) (x:a)
  : Lemma ((r |> x) `mcontains` r)
          [SMTPat ((r |> x) `mcontains` r)]

val sel : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> Tot a
val upd : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> x:a -> Tot heap

val points_to_sel (#a:Type) (r:ref a) (x:a) (h:heap)
  : Lemma (requires (h `hcontains` r /\ heap_memory h == (r |> x)))    //F* doesn't see that (h `hcontains` r) follows from (heap_memory h == (r |> x))
          (ensures  (sel h r == x))
          [SMTPat (heap_memory h);
           SMTPat (r |> x);
           SMTPat (sel h r)]

val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a) (h:heap)
  : Lemma  (requires (h `hcontains` r /\ heap_memory h == (r |> x)))  //F* doesn't see that (h `hcontains` r) follows from (heap_memory h == (r |> x))
           (ensures  (heap_memory ((upd h r v)) == (r |> v)))
           [SMTPat (heap_memory h);
            SMTPat (r |> x);
            SMTPat (upd h r v)]

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

val alloc_sel (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in
           sel h1 r == x)
          [SMTPat (alloc h0 x)]

val alloc_emp_points_to (#a:Type0) (h0:heap) (x:a)
  : Lemma (requires (heap_memory h0 == emp))
          (ensures  (let (r,h1) = alloc h0 x in
                     heap_memory h1 == (r |> x)))
          [SMTPat (alloc h0 x)]





