module SepLogic.Heap

module S  = FStar.Set
module TS = FStar.TSet

let set  = Set.set

(* heaps, memories, and operations on them *)

val heap : Type u#1
val memory : Type u#1
val defined : memory -> Type0

val emp : memory

val lemma_defined_emp (u:unit) 
  : Lemma (defined emp)

assume Emp_defined_axiom : defined emp

val ref (a:Type0) : Type0
val addr_of : #a:Type0 -> ref a -> GTot nat
val heap_memory : heap -> GTot memory

val disjoint_heaps : heap -> heap -> Type0
val disjoint_memories : memory -> memory -> Type0

val join : h0:heap -> h1:heap{disjoint_heaps h0 h1} -> Tot heap

val ( |> ) : #a:Type0 -> r:ref a -> x:a -> Tot memory
val ( <*> ) : m0:memory -> m1:memory -> GTot memory

val split_heap : (m0:memory) 
              -> (m1:memory)
              -> (h:heap{defined (m0 <*> m1) /\ heap_memory h == (m0 <*> m1)}) 
              -> heap * heap

val hcontains : #a:Type0 -> heap -> ref a -> Type0
val mcontains : #a:Type0 -> memory -> ref a -> Type0

val sel : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> Tot a
val upd : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> x:a -> Tot heap

val fresh : #a:Type0 -> ref a -> heap -> Type0
val alloc : #a:Type0 -> h:heap -> a -> Tot (ref a * heap) 

val addrs_in : memory -> Set.set nat

(* disjoint_heaps and disjoint_memories *)

val lemma_disjoint_heaps_comm (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_heaps h1 h0)

val lemma_disjoint_memories_emp (m:memory)
  : Lemma (requires (defined m))
          (ensures  (disjoint_memories m emp))
          [SMTPat (disjoint_memories m emp)]

val lemma_disjoint_memories_comm (m0 m1:memory)
  : Lemma (requires (defined m0 /\ defined m1))
          (ensures  (disjoint_memories m0 m1 <==> disjoint_memories m1 m0))

val lemma_disjoint_heaps_memories (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_memories (heap_memory h0) (heap_memory h1))
          [SMTPat (disjoint_memories (heap_memory h0) (heap_memory h1))]

val lemma_sep_disjoint_memories (m0 m1:memory) 
  : Lemma (disjoint_memories m0 m1 <==> defined (m0 <*> m1))
          [SMTPat (disjoint_memories m0 m1);
           SMTPat (defined (m0 <*> m1))]

(* join *)

val lemma_join_comm (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ disjoint_heaps h1 h0))
          (ensures  (join h0 h1 == join h1 h0))

(* <*> *)

val lemma_sep_unit (m:memory)
  : Lemma ((m <*> emp) == m)
          [SMTPat (m <*> emp)]

val lemma_sep_comm (m0 m1:memory)
  : Lemma ((m0 <*> m1) == (m1 <*> m0))
          
val lemma_sep_assoc (m0 m1 m2:memory)
  : Lemma ((m0 <*> (m1 <*> m2)) == ((m0 <*> m1) <*> m2))
         [SMTPatOr [[SMTPat ((m0 <*> (m1 <*> m2)))];
	            [SMTPat ((m0 <*> m1) <*> m2)]]]

(* heap_memory *)

val lemma_sep_join (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1))
          (ensures  (heap_memory (join h0 h1) == ((heap_memory h0) <*> (heap_memory h1))))
          [SMTPat (heap_memory (join h0 h1))]

(* defined *)

val lemma_points_to_defined (#a:Type0) (r:ref a) (x:a)
  : Lemma (defined (r |> x))
          [SMTPat (defined (r |> x))]

val lemma_sep_defined (m0 m1:memory)
  : Lemma (defined (m0 <*> m1) <==> (defined m0 /\ defined m1 /\ Set.disjoint (addrs_in m0) (addrs_in m1)))
 	  [SMTPat (defined (m0 <*> m1))]

val lemma_heap_memory_defined (h:heap)
  : Lemma (defined (heap_memory h))
          [SMTPat (defined (heap_memory h))]

(* split_heap *)

val lemma_split_heap_disjoint (m0 m1:memory) (h:heap)
  : Lemma (requires (defined (m0 <*> m1) /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     disjoint_heaps h0 h1))
          [SMTPat (split_heap m0 m1 h)]

val lemma_split_heap_join (m0 m1:memory) (h:heap)
  : Lemma (requires (defined (m0 <*> m1) /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     h == join h0 h1))
          [SMTPat (split_heap m0 m1 h)]

val lemma_split_heap_memories (m0 m1:memory) (h:heap)
  : Lemma (requires (defined (m0 <*> m1) /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in
                     heap_memory h0 == m0 /\ heap_memory h1 == m1))
          [SMTPat (split_heap m0 m1 h)]

(* hcontains and mcontains *)

val lemma_hcontains_mcontains (#a:Type0) (r:ref a) (h:heap)
  : Lemma (h `hcontains` r <==> (heap_memory h) `mcontains` r)
          [SMTPat ((heap_memory h) `mcontains` r)]

val lemma_points_to_mcontains (#a:Type0) (r:ref a) (x:a)
  : Lemma ((r |> x) `mcontains` r)
          [SMTPat ((r |> x) `mcontains` r)]

(* sel, upd, and |> *)

val lemma_points_to_sel (#a:Type) (r:ref a) (x:a) (h:heap)
  : Lemma (requires (h `hcontains` r /\ heap_memory h == (r |> x)))
          (ensures  (sel h r == x))
          [SMTPat (heap_memory h);
           SMTPat (r |> x);
           SMTPat (sel h r)]

val lemma_points_to_upd (#a:Type) (r:ref a) (x:a) (v:a) (h:heap)
  : Lemma  (requires (h `hcontains` r /\ heap_memory h == (r |> x)))
           (ensures  (heap_memory (upd h r v) == (r |> v)))
           [SMTPat (heap_memory h);
            SMTPat (r |> x);
            SMTPat (upd h r v)]

(* alloc and fresh *)

val lemma_alloc_fresh (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,_) = alloc h0 x in
           fresh r h0)
          [SMTPat (alloc h0 x)]

val lemma_alloc_contains (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in 
           h1 `hcontains` r)
          [SMTPat (alloc h0 x)]

val lemma_alloc_sel (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in
           sel h1 r == x)
          [SMTPat (alloc h0 x)]

val lemma_alloc_emp_points_to (#a:Type0) (h0:heap) (x:a)
  : Lemma (requires (heap_memory h0 == emp))
          (ensures  (let (r,h1) = alloc h0 x in
                     heap_memory h1 == (r |> x)))
          [SMTPat (alloc h0 x)]

(* addrs_in *)

val lemma_addrs_in_emp (u:unit) 
  : Lemma (Set.equal (addrs_in emp) (Set.empty))

assume Addrs_in_emp_axiom: Set.equal (addrs_in emp) (Set.empty)

val lemma_addrs_in_points_to (#a:Type) (r:ref a) (x:a)
  : Lemma (Set.equal (addrs_in (r |> x)) (Set.singleton (addr_of r)))
          [SMTPat (addrs_in (r |> x))]

val lemma_addrs_in_join (m0 m1:memory)
  : Lemma (requires (defined (m0 <*> m1)))
          (ensures  (Set.equal (addrs_in (m0 <*> m1)) (Set.union (addrs_in m0) (addrs_in m1))))
          [SMTPat (addrs_in (m0 <*> m1))]
