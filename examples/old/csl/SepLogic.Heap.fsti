(*
   Copyright 2008-2018 Microsoft Research

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
module SepLogic.Heap

module S  = FStar.Set

module OS = FStar.OrdSet

let addrs = OS.ordset nat (fun n m -> n <= m)

unfold let disjoint_addrs (s0 s1:addrs) = OS.intersect s0 s1 = OS.empty

let set  = S.set

(* heaps, memories, and operations on them *)

val heap : Type u#1
val memory : Type u#1
val defined : memory -> Type0

val emp : memory

val ref (a:Type0) : Type0
val addr_of : #a:Type0 -> ref a -> Tot nat
val heap_memory : heap -> Tot memory

val disjoint_heaps : heap -> heap -> Type0
val join : h0:heap -> h1:heap{disjoint_heaps h0 h1} -> Tot heap

val ( |> ) : #a:Type0 -> r:ref a -> x:a -> Tot memory
val ( <*> ) : m0:memory -> m1:memory -> Tot memory

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
val dealloc : #a:Type0 -> h:heap -> r:ref a{h `hcontains` r} -> Tot heap

val addrs_in : memory -> Tot addrs
val addr_to_ref : m:memory{defined m} -> r:nat{OS.mem r (addrs_in m)} -> a:Type0 & ref a

let fresh_or_old' (h0 h1:heap) (m_old m_fresh:memory) = 
    heap_memory h1 == (m_old <*> m_fresh) /\ 
    OS.subset (addrs_in m_old) (addrs_in (heap_memory h0)) /\
    (forall a (r:ref a) . OS.mem (addr_of r) (addrs_in m_fresh) ==> fresh r h0) /\ 
    (forall a (r:ref a) . fresh r h1 ==> fresh r h0)

let fresh_or_old (h0 h1:heap) =
  exists m_old m_fresh . fresh_or_old' h0 h1 m_old m_fresh

let same_freshness (h0 h1:heap) =
  forall a (r:ref a) . fresh r h0 <==> fresh r h1

val restrict_memory : rs:addrs
                   -> m:memory{defined m}
                   -> Tot memory
val complement_memory : rs:addrs
                     -> m:memory{defined m}
                     -> Tot memory

(* disjoint_heaps *)

val lemma_disjoint_heaps_comm (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_heaps h1 h0)

val lemma_sep_defined_disjoint_heaps (h0 h1:heap)
  : Lemma ((defined ((heap_memory h0) <*> (heap_memory h1))) <==> (disjoint_heaps h0 h1))
          [SMTPat (defined ((heap_memory h0) <*> (heap_memory h1)))]

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
          [SMTPat (m0 <*> m1);         //Temporary SMTPats until the canonizer is ready
           SMTPat (m1 <*> m0)]
          
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

val lemma_emp_defined (u:unit) 
  : Lemma (defined emp)

assume Emp_defined_axiom : defined emp

val lemma_points_to_defined (#a:Type0) (r:ref a) (x:a)
  : Lemma (defined (r |> x))
          [SMTPat (defined (r |> x))]

val lemma_sep_defined (m0 m1:memory)
  : Lemma (defined (m0 <*> m1) <==> (defined m0 /\ defined m1 /\ disjoint_addrs (addrs_in m0) (addrs_in m1)))
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

val lemma_split_heap_fresh (m0 m1:memory) (h:heap)
  : Lemma (requires (defined (m0 <*> m1) /\ heap_memory h == (m0 <*> m1)))
          (ensures  (let (h0,h1) = split_heap m0 m1 h in 
                     (forall a (r:ref a) . fresh r h0 <==> fresh r h1)))
          [SMTPat (split_heap m0 m1 h)]

(* hcontains and mcontains *)

val lemma_hcontains_mcontains (#a:Type0) (r:ref a) (h:heap)
  : Lemma (h `hcontains` r <==> (heap_memory h) `mcontains` r)
          [SMTPat (h `hcontains` r)]

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

val lemma_alloc_heap_memory (#a:Type0) (h0:heap) (x:a)
  : Lemma (let (r,h1) = alloc h0 x in
           heap_memory h1 == (heap_memory h0 <*> (r |> x)))
          [SMTPat (alloc h0 x)]

val lemma_fresh_in_complement (#a:Type0) (r:ref a) (h:heap)
  : Lemma (requires (fresh r h))
          (ensures  (not (OS.mem (addr_of r) (addrs_in (heap_memory h)))))
          [SMTPat (fresh r h);
           SMTPat (heap_memory h)]

val lemma_fresh_join (#a:Type0) (r:ref a) (h0 h1:heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ fresh r h0 /\ fresh r h1))
          (ensures  (fresh r (join h0 h1)))
          [SMTPat (fresh r (join h0 h1))]

(* dealloc *)

val lemma_dealloc_contains (#a:Type0) (h0:heap) (r:ref a)
  : Lemma (requires (h0 `hcontains` r))
          (ensures  (~((dealloc h0 r) `hcontains` r)))
          [SMTPat ((dealloc h0 r) `hcontains` r)]

val lemma_points_to_dealloc (#a:Type0) (h0:heap) (r:ref a)
  : Lemma (requires ((exists x . heap_memory h0 == (r |> x)) /\ h0 `hcontains` r))
          (ensures  (heap_memory (dealloc h0 r) == emp))
          [SMTPat (heap_memory (dealloc h0 r))]

(* addrs_in *)

val lemma_addrs_in_emp (u:unit) 
  : Lemma (addrs_in emp = OS.empty)

assume Addrs_in_emp_axiom: OS.equal (addrs_in emp) (OS.empty)

val lemma_addrs_in_disjoint_heaps (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> disjoint_addrs (addrs_in (heap_memory h0)) (addrs_in (heap_memory h1)))
          [SMTPat (disjoint_addrs (addrs_in (heap_memory h0)) (addrs_in (heap_memory h1)))]

val lemma_addrs_in_points_to (#a:Type) (r:ref a) (x:a)
  : Lemma (addrs_in (r |> x) = OS.singleton (addr_of r))
          [SMTPat (addrs_in (r |> x))]

val lemma_addrs_in_join (m0 m1:memory)
  : Lemma (requires (defined (m0 <*> m1)))
          (ensures  (addrs_in (m0 <*> m1) = OS.union (addrs_in m0) (addrs_in m1)))
          [SMTPat (addrs_in (m0 <*> m1))]

(* addr_to_ref *)
val lemma_addr_to_ref_addr_of (m:memory) (r:nat) 
  : Lemma (requires (defined m /\ OS.mem r (addrs_in m)))
          (ensures  (addr_of (dsnd (addr_to_ref m r)) = r))
          [SMTPat (defined m);
           SMTPat (OS.mem r (addrs_in m))]

(* restrict_memory and complement_memory*)

val lemma_restrict_complement_disjoint (rs:addrs) (m:memory)
  : Lemma (requires (defined m))
          (ensures  (disjoint_addrs (addrs_in (restrict_memory rs m)) (addrs_in (complement_memory rs m))))
          [SMTPat (addrs_in (restrict_memory rs m));
           SMTPat (addrs_in (complement_memory rs m))]

val lemma_restrict_complement_sep (rs:addrs) (m:memory)
  : Lemma (requires (defined m))
          (ensures  (m == ((restrict_memory rs m) <*> (complement_memory rs m))))
          [SMTPat (restrict_memory rs m);
           SMTPat (complement_memory rs m)]

(* fresh_or_old *)

val lemma_fresh_or_old_refl (h:heap)
  : Lemma (fresh_or_old h h)
          [SMTPat (fresh_or_old h h)]

val lemma_fresh_or_old_trans (h0 h1 h2:heap)
  : Lemma (requires (fresh_or_old h0 h1 /\ fresh_or_old h1 h2))
          (ensures  (fresh_or_old h0 h2))
          [SMTPat (fresh_or_old h0 h1);
           SMTPat (fresh_or_old h1 h2)]

val lemma_fresh_or_old_disjoint (h0 h1 h2:heap)
  : Lemma (requires (fresh_or_old h0 h1 /\ disjoint_heaps h0 h2 /\ same_freshness h0 h2))
          (ensures  (disjoint_heaps h1 h2))
          [SMTPat (fresh_or_old h0 h1);
           SMTPat (same_freshness h0 h2)]

val lemma_fresh_or_old_sep (h0 h1 h2:heap) 
  : Lemma (requires (fresh_or_old h0 h1 /\ disjoint_heaps h0 h2 /\ same_freshness h0 h2))
          (ensures  (fresh_or_old (join h0 h2) (join h1 h2)))

val lemma_fresh_or_old_alloc (#a:Type0) (x:a) (h0:heap)
  : Lemma (let (_,h1) = alloc h0 x in
           fresh_or_old h0 h1)

val lemma_fresh_or_old_dealloc (#a:Type0) (r:ref a) (h0:heap)
  : Lemma (requires (h0 `hcontains` r))
          (ensures  (fresh_or_old h0 (dealloc h0 r)))

val lemma_fresh_or_old_upd (#a:Type0) (r:ref a) (x:a) (h0:heap)
  : Lemma (requires (h0 `hcontains` r))
          (ensures  (fresh_or_old h0 (upd h0 r x)))
