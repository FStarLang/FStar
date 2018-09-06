module SL.Heap

module S  = FStar.Set

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

val addrs_in : memory -> Tot (set nat)

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

val lemma_sep_unit' (m:memory)
  : Lemma ((emp <*> m) == m)
          [SMTPat (emp <*> m)]

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
  : Lemma (defined (m0 <*> m1) <==> (defined m0 /\ defined m1 /\ S.disjoint (addrs_in m0) (addrs_in m1)))
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
            
(* addrs_in *)

val lemma_addrs_in_emp (u:unit) 
  : Lemma (S.equal (addrs_in emp) (S.empty))

assume Addrs_in_emp_axiom: S.equal (addrs_in emp) (S.empty)

val lemma_addrs_in_disjoint_heaps (h0 h1:heap)
  : Lemma (disjoint_heaps h0 h1 <==> S.disjoint (addrs_in (heap_memory h0)) (addrs_in (heap_memory h1)))
          [SMTPat (S.disjoint (addrs_in (heap_memory h0)) (addrs_in (heap_memory h1)))]

val lemma_addrs_in_points_to (#a:Type) (r:ref a) (x:a)
  : Lemma (S.equal (addrs_in (r |> x)) (S.singleton (addr_of r)))
          [SMTPat (addrs_in (r |> x))]

val lemma_addrs_in_join (m0 m1:memory)
  : Lemma (requires (defined (m0 <*> m1)))
          (ensures  (S.equal (addrs_in (m0 <*> m1)) (S.union (addrs_in m0) (addrs_in m1))))
          [SMTPat (addrs_in (m0 <*> m1))]

val em_singl (#a:Type) (r:ref a) (v1 v2 : a)
  : Lemma (requires (r |> v1 == r |> v2))
          (ensures (v1 == v2))
          [SMTPat (r |> v1); SMTPat (r |> v2)]

val em_invert (#a:Type) (r:ref a) (v1 v2 : a) (m1 m2 : memory)
  : Lemma (requires (defined (r |> v1 <*> m1) /\ (r |> v1 <*> m1) == (r |> v2 <*> m2)))
          (ensures (v1 == v2 /\ m1 == m2))
          [SMTPat (r |> v1 <*> m1); SMTPat (r |> v2 <*> m2)]

type sref = (a:Type & ref a)
let refs = list sref
let ii #a (r : ref a) : sref = Mkdtuple2 a r

(* Does there exist a memory with domain fp such that pred? *)
let dom_exists (fp:list sref) (pred:memory -> Type0) : Type0 =
  let rec aux acc fp : Tot Type0 (decreases fp) =
    match fp with
    | [] -> pred acc
    (* this case prevents spurious `emp <*>` which actually matter (the pattern doesn't kick in?) *)
    (* the pattern was wrong, so not realy needed now, but we might as well keep it I guess *)
    | [h] ->
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      exists (v:ty). pred (acc <*> r |> v)
    | h :: t -> (* Note, if we match on the sigma pair here, we might prevent reduction *)
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      exists (v:ty). aux (acc <*> r |> v) t
  in aux emp fp

(* Do all memories with domain fp satisfy pred? *)
let dom_forall (fp:list sref) (pred:memory -> Type0) : Type0 =
  let rec aux acc fp : Tot Type0 (decreases fp) =
    match fp with
    | [] -> pred acc
    (* this case prevents spurious `emp <*>` which actually matter (the pattern doesn't kick in?) *)
    (* the pattern was wrong, so not realy needed now, but we might as well keep it I guess *)
    | [h] ->
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      forall (v:ty). pred (acc <*> r |> v)
    | h :: t -> (* Note, if we match on the sigma pair here, we might prevent reduction *)
      let ty = dfst h in
      let r : ref ty = dsnd #Type #ref h in
      forall (v:ty). aux (acc <*> r |> v) t
  in aux emp fp
