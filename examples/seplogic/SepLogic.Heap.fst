module SepLogic.Heap

private noeq type heap_rec = {
  next_addr : nat;
  hdomain   : set nat;
  memory    : nat -> Tot (option (a:Type0 & a))
}

let heap = h:heap_rec
  {(forall (r:nat) . 
      FStar.Set.mem r h.hdomain    ==> r < h.next_addr) /\
      (forall (r:nat) . FStar.Set.mem r h.hdomain    ==> Some? (h.memory r)) /\ 
      (forall (r:nat) . FStar.Set.mem r (FStar.Set.complement h.hdomain) ==> None? (h.memory r))}

private let equal_heaps (h0 h1:heap) =
  let _ = () in
  h0.next_addr = h1.next_addr /\
  FStar.Set.equal h0.hdomain h1.hdomain /\ 
  FStar.FunctionalExtensionality.feq h0.memory h1.memory

private let lemma_heap_ext (h0 h1:heap)
  : Lemma (equal_heaps h0 h1 <==> h0 == h1)
  = ()
  
private noeq type memory_rec = {
  domain   : set nat; 
  contents : nat -> Tot (option (a:Type0 & a))
}

let memory = m:(option memory_rec)
  {forall m' . m == Some m' ==> 
               ((forall r . FStar.Set.mem r m'.domain   ==> Some? (m'.contents r)) /\ 
                (forall r . FStar.Set.mem r (FStar.Set.complement m'.domain) ==> None? (m'.contents r)))}

private let equal_memories (m0 m1:memory) =
  match (m0, m1) with
  | (Some m0', Some m1') -> FStar.Set.equal m0'.domain m1'.domain /\ 
                            FStar.FunctionalExtensionality.feq m0'.contents m1'.contents
  | (Some _, None)     -> False
  | (None, Some _)     -> False
  | (None, None)       -> True

private let lemma_memory_ext (m0 m1:memory)
  : Lemma (equal_memories m0 m1 <==> m0 == m1)
  = ()

let defined m = Some? m

let emp = 
  let domain = FStar.Set.empty in
  let contents = fun _ -> None in
  Some ({ domain = domain; contents = contents })
  
let lemma_defined_emp () = ()

let ref a = nat

let addr_of #a n = n

let heap_memory h = Some ({ domain   = h.hdomain;
                            contents = h.memory  })

let disjoint_heaps (h0 h1:heap) =
  let _ = () in
  FStar.Set.disjoint h0.hdomain h1.hdomain

(*let disjoint_memories (m0 m1:memory) =
  match (m0, m1) with
  | (Some m0', Some m1') -> FStar.Set.disjoint m0'.domain m1'.domain
  | _ -> False*)

let join h0 h1 =
  let domain = FStar.Set.union h0.hdomain h1.hdomain in 
  let memory = (fun r' ->  match (h0.memory r', h1.memory r') with
                              | (Some v1, None) -> Some v1
			      | (None, Some v2) -> Some v2
			      | (None, None)    -> None) in
  if (h0.next_addr < h1.next_addr)
  then { next_addr = h1.next_addr; hdomain = domain; memory = memory }
  else { next_addr = h0.next_addr; hdomain = domain; memory = memory }

let ( |> ) #a r x = 
  let domain = FStar.Set.singleton r in
  let contents : nat -> Tot (option (a:Type0 & a)) = 
    (fun r' -> if r = r' then Some (| a , x |)
                         else None) in
  Some ({ domain = domain; contents = contents })

let ( <*> ) m0 m1 = 
  match (m0, m1) with
  | (Some m0', Some m1') ->
      (if (FStar.StrongExcludedMiddle.strong_excluded_middle (FStar.Set.disjoint m0'.domain m1'.domain))
       then (let domain = FStar.Set.union m0'.domain m1'.domain in
             let contents = (fun r -> match (m0'.contents r, m1'.contents r) with
                                     | (Some v1, None) -> Some v1
                                     | (None, Some v2) -> Some v2
                                     | (None, None)    -> None) in
             Some ({ domain = domain; contents = contents }))
       else None)
  | _ -> None

let split_heap m0 m1 h = 
  match (m0, m1) with 
  | (Some m0', Some m1') -> 
      let h0 = { next_addr = h.next_addr; hdomain = m0'.domain; memory = m0'.contents } in
      let h1 = { next_addr = h.next_addr; hdomain = m1'.domain; memory = m1'.contents } in
      (h0,h1)

let hcontains #a h r = 
  let _ = () in 
  exists x . h.memory r == Some (| a , x |)

let mcontains #a m r = 
  match m with
  | Some m' -> exists x . m'.contents r == Some (| a , x |)
  | None    -> False

let sel #a h r =
  let Some (| _, x |) = h.memory r in
  x

let upd' (#a:Type0) (h:heap) (r:ref a) (x:a) =
  { h with memory = (fun r' -> if r = r' then Some (| a, x |)
                                         else h.memory r') }

let upd #a h r x = upd' h r x

let fresh #a r h = 
  h.memory r == None

let alloc #a h0 x = 
  let r = h0.next_addr in 
  let next_addr = h0.next_addr + 1 in
  let domain = FStar.Set.union h0.hdomain (FStar.Set.singleton r) in
  let memory = (fun r' -> if r = r' then Some (| a , x |)
                                    else h0.memory r') in
  let h1 = { next_addr = next_addr + 1; hdomain = domain; memory = memory } in
  (r, h1)

let addrs_in m = 
  match m with
  | Some m' -> m'.domain
  | None    -> FStar.Set.empty

let lemma_disjoint_heaps_comm (h0 h1:heap) = ()

let lemma_disjoint_heaps_memories h0 h1 = ()

let lemma_sep_defined_disjoint_heaps h0 h1 = ()

let lemma_join_comm h0 h1 =
  assert (equal_heaps (join h0 h1) (join h1 h0))

let lemma_sep_unit m = 
  assert (equal_memories (m <*> emp) m)

let lemma_sep_comm m0 m1 = 
  assert (equal_memories (m0 <*> m1) (m1 <*> m0))

let lemma_sep_assoc m0 m1 m2 =
  assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2))

let lemma_sep_join (h0 h1:heap) = 
  assert (equal_memories (heap_memory (join h0 h1)) 
                         ((heap_memory h0) <*> (heap_memory h1)))

let lemma_points_to_defined #a r x = ()

let lemma_sep_defined m0 m1 = ()

let lemma_heap_memory_defined h = ()

let lemma_split_heap_disjoint m0 m1 h = ()

let lemma_split_heap_join m0 m1 h = 
  assert (let (h0,h1) = split_heap m0 m1 h in
          equal_heaps h (join h0 h1))

let lemma_split_heap_memories m0 m1 h = ()

let lemma_hcontains_mcontains #a r h = ()

let lemma_points_to_mcontains #a r x = ()

let lemma_points_to_sel #a r x h = ()

let lemma_points_to_upd #a r x v h = 
  assert (equal_memories (heap_memory ((upd h r v))) (r |> v))

let lemma_alloc_fresh #a h0 x = ()

let lemma_alloc_contains #a h0 x = ()

let lemma_alloc_sel #a h0 x = ()

let lemma_alloc_emp_points_to #a h0 x = 
  assert (let (r,h1) = alloc h0 x in
          equal_memories (heap_memory h1) (r |> x))

let lemma_addrs_in_emp () = ()

let lemma_addrs_in_points_to #a r x = ()

let lemma_addrs_in_join m0 m1 = ()
