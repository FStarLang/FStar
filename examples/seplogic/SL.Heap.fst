module SL.Heap

module OS = FStar.OrdSet
module F = FStar.FunctionalExtensionality

let addrs = OS.ordset nat (fun n m -> n <= m)

unfold let disjoint_addrs (s0 s1:addrs) = OS.intersect s0 s1 = OS.empty

private noeq type heap_rec = {
  next_addr : nat;
  hdomain   : addrs;
  memory    : F.restricted_t nat (fun _ -> option (a:Type0 & a))
}

let heap = h:heap_rec
  {(forall (r:nat) . 
      OS.mem r h.hdomain ==> r < h.next_addr) /\
      (forall (r:nat) . OS.mem r h.hdomain ==> Some? (h.memory r)) /\ 
      (forall (r:nat) . not (OS.mem r h.hdomain) ==> None? (h.memory r))}

private let equal_heaps (h0 h1:heap) =
  let _ = () in
  h0.next_addr = h1.next_addr /\
  h0.hdomain = h1.hdomain /\ 
  FStar.FunctionalExtensionality.feq h0.memory h1.memory
  
private noeq type memory_rec = {
  domain   : addrs; 
  contents : F.restricted_t nat (fun _ -> option (a:Type0 & a))
}

let memory = m:(option memory_rec)
  {forall m' . m == Some m' ==> 
               ((forall r . OS.mem r m'.domain ==> Some? (m'.contents r)) /\ 
                (forall r . not (OS.mem r m'.domain) ==> None? (m'.contents r)))}

private let equal_memories (m0 m1:memory) =
  match (m0, m1) with
  | (Some m0', Some m1') -> m0'.domain = m1'.domain /\ 
                            FStar.FunctionalExtensionality.feq m0'.contents m1'.contents
  | (Some _, None)     -> False
  | (None, Some _)     -> False
  | (None, None)       -> True

let defined m = Some? m

let emp = 
  let domain = OS.empty in
  let contents = F.on_dom nat (fun _ -> None) in
  Some ({ domain = domain; contents = contents })
  
let ref a = nat

let addr_of #a n = n

let heap_memory h = Some ({ domain   = h.hdomain;
                            contents = h.memory   })

let disjoint_heaps (h0 h1:heap) =
  let _ = () in
  disjoint_addrs h0.hdomain h1.hdomain

let join h0 h1 =
  let domain = OS.union h0.hdomain h1.hdomain in 
  let memory = F.on_dom nat (fun r ->  match (h0.memory r, h1.memory r) with
                                  | (Some v1, None) -> Some v1
			          | (None, Some v2) -> Some v2
			          | (None, None)    -> None) in
  if (h0.next_addr < h1.next_addr)
  then { next_addr = h1.next_addr; hdomain = domain; memory = memory }
  else { next_addr = h0.next_addr; hdomain = domain; memory = memory }

let ( |> ) #a r x = 
  let domain = OS.singleton r in
  let contents =
    (F.on_dom nat (fun r' -> if r = r' then Some (| a , x |)
                         else (None <: option (a:Type0 & a)))) in
  Some ({ domain = domain; contents = contents })

let ( <*> ) m0 m1 = 
  match (m0, m1) with
  | (Some m0', Some m1') ->
      (if (disjoint_addrs m0'.domain m1'.domain)
       then (let domain = OS.union m0'.domain m1'.domain in
             let contents = F.on_dom nat (fun r -> match (m0'.contents r, m1'.contents r) with
                                              | (Some v1, None) -> Some v1
                                              | (None, Some v2) -> Some v2
                                              | (None, None)    -> None) in
             Some ({ domain = domain; contents = contents }))
       else None)
  | _ -> None

let split_heap m0 m1 h = 
  match (m0, m1) with 
  | (Some m0', Some m1') -> 
      let h0 = { next_addr = h.next_addr; 
                 hdomain = m0'.domain; 
                 memory = m0'.contents } in
      let h1 = { next_addr = h.next_addr; 
                 hdomain = m1'.domain; 
                 memory = m1'.contents } in
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
  { h with memory = F.on_dom nat (fun r' -> if r = r' then Some (| a, x |)
                                        else h.memory r') }

let upd #a h r x = upd' h r x
  
let addrs_in m = 
  match m with
  | Some m' -> OS.as_set m'.domain
  | None    -> S.empty

let lemma_disjoint_heaps_comm h0 h1 = ()

let lemma_disjoint_heaps_memories h0 h1 = ()

let lemma_sep_defined_disjoint_heaps h0 h1 = ()

let lemma_join_comm h0 h1 =
  assert (OS.equal (OS.union h0.hdomain h1.hdomain) (OS.union h1.hdomain h0.hdomain));
  assert (equal_heaps (join h0 h1) (join h1 h0))

let lemma_sep_unit m = 
  match m with 
  | None    -> ()
  | Some m' -> 
      let (Some e) = emp in 
      assert (OS.equal (OS.intersect m'.domain e.domain) OS.empty);
      let (Some m'') = m <*> emp in 
      assert (OS.equal m''.domain m'.domain);
      assert (equal_memories (m <*> emp) m)

let lemma_sep_unit' m =
  match m with
  | None    -> ()
  | Some m' ->
      let (Some e) = emp in
      assert (OS.equal (OS.intersect m'.domain e.domain) OS.empty);
      let (Some m'') = emp <*> m in
      assert (OS.equal m''.domain m'.domain);
      assert (equal_memories (emp <*> m) m)

let lemma_sep_comm m0 m1 =
  match (m0,m1) with
  | (Some m0', Some m1') -> 
      if (disjoint_addrs m0'.domain m1'.domain)
      then (assert (OS.equal (OS.union m0'.domain m1'.domain) (OS.union m1'.domain m0'.domain));
            let (Some m)  = m0 <*> m1 in
            let (Some m') = m1 <*> m0 in
            assert (equal_memories (m0 <*> m1) (m1 <*> m0)))
      else (assert (equal_memories (m0 <*> m1) (m1 <*> m0)))
  | _ -> ()

let lemma_sep_assoc m0 m1 m2 = 
  match (m0,m1,m2) with
  | (Some m0', Some m1', Some m2') -> 
      if (disjoint_addrs m0'.domain m1'.domain && 
          disjoint_addrs m1'.domain m2'.domain && 
          disjoint_addrs m0'.domain m2'.domain)
      then (assert (OS.equal (OS.union m0'.domain (OS.union m1'.domain m2'.domain)) 
                             (OS.union (OS.union m0'.domain m1'.domain) m2'.domain));
            assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2)))
      else if (not (disjoint_addrs m0'.domain m1'.domain))
      then (assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2)))
      else if (not (disjoint_addrs m1'.domain m2'.domain))
      then (assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2)))
      else if (not (disjoint_addrs m0'.domain m2'.domain))
      then (assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2)))
  | _ -> ()

let lemma_sep_join (h0 h1:heap) = 
  assert (equal_memories (heap_memory (join h0 h1)) 
                         ((heap_memory h0) <*> (heap_memory h1)))

let lemma_emp_defined () = ()

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

let lemma_addrs_in_emp () = ()

let lemma_addrs_in_disjoint_heaps h0 h1 = ()

let lemma_addrs_in_points_to #a r x = ()

let lemma_addrs_in_join m0 m1 = ()
