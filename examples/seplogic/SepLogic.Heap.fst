module SepLogic.Heap

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & a))
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

private let equal_heaps (h0 h1:heap) =
  let _ = () in
  h0.next_addr = h1.next_addr /\
  FStar.FunctionalExtensionality.feq h0.memory h1.memory

private let equal_heaps_extensional (h0 h1:heap)
  : Lemma (requires True) (ensures (equal_heaps h0 h1 <==> h0 == h1))
  = ()
  
let memory = option (nat -> Tot (option (a:Type0 & a)))

private let equal_memories (m0 m1:memory) =
  match (m0, m1) with
  | (Some f0, Some f1) -> FStar.FunctionalExtensionality.feq f0 f1
  | (Some _, None)     -> False
  | (None, Some _)     -> False
  | (None, None)       -> True

private let equal_memories_extensional (m0 m1:memory)
  : Lemma (requires True) (ensures (equal_memories m0 m1 <==> m0 == m1))
  = ()

let defined m = Some? m

let emp = Some (fun _ -> None)

let emp_defined () = ()

let ref a = nat

let addr_of #a n = n

let heap_memory h = Some h.memory

let heap_memory_defined h = ()

let disjoint_heaps h0 h1 =
  let _ = () in
  (forall r . ~(Some?(h0.memory r) && Some?(h1.memory r)))

let disjoint_memories m0 m1 =
  match (m0, m1) with
  | (Some f0, Some f1) -> forall r . ~(Some?(f0 r) && Some?(f1 r))
  | _ -> False

let disjoint_heaps_comm h0 h1 = ()

let disjoint_memories_emp m = ()

let disjoint_memories_comm m0 m1 = ()

let disjoint_heaps_memories h0 h1 = ()

let join h0 h1 = 
  let memory = (fun r' ->  match (h0.memory r', h1.memory r') with
                              | (Some v1, None) -> Some v1
			      | (None, Some v2) -> Some v2
			      | (None, None)    -> None) in
  if (h0.next_addr < h1.next_addr)
  then { next_addr = h1.next_addr; memory = memory }
  else { next_addr = h0.next_addr; memory = memory }

let join_comm h0 h1 = assert (equal_heaps (join h0 h1) (join h1 h0))

let ( |> ) #a r x = 
  let f : nat -> Tot (option (a:Type0 & a)) = 
    (fun r' -> if r = r' then Some (| a , x |)
                         else None) in
  Some f

let ( <*> ) m0 m1 = 
  if (FStar.StrongExcludedMiddle.strong_excluded_middle (disjoint_memories m0 m1)) 
  then (match (m0, m1) with
        | (Some f0, Some f1) -> 
            let f = (fun r -> match (f0 r, f1 r) with
                              | (Some v1, None) -> Some v1
                              | (None, Some v2) -> Some v2
                              | (None, None)    -> None) in
            Some f)
  else None

let sep_emp m = 
  assert (equal_memories (m <*> emp) m)

let sep_comm m0 m1 = 
  assert (equal_memories (m0 <*> m1) (m1 <*> m0))

let sep_assoc m0 m1 m2 =
  assert (equal_memories (m0 <*> (m1 <*> m2)) ((m0 <*> m1) <*> m2))

let sep_join h0 h1 = 
  assert (equal_memories (heap_memory (join h0 h1)) 
                         ((heap_memory h0) <*> (heap_memory h1)))

let points_to_disjoint_memories #a #b r s x y = ()

let sep_disjoint_memories m0 m1 = ()

let points_to_defined #a r x = ()

let sep_defined m0 m1 = ()

let split_heap m0 m1 h = 
  match (m0, m1) with 
  | (Some f0, Some f1) -> 
      let h0 = { next_addr = h.next_addr; memory = f0 } in
      let h1 = { next_addr = h.next_addr; memory = f1 } in
      (h0,h1)

let split_heap_disjoint m0 m1 h = ()

let split_heap_join m0 m1 h = 
  assert (let (h0,h1) = split_heap m0 m1 h in
          equal_heaps h (join h0 h1))

let split_heap_memories m0 m1 h = ()

let hcontains #a h r = 
  let _ = () in 
  exists x . h.memory r == Some (| a , x |)

let mcontains #a m r = 
  match m with
  | Some f -> exists x . f r == Some (| a , x |)
  | None   -> False

let hcontains_mcontains #a r h = ()

let points_to_mcontains #a r x = ()

let sel #a h r =
  let Some (| _, x |) = h.memory r in
  x

let upd' (#a:Type0) (h:heap) (r:ref a) (x:a) =
  { h with memory = (fun r' -> if r = r' then Some (| a, x |)
                                         else h.memory r') }

let upd #a h r x = upd' h r x

let points_to_sel #a r x h = ()

let points_to_upd #a r x v h = 
  assert (equal_memories (heap_memory ((upd h r v))) (r |> v))

let hfresh #a r h = 
  h.memory r == None

let mfresh #a r m = 
  match m with
  | Some f -> f r == None
  | None   -> False

let hfres_mfresh #a r h = ()

let alloc #a h0 x = 
  let r = h0.next_addr in
  let memory1 = (fun r' -> if r = r' then Some (| a , x |)
                                     else h0.memory r') in
  let h1 = { next_addr = h0.next_addr + 1; memory = memory1 } in
  (r, h1)

let alloc_fresh #a h0 x = ()

let alloc_contains #a h0 x = ()

let alloc_sel #a h0 x = ()

let alloc_emp_points_to #a h0 x = 
  assert (let (r,h1) = alloc h0 x in
          equal_memories (heap_memory h1) (r |> x))
