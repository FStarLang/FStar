module SepLogic.Heap

module S  = FStar.Set
module TS = FStar.TSet

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & a))
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

let ref a = nat

let addr_of #a n = n

private let equal (h1 h2:heap) =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

private let equal_extensional (h0 h1:heap)
  : Lemma (requires True) (ensures (equal h0 h1 <==> h0 == h1))
  = ()

let join_tot h0 h1 =
  let memory = (fun r' ->  match (h0.memory r', h1.memory r') with
                              | (Some v1, None) -> Some v1
			      | (None, Some v2) -> Some v2
			      | _               -> None) in
  if (h0.next_addr < h1.next_addr)
  then { next_addr = h1.next_addr; memory = memory }
  else { next_addr = h0.next_addr; memory = memory }

let disjoint #a #b r0 r1 = r0 =!= r1

let disjoint_heaps h0 h1 =
  let _ = () in
  (forall (r:nat). ~(Some?(h0.memory r) && Some?(h1.memory r)))

let emp = fun h -> h.next_addr = 0 /\ (forall r . None? (h.memory r))

private let init_heap : heap = 
  let memory = fun r -> None in
  { next_addr = 0; memory = memory}

private let lemma_init_heap_emp ()
  : Lemma (emp (init_heap))
          [SMTPat (emp (init_heap))]
  = ()

let ( |> ) #a r x = 
  fun h -> h.memory r == Some (| a , x |) /\ (forall r' . r =!= r' ==> None? (h.memory r'))  

let ( <*> ) p q = 
  fun h -> exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ q h1 

let sep_interp p q h = 
  assert_norm ((p <*> q) h ==> (exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ (q h1)))

private let lemma_disjoint_heaps_emp (h0 h1:heap)
  : Lemma (emp h1 ==> disjoint_heaps h0 h1)
          [SMTPat (disjoint_heaps h0 h1); SMTPat (emp h1)]
  = ()

private let lemma_join_tot_emp' (h0 h1:heap)
  : Lemma (emp h1 ==> equal (join_tot h0 h1) h0)
  = ()

private let lemma_join_tot_emp (h0 h1:heap)
  : Lemma (emp h1 ==> (join_tot h0 h1) == h0)
          [SMTPat (join_tot h0 h1); SMTPat (emp h1)]
  = lemma_join_tot_emp' h0 h1

private let emp_unit'  (p:hpred) (h:heap) (h0 h1:heap)
  : Lemma ((disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ (emp h1)) ==> p h)
  = lemma_join_tot_emp h0 h1

let emp_unit p h = 
  sep_interp p emp h;
  FStar.Classical.forall_to_exists (fun h1 -> FStar.Classical.forall_to_exists (fun h0 -> emp_unit' p h h0 h1));
  FStar.Classical.move_requires (fun h -> 
    FStar.Classical.exists_intro (fun h1 -> exists h0 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ (emp h1)) init_heap) h
  
private let lemma_disjoint_heaps_comm (h0 h1:heap) 
  : Lemma ((disjoint_heaps h0 h1) <==> (disjoint_heaps h0 h1))
          [SMTPat (disjoint_heaps h0 h1)]
  = ()

private let lemma_join_tot_comm' (h0 h1:heap)
  : Lemma (equal (join_tot h0 h1) (join_tot h1 h0))
  = ()

private let lemma_join_tot_comm (h0 h1:heap)
  : Lemma ((join_tot h0 h1) == (join_tot h1 h0))
          [SMTPat (join_tot h0 h1)]
  = lemma_join_tot_comm' h0 h1

private let lemma_sep_comm (p q:hpred) (h:heap)
  : Lemma ((exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ q h1) 
           <==> 
           (exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h1 /\ q h0))
  = ()

let sep_comm p q h = lemma_sep_comm p q h

// exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ (exists h1' h1'' . disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1'')

// exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ (exists h0' h0'' . disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'') /\ r h1


// exists h0 h1 h1' h1'' . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1''

// exists h0 h1 h0' h0'' . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1

private let lemma_join_tot_assoc' (h0 h1 h2:heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ disjoint_heaps h1 h2 /\ disjoint_heaps h0 h2))
          (ensures  (equal (join_tot h0 (join_tot h1 h2)) (join_tot (join_tot h0 h1) h2)))
  = ()

private let lemma_join_tot_assoc (h0 h1 h2:heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ disjoint_heaps h1 h2 /\ disjoint_heaps h0 h2))
          (ensures  (join_tot h0 (join_tot h1 h2) == join_tot (join_tot h0 h1) h2))
          [SMTPat (join_tot h0 (join_tot h1 h2)); SMTPat (join_tot (join_tot h0 h1) h2)]
  = lemma_join_tot_assoc' h0 h1 h2

private let exists_intro_4 (#a0:Type) (#a1:Type) (#a2:Type) (#a3:Type) 
                           (p:(a0 -> a1 -> a2 -> a3 -> Type)) 
                           (witness0:a0) (witness1:a1) (witness2:a2) (witness3:a3)
  : Lemma (requires (p witness0 witness1 witness2 witness3))
          (ensures  (exists x0 x1 x2 x3 . p x0 x1 x2 x3))
  = ()

private let sep_assoc_l2r' (p q r:hpred) (h h0 h1 h1' h1'':heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
                     disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1''))
          (ensures  (exists h0 h1 h0' h0'' . 
                       disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
                       disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1))
  = exists_intro_4 (fun h0 h1 h0' h0'' -> 
                      disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
                      disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1)
                   (join_tot h0 h1') h1'' h0 h1'

private let sep_assoc_l2r'' (p q r:hpred) (h h0 h1 h1' h1'':heap)
  : Lemma ((disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
            disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1'')
           ==> 
          (exists h0 h1 h0' h0'' . 
             disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
             disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1))
  = FStar.Classical.move_requires (fun h -> sep_assoc_l2r' p q r h h0 h1 h1' h1'') h

private let forall_to_exists_4 (#a0:Type) (#a1:Type) (#a2:Type) (#a3:Type) 
                               (#p:(a0 -> a1 -> a2 -> a3 -> Type)) (#r:Type) 
                               ($f:(x0:a0 -> x1:a1 -> x2:a2 -> x3:a3 -> Lemma (p x0 x1 x2 x3 ==> r)))
  : Lemma ((exists (x0:a0) (x1:a1) (x2:a2) (x3:a3) . p x0 x1 x2 x3) ==> r)
  = FStar.Classical.forall_to_exists (fun (x3:a3) -> 
    FStar.Classical.forall_to_exists (fun (x2:a2) -> 
    FStar.Classical.forall_to_exists (fun (x1:a1) -> 
    FStar.Classical.forall_to_exists (fun (x0:a0) -> f x0 x1 x2 x3))))

private let sep_assoc_l2r''' (p q r:hpred) (h:heap)
  : Lemma ((exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
              (exists h1' h1'' . disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1''))
           ==> 
           (exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
              (exists h0' h0'' . disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'') /\ r h1))
  = forall_to_exists_4 (fun h0 h1 h1' h1'' -> sep_assoc_l2r'' p q r h h0 h1 h1' h1'')

private let sep_assoc_l2r'''' (p q r:hpred) (h:heap)
  : Lemma ((exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
              (exists h0' h0'' . disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'') /\ r h1) 
           ==> 
           ((p <*> q) <*> r) h)
  = sep_interp (p <*> q) r h;
    sep_assoc_l2r''' p q r h

private let sep_assoc_l2r (p q r:hpred) (h:heap)
  : Lemma ((p <*> (q <*> r)) h ==> ((p <*> q) <*> r) h)
  = sep_assoc_l2r'''' p q r h;
    sep_interp p (q <*> r) h;
    admit ()
    
private let sep_assoc_r2l' (p q r:hpred) (h h0 h1 h0' h0'':heap)
  : Lemma (requires (disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
                     disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1))
          (ensures  (exists h0 h1 h1' h1'' . 
                       disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
                       disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1''))
  = exists_intro_4 (fun h0 h1 h1' h1'' -> 
                      disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
                      disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1'')
                   h0' (join_tot h0'' h1) h0'' h1

private let sep_assoc_r2l'' (p q r:hpred) (h h0 h1 h0' h0'':heap)
  : Lemma ((disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
            disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'' /\ r h1)
           ==>
           (exists h0 h1 h1' h1'' . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
              disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1''))
  = FStar.Classical.move_requires (fun h -> sep_assoc_r2l' p q r h h0 h1 h0' h0'') h

private let sep_assoc_r2l''' (p q r:hpred) (h:heap)
  : Lemma ((exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
              (exists h0' h0'' . disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'') /\ r h1)
           ==>
           (exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ 
              (exists h1' h1'' . disjoint_heaps h1' h1'' /\ h1 == join_tot h1' h1'' /\ q h1' /\ r h1'')))
  = forall_to_exists_4 (fun h0 h1 h0' h0'' -> sep_assoc_r2l'' p q r h h0 h1 h0' h0'')

private let sep_assoc_r2l'''' (p q r:hpred) (h:heap)
  : Lemma ((exists h0 h1 . 
              disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ 
              (exists h0' h0'' . disjoint_heaps h0' h0'' /\ h0 == join_tot h0' h0'' /\ p h0' /\ q h0'') /\ r h1)
           ==>
           (p <*> (q <*> r)) h)
  = sep_interp p (q <*> r) h;
    sep_assoc_r2l''' p q r h

private let sep_assoc_r2l (p q r:hpred) (h:heap)
  : Lemma (((p <*> q) <*> r) h ==> (p <*> (q <*> r)) h)
  = sep_assoc_r2l'''' p q r h;
    sep_interp (p <*> q) r h
    
let sep_assoc p q r h = 
  sep_assoc_l2r p q r h;
  sep_assoc_r2l p q r h

let fresh #a r = fun h -> h.memory r == None

let contains #a h r = 
  let _ = () in 
  exists x . h.memory r == Some (| a , x |)

let points_to_contains #a r x h = ()

private let points_to_disj' (#a:Type) (#b:Type) (r:ref a) (s:ref b) (x:a) (y:b) (h:heap) (h0:heap) (h1:heap)
  : Lemma ((disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ (r |> x) h0 /\ (s |> y) h1) ==> disjoint r s)
  = ()

private let points_to_disj'' (#a:Type) (#b:Type) (r:ref a) (s:ref b) (x:a) (y:b) (h:heap) (h0:heap) 
  : Lemma ((exists h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ (r |> x) h0 /\ (s |> y) h1) ==> disjoint r s)
  = FStar.Classical.forall_to_exists (fun h1 -> points_to_disj' r s x y h h0 h1)

private let points_to_disj''' (#a:Type) (#b:Type) (r:ref a) (s:ref b) (x:a) (y:b) (h:heap) 
  : Lemma ((exists h0 h1 . disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ (r |> x) h0 /\ (s |> y) h1) ==> disjoint r s)
  = FStar.Classical.forall_to_exists (fun h0 -> points_to_disj'' r s x y h h0)

let points_to_disj #a #b r s x y h = 
  sep_interp (r |> x) (s |> y) h;
  points_to_disj''' r s x y h

let sel_tot #a h r =
  let Some (| _, x |) = h.memory r in
  x

let upd_tot' (#a:Type0) (h:heap) (r:ref a) (x:a) =
  { h with memory = (fun r' -> if r = r' then Some (| a, x |)
                                         else h.memory r') }

let upd_tot #a h r x = upd_tot' h r x

let points_to_sel #a r x h = ()

let points_to_upd #a r x v h = ()

let restrict #a h r =
  { next_addr = r + 1;
    memory    = (fun (r':nat) -> if r' = r then h.memory r' else None) }

let minus #a h r =
  { h with memory = (fun (r':nat) -> if r' = r then None else h.memory r') }

let minus_contains #a r h = ()

let restrict_points_to #a r h = ()
