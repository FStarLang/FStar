module Test.Vale

open FStar.Heap

let test (m0:mem) =

  let r1, m1 = alloc #Bool m0 true false in

  let lo1 = get_lo_view m1 in
  let _, s1, e1 = get_lo_range m1 r1 in
  assert (sel m1 r1 = true);
  assert (read_lo lo1 s1 e1 == Seq.create 1 b1);

  let r2, m2 = alloc #Bool m1 false true in

  let lo2 = get_lo_view m2 in
  let _, s2, e2 = get_lo_range m2 r2 in

  assert (sel m2 r1 = true);
  assert (sel m2 r2 = false);
  assert (get_lo_range m2 r1 = get_lo_range m1 r1);
  assert (m2 `mcontains` r1);
  assert (read_lo lo2 s1 e1 == Seq.create 1 b1);
  assert (read_lo lo2 s2 e2 == Seq.create 1 b0);
  assert (non_overlapping s1 e1 s2 e2);

  let lo3 = store lo2 s2 e2 (Seq.create 1 b1) in

  assert (read_lo lo3 s2 e2 == Seq.create 1 b1);
  assert (read_lo lo3 s1 e1 == Seq.create 1 b1);

  let m_opt = sync m2 (Set.singleton (addr_of r2)) lo3 in

  assert (forall (rt:rtti) (r:ref (type_of rt)). addr_of r <> addr_of r2 ==>
            (let (_, s, e) = get_lo_range m2 r in
	     read_lo lo2 s e == read_lo lo3 s e));
  assert (forall (rt:rtti) (r:ref (type_of rt)). Set.mem (addr_of r) (Set.singleton (addr_of r2)) \/
            (let (_, s, e) = get_lo_range m2 r in
	     read_lo lo2 s e == read_lo lo3 s e));
  assert (Some? (unmarshal Bool (read_lo lo3 s2 e2)));

  assert (forall (rt:rtti) (r:ref (type_of rt)). (m2 `mcontains` r /\ Set.mem (addr_of r) (Set.singleton (addr_of r2))) ==>
            (let (rt, s, e) = get_lo_range m2 r in
	     Some? (unmarshal rt (read_lo lo2 s e))));
  assert (forall (rt:rtti) (r:ref (type_of rt)). (m2 `mcontains` r /\ Set.mem (addr_of r) (Set.singleton (addr_of r2))) ==>
            (let (rt, s, e) = get_lo_range m2 r in
	     Some? (unmarshal rt (read_lo lo3 s e))))
  assert (Some? m_opt)



  assert False;

  ()
  

  
