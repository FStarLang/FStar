module Test.Par

module P = LowStar.Permissions
module A = LowStar.RST.Array
module HST = FStar.HyperStack.ST
open LowStar.RST.Par
open LowStar.Array

open LowStar.Resource
open LowStar.RST

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=100"


let test (b1 b2:array UInt32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2)
  (fun _ -> vlength b1 = 1 /\ vlength b2 = 1)
  (fun _ _ _ -> True)
  =
  // let b = A.alloc 2ul 42ul in
  // let b1 = A.share b in
  assert (UInt32.v 0ul < vlength b1 /\ UInt32.v 0ul < vlength b2);  
  let x = par 
    (fun _ -> A.array_resource b1 <*> A.array_resource b2)
    (fun () -> A.index b1 0ul) (fun _ -> A.index b2 0ul) in
  ()



let read_write_with_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 2ul 42ul in
  let b1 = A.share b in
  let x, y = par 
    (fun _ -> A.array_resource b <*> A.array_resource b1)
    (fun () -> A.index b 0ul) (fun () -> A.index b1 1ul) in
  let x, y = par 
    (fun _ -> A.array_resource b <*> A.array_resource b1)
    (fun () -> A.index b 0ul) (fun () -> A.index b1 1ul) in
  let x1 =
    rst_frame
      ((A.array_resource b <*> A.array_resource b1))
      (fun _ -> (A.array_resource b <*> A.array_resource b1))
      (fun _ ->
        A.index b 0ul
      )
  in
  A.merge b b1;
  A.free b

let parallel_alloc () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  // Need those to conclude that empty_resource ~= empty_resource <*> empty_resource
  reveal_empty_resource();
  reveal_star();
  reveal_rst_inv();
  reveal_modifies();
  let h0 = HST.get() in
  // Allocates in parallel 
  let b1, b2 = par 
    (fun (x, y) -> A.array_resource x <*> A.array_resource y)
    (fun () -> A.alloc 2ul 2ul) (fun () -> A.alloc 2ul 2ul) in
  let res0 = empty_resource in
  let res1 = A.array_resource b1 <*> A.array_resource b2 in
  let h1 = HST.get() in
  // This explicit modifies is needed to trigger modifies_trans. Why?
  assert (modifies res0 res1 h0 h1);
  let x1 =
    rst_frame
      ((A.array_resource b1 <*> A.array_resource b2))
      (fun _ -> (A.array_resource b1 <*> A.array_resource b2))
      (fun _ ->
        A.index b1 0ul
      )
  in
  // We know the contents of each array after parallel allocation
  assert (x1 == 2ul);
  let _, x3 =
    par (fun _ -> A.array_resource b1 <*> A.array_resource b2)
      (fun _ -> A.upd b1 0ul 0ul) (fun () -> A.index b2 0ul) in
  let x2 =
    rst_frame
      ((A.array_resource b1 <*> A.array_resource b2))
      (fun _ -> (A.array_resource b1 <*> A.array_resource b2))
      (fun _ ->
        A.index b1 0ul
      )
  in
  // We can modify just one array...
  assert (x2 == 0ul);
  let x3 =
    rst_frame
      ((A.array_resource b1 <*> A.array_resource b2))
      (fun _ -> (A.array_resource b1 <*> A.array_resource b2))
      (fun _ ->
        A.index b2 0ul
      )
  in
  // and we still know that the other one was unmodified (since it's starred)
  assert (x3 == 2ul);

  // We can also do the free in parallel if we want
  // let _ = par (fun _ -> empty_resource <*> empty_resource)
  //   (fun () -> A.free b1) (fun () -> A.free b2) in
  rst_frame
      ((A.array_resource b1 <*> A.array_resource b2))
      (fun _ -> A.array_resource b2)
      (fun _ ->
        A.free b1
      );
  A.free b2
