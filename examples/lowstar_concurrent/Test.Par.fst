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
  // let x, y = par (A.array_resource b) (A.array_resource b1)
  //   #_ #_
  //   #(fun _ -> A.array_resource b) #(fun _ -> A.array_resource b1)
  //   #_ #_ #_ #_
  //   (fun () -> A.index b 0ul) (fun () -> A.index b1 1ul) in
  // let x1 =
  //   RST.rst_frame
  //     (R.(A.array_resource b <*> A.array_resource b1))
  //     (fun _ -> R.(A.array_resource b <*> A.array_resource b1))
  //     (fun _ ->
  //       A.index b 0ul
  //     )
  // in
  // admit();
  A.merge b b1;
  A.free b
