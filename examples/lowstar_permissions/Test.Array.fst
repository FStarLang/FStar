module Test.Array

module P = LowStar.Permissions
module A = LowStar.RST.Array
module RST = LowStar.RST
module R = LowStar.Resource
module HST = FStar.HyperStack.ST


#reset-options "--z3rlimit 5 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=1000"

let read_write_without_sharing () : RST.RST unit
  (R.empty_resource)
  (fun _ -> R.empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 2ul 42ul in
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 1ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 1ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 1ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 1ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  A.free b;
  ()

[@expect_failure]
let read_write_with_sharing () : RST.RST unit
  (R.empty_resource)
  (fun _ -> R.empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = A.alloc 2ul 42ul in
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let b1 = A.share b in
  let x1 =
    RST.rst_frame
      (R.(A.array_resource b <*> A.array_resource b1))
      #(A.array_resource b)
      (fun _ -> R.(A.array_resource b <*> A.array_resource b1))
      #(fun _ -> A.array_resource b)
      #(A.array_resource b1)
      (fun _ ->
        A.index b 0ul
      )
  in
  let b_first, b_second = RST.rst_frame
    (R.(A.array_resource b <*> A.array_resource b1))
    #(A.array_resource b)
    (fun (b_first, b_second) -> R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    #(fun (b_first, b_second) -> R.(A.array_resource b_first <*> A.array_resource b_second))
    #(A.array_resource b1)
    (fun _ -> A.split #FStar.UInt32.t b 1ul)
  in
  let x2 = RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    #(A.array_resource b_second)
    (fun _ -> R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    #(fun _ -> A.array_resource b_second)
    #(R.(A.array_resource b_first <*> A.array_resource b1))
    (fun _ -> A.index b_second 0ul)
  in
  let b = RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    #(R.(A.array_resource b_first <*> A.array_resource b_second))
    (fun b -> R.(A.array_resource b <*> A.array_resource b1))
    #(fun b -> A.array_resource b)
    #(A.array_resource b1)
    (fun _ -> A.glue b_first b_second)
  in
  A.merge b b1;
  A.free b;
  ()
