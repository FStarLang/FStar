module Test.Array

module P = LowStar.Permissions
module A = LowStar.RST.Array
module Arr = LowStar.Array
module RST = LowStar.RST
module R = LowStar.Resource
module HST = FStar.HyperStack.ST


#reset-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 --z3cliopt smt.qi.eager_threshold=1000"
#restart-solver
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

#set-options "--z3rlimit 20"
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
      (fun _ -> R.(A.array_resource b <*> A.array_resource b1))
      (fun _ ->
        A.index b 0ul
      )
  in
  let b_first, b_second = RST.rst_frame
    (R.(A.array_resource b <*> A.array_resource b1))
    (fun p -> R.(A.array_resource (fst p) <*> A.array_resource (snd p) <*> A.array_resource b1))
    (let f = fun _ -> A.split #FStar.UInt32.t b 1ul in f) //TODO: remove let binding
  in
    let h0 =
    RST.get R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in
  assert(A.get_perm b_first h0 == A.get_perm b_second h0);
  let x2 = RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)))
    (fun _ -> A.index b_second 0ul)
  in
  let h1 =
    RST.get R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in
  assume(
    RST.focus_rmem h0 R.(A.array_resource b_first <*> A.array_resource b_second) ==
    RST.focus_rmem h1 R.(A.array_resource b_first <*> A.array_resource b_second)
  );
  assume(
    RST.focus_rmem h0 R.(A.array_resource b1) ==
    RST.focus_rmem h1 R.(A.array_resource b1)
  );
  RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> R.(A.array_resource b <*> A.array_resource b1))
    (fun _ -> A.glue b b_first b_second);
  let h2 = RST.get R.(A.array_resource b <*> A.array_resource b1) in
  assume(
    RST.focus_rmem h1 R.(A.array_resource b1) ==
    RST.focus_rmem h2 R.(A.array_resource b1)
  );
  A.gather b b1;
  let h = RST.get R.(A.array_resource b) in
  A.free b
