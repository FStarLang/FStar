module Test.Array

module P = LowStar.Permissions
open Steel.RST
module A = Steel.Array


#reset-options "--z3rlimit 10 --max_fuel 1 --max_ifuel 1 --z3cliopt smt.qi.eager_threshold=1000"
#restart-solver
let read_write_without_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
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
let read_write_with_sharing () : RST unit
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let b = rst_frame
    empty_resource
    (fun b -> A.array_resource b)
    (fun _ -> A.alloc 2ul 42ul)
  in
  let x1 = rst_frame
    (A.array_resource b)
    (fun _ -> A.array_resource b)
    (fun _ -> A.index b 0ul)
  in
  let _ = rst_frame
    (A.array_resource b)
    (fun _ -> A.array_resource b)
    (fun _ -> A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul))
  in    admit()

  let b1 = rst_frame
    (A.array_resource b)
    (fun b1 -> A.array_resource b <*> A.array_resource b1)
    (fun _ -> A.share b)
  in
  let x1 =
    rst_frame
      (A.array_resource b <*> A.array_resource b1)
      (fun _ -> A.array_resource b <*> A.array_resource b1)
      (fun _ -> let f = A.index b 0ul in f)
  in
 // admit()

  let b_first, b_second = rst_frame
    (A.array_resource b <*> A.array_resource b1)
    (fun p -> A.array_resource (fst p) <*> A.array_resource (snd p) <*> A.array_resource b1)
    (let f = fun _ -> A.split #FStar.UInt32.t b 1ul in f) //TODO: remove let binding
  in
    let h0 =
    get (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in
  assert(A.get_rperm b_first h0 == A.get_rperm b_second h0);
  let x2 = rst_frame
    (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
    (fun _ -> (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> A.index b_second 0ul)
  in
  let h1 =
    get (A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)
  in
  assume(
    focus_rmem h0 (A.array_resource b_first <*> A.array_resource b_second) ==
    focus_rmem h1 (A.array_resource b_first <*> A.array_resource b_second)
  );
  assume(
    focus_rmem h0 (A.array_resource b1) ==
    focus_rmem h1 (A.array_resource b1)
  );
  rst_frame
    ((A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> (A.array_resource b <*> A.array_resource b1))
    (fun _ -> A.glue b b_first b_second);
  let h2 = get (A.array_resource b <*> A.array_resource b1) in
  assume(
    focus_rmem h1 (A.array_resource b1) ==
    focus_rmem h2 (A.array_resource b1)
  );
  A.gather b b1;
  let h = get (A.array_resource b) in
  A.free b
