module Test.Array

module P = LowStar.Permissions
module A = LowStar.RST.Array
module Arr = LowStar.Array
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

let read_write_with_sharing () : RST.RST unit
  (R.empty_resource)
  (fun _ -> R.empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let h0 = HST.get () in
  let b = A.alloc 2ul 42ul in
  let x1 = A.index b 0ul in
  A.upd b 0ul FStar.UInt32.(x1 +%^ 1ul);
  let b1 = A.share b in
  let h = HST.get () in
  assert((R.sel (A.array_view b) h).A.p = 0.5R);
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
    (let f = fun _ -> A.split #FStar.UInt32.t b 1ul in f) //TODO: remove let binding
  in
  let h = HST.get () in
  assert((R.sel (A.array_view b_first) h).A.p = 0.5R);
  assert((R.sel (A.array_view b_second) h).A.p = 0.5R);
  assume(R.inv R.(A.array_resource b_second <*> (A.array_resource b_first <*> A.array_resource b1)) h);
  assume(RST.rst_inv R.(A.array_resource b_second <*> (A.array_resource b_first <*> A.array_resource b1)) h);
  let x2 = RST.rst_frame
    (R.(A.array_resource b_second <*> (A.array_resource b_first <*> A.array_resource b1)))
    #(A.array_resource b_second)
    (fun _ -> R.(A.array_resource b_second <*> (A.array_resource b_first <*> A.array_resource b1)))
    #(fun _ -> A.array_resource b_second)
    #(R.(A.array_resource b_first <*> A.array_resource b1))
    (fun _ -> A.index b_second 0ul)
  in
  let h = HST.get () in
  assume(R.inv R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1) h);
  assume(RST.rst_inv R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1) h);
  assume((R.sel (A.array_view b_first) h).A.p = 0.5R);
  assume((R.sel (A.array_view b_second) h).A.p = 0.5R);
  let b = RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    #(R.(A.array_resource b_first <*> A.array_resource b_second))
    (fun b -> R.(A.array_resource b <*> A.array_resource b1))
    #(fun b -> A.array_resource b)
    #(A.array_resource b1)
    (fun _ -> A.glue b_first b_second)
  in
  let h = HST.get () in
  assume((R.sel (A.array_view b) h).A.p = 0.5R);
  assume((R.sel (A.array_view b1) h).A.p = 0.5R);
  assume(Arr.mergeable b b1 /\ Arr.freeable b); // These ones have to be fixed in Lowstar.Array
  A.merge b b1;
  let h = HST.get () in
  assert((R.sel (A.array_view b) h).A.p = 1.0R);
  A.free b;
  let h1 = HST.get () in
  assume (RST.modifies (R.empty_resource) (R.empty_resource) h0 h1)
