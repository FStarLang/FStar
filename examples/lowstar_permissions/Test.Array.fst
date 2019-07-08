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

#set-options "--warn_error '-271-296'"
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
  let h = HST.get () in
   let full = R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1) in
  let delta = R.(A.array_resource b_first <*> A.array_resource b1) in
  let open FStar.Tactics in
  assert (R.can_be_split_into full (delta, A.array_resource b_second)) by (tadmit ()); (* TODO: fix by tactic ?*)
  let x2 = RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1)))
    (fun _ -> A.index b_second 0ul)
  in

  let h' = HST.get () in
  assert(R.can_be_split_into delta (A.array_resource b_first, A.array_resource b1));
  assume(R.sel (R.view_of delta) h == R.sel (R.view_of delta) h' ==>
    R.sel (A.array_view b_first ) h == R.sel (A.array_view b_first) h' /\
    R.sel (A.array_view b1 ) h == R.sel (A.array_view b1) h');
  RST.rst_frame
    (R.(A.array_resource b_first <*> A.array_resource b_second <*> A.array_resource b1))
    (fun _ -> R.(A.array_resource b <*> A.array_resource b1))
    (fun _ -> A.glue b b_first b_second);

  let h'' = HST.get () in
  A.merge b b1;
  A.free b
