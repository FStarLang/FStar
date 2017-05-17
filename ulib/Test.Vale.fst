module Test.Vale

open FStar.Heap
open FStar.Heap.Vale

(*
 * test the model
 *)
let test (m0:mem{sync m0}) =
  let href, m1 = alloc #Bool m0 true in  //allocate a boolean value

  let a = get_lo_start m1 (addr_of href) in  //a is the address in the lo-level view

  (* check that the lo-level view is correct and that m1 is synchronized *)
  assert (load m1 a = b1);
  ()


  assert (sync m1);

  (* update the hi-level heap, and check that the updates are reflected in the lo-level view *)
  let m2 = upd m1 href false in
  assert (load m2 a = b0);
  assert (sync m2);

  (* update the lo-level view and check that the updates are reflected in the hi-level view *)
  let m3 = store m2 a b1 in
  assert (sel m3 href = true);
  assert (sync m3);

  (* store a bad value in the lo-level, check that the hi-level view is unchanged and the mem is no longer synchronized *)
  let m4 = store m3 a b2 in
  assert (sel m4 href = true);
  assert (~ (sync m4));

  (* store back a good value, and check that the hi-level view is again in sync *)
  let m5 = store m4 a b0 in
  assert (sel m5 href = false);
  assert (sync m5);

  let href1, m6 = alloc #Bool m5 true in
  let a1 = get_lo_start m6 (addr_of href1) in

  assert (addr_of href =!= addr_of href1);

  assert (sel m6 href == false);
  assert (load m6 a1 == b1);

  let m7 = store m6 a1 b1 in

  assert (sel m7 href1 == true);
  assert (sel m7 href == false);
  assert (load m7 a == b0);

  ()
