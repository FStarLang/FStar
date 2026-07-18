module MachineIntegerPrimops

#set-options "--no_smt"
// This module is just meant to test that the embeddings and unembeddings
// work OK. We use the underspec versions of the primops to avoid
// having to deal with overflow preconditions, and use --no_smt.
// The signed ints don't have an underspec.. so we are not testing those
// here.

let _ =
  let open FStar.UInt8 in
  assert_norm (add_underspec 3uy 2uy == 5uy);
  assert_norm (sub_underspec 3uy 2uy == 1uy);
  assert_norm (mul_underspec 3uy 2uy == 6uy);
  assert_norm (1uy `add_underspec` 2uy `add_underspec` 3uy `add_underspec` 4uy == 10uy);
  ()

let _ =
  let open FStar.UInt16 in
  assert_norm (add_underspec 3us 2us == 5us);
  assert_norm (sub_underspec 3us 2us == 1us);
  assert_norm (mul_underspec 3us 2us == 6us);
  assert_norm (1us `add_underspec` 2us `add_underspec` 3us `add_underspec` 4us == 10us);
  ()

let _ =
  let open FStar.UInt32 in
  assert_norm (add_underspec 3ul 2ul == 5ul);
  assert_norm (sub_underspec 3ul 2ul == 1ul);
  assert_norm (mul_underspec 3ul 2ul == 6ul);
  assert_norm (1ul `add_underspec` 2ul `add_underspec` 3ul `add_underspec` 4ul == 10ul);
  ()

let _ =
  let open FStar.UInt64 in
  assert_norm (add_underspec 3uL 2uL == 5uL);
  assert_norm (sub_underspec 3uL 2uL == 1uL);
  assert_norm (mul_underspec 3uL 2uL == 6uL);
  assert_norm (1uL `add_underspec` 2uL `add_underspec` 3uL `add_underspec` 4uL == 10uL);
  ()
