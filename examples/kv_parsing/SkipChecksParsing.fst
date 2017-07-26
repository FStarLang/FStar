module SkipChecksParsing

open FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open KeyValue
open PureValidator
open ValidatedParser
open PureParser

(*! Skipping bounds checks due to validation *)

// Another aspect to verify is that the bounds checks can be skipped. This
// can be done even in pure F*, but is more obvious in effectful F* where we
// prove safety of pointer arithmetic.

// note that there are no bounds checks here; they are instead asserted and
// proven through the validation
let parse_valid_u16_array (b:bytes{Some? (validate_u16_array b)}) : a:u16_array{parse_result (parse_u16_array b) == a} =
  // these asserts are for illustration only; in this simple example Z3 proves the
  // right bounds automatically from the refinements on [slice].
  assert (length b >= 2);
  let len = u16_from_be (slice b 0 2) in
  assert (length (slice b 2 (length b)) >= U16.v len);
  let data = slice b 2 (2+U16.v len) in
  U16Array len data

let parse_valid_u32_array (b:bytes{Some? (validate_u32_array b)}) : a:u32_array{parse_result (parse_u32_array b) == a} =
  let len = u32_from_be (slice b 0 4) in
  let data = slice b 4 (4+U32.v len) in
  U32Array len data

assume val parse_valid_entry (b:bytes{Some? (validate_entry b)}) : e:encoded_entry{parse_result (parse_entry b) == e}
  // TODO: unfortunately these validated parsers don't return how much data they
  // consumed like normal parsers, so chaining them will require separately
  // computing these lengths (based on the length of the array returned))

  // TODO: the underlying reason is that a validated parser is a special case of
  // a parser, but with a refinement on both the result type _and_ the input
  // b:bytes, which can't even possibly be expressed using the [parser] type.
