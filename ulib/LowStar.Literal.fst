module LowStar.Literal

module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module IB = LowStar.ImmutableBuffer
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul

/// The implementation of LowStar.Literal.fsti. Not extracted as-is but instead
/// implemented in C using native string literals.

let buffer_of_literal s =
  let init: list UInt8.t = List.Tot.map u8_of_ascii_char (ascii_chars_of_ascii_string s) in
  normalize_spec (List.Tot.length init <= UInt.max_int 32);
  let h0 = ST.get () in
  let b = IB.igcmalloc_of_list HS.root init in
  let h1 = ST.get () in
  // Note: our memory model isn't fine-grained enough to account for things
  // allocated in the data-segment at program load-time and which remains always
  // live. However, we wish for this function to remain in the Stack and expose
  // no allocation behavior to its client. So, we cheat a little bit here.
  assume (ST.equal_domains h0 h1);
  b

let const_string = s:string { zero_free s }

let const_string_of_literal s = s
