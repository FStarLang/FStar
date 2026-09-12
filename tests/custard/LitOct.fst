module LitOct

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32

/// Section 43.1-43.2.  Every base F* can write, on a backend that cannot
/// necessarily write it back.
///
/// The assertions below are on the *values*, not on the spellings, and that is
/// the whole point of this test.  Both bugs it pins were silent: the C backend
/// wrote [0o17], which no C compiler accepts, and the karamel path wrote
/// [017], which karamel reads back as seventeen.  A grep for a spelling would
/// have passed the second one.

let oct : U32.t = 0o17ul
let bin : U32.t = 0b1010ul
let hex : U32.t = 0xful
let dec : U32.t = 15ul

let oct_big : U32.t = 0o7654321ul
let bin_byte : U8.t = 0b10000001uy

let classify (x : U8.t) : U32.t =
  match x with
  | 0o17uy -> 1ul
  | 0b1010uy -> 2ul
  | 0xffuy -> 3ul
  | _ -> 0ul

let main () : I32.t =
  if not (U32.eq oct 15ul) then 1l
  else if not (U32.eq bin 10ul) then 2l
  else if not (U32.eq hex 15ul) then 3l
  else if not (U32.eq dec 15ul) then 4l
  else if not (U32.eq oct_big 2054353ul) then 5l
  else if not (U8.eq bin_byte 129uy) then 6l
  else if not (U32.eq (classify 15uy) 1ul) then 7l
  else if not (U32.eq (classify 10uy) 2ul) then 8l
  else if not (U32.eq (classify 255uy) 3ul) then 9l
  else if not (U32.eq (classify 7uy) 0ul) then 10l
  else 0l
