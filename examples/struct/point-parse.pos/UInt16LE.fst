module UInt16LE

module S = FStar.Seq
module B = FStar.BufferNG
module HST = FStar.HyperStack.ST

abstract let of_bytes (s : S.seq UInt8.t { S.length s = 2 }) : Tot UInt16.t
=
  let x_lo = S.index s 0 in
  let x_hi = S.index s 1 in
  let x_lo_16 = FStar.Int.Cast.uint8_to_uint16 x_lo in
  let x_hi_16 = FStar.Int.Cast.uint8_to_uint16 x_hi in
  FStar.UInt16.(x_lo_16 |^ (x_hi_16 <<^ 8ul))

abstract let parse_bytes
  (b : B.buffer UInt8.t { B.length b = 2ul }) : HST.Stack UInt16.t
  (requires (fun h -> B.live h b))
  (ensures (fun h x h' ->
    h == h' /\
    x = of_bytes (B.as_seq h' b)
  ))
=
  let x_lo = B.read b 0ul in
  let x_hi = B.read b 1ul in
  let x_lo_16 = FStar.Int.Cast.uint8_to_uint16 x_lo in
  let x_hi_16 = FStar.Int.Cast.uint8_to_uint16 x_hi in
  FStar.UInt16.(x_lo_16 |^ (x_hi_16 <<^ 8ul))
