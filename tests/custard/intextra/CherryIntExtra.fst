module CherryIntExtra

(* FStarC.Int.Extra-c.cherry.fst: the bitwise operations on [int], with
   Zarith's two's complement semantics, on small, negative and multi-word
   operands. *)
open FStarC.Effect
module E = FStarC.Int.Extra

let big : int = 0x123456789abcdef0123456789

let main () : ML FStar.UInt32.t =
  let ok = E.logand 12 10 = 8 && E.logor 12 10 = 14 && E.logxor 12 10 = 6 in
  let ok = E.logand (-1) 5 = 5 && E.logand (-8) 13 = 8 && E.logor (-8) 3 = -5 && ok in
  let ok = E.logxor (-1) 5 = -6 && E.logxor (-6) (-3) = 7 && E.lognot 0 = -1 && E.lognot (-7) = 6 && ok in
  let ok = E.logand big 0xffffffffffffffff = 0xabcdef0123456789 && ok in
  let ok = E.logand big (-0x100000000) = 0x123456789abcdef0100000000 && ok in
  let ok = E.logor big (-0x10000000000000000) = -0x543210fedcba9877 && ok in
  let ok = E.logxor big big = 0 && E.logxor big (E.lognot big) = -1 && ok in
  let ok = E.shift_left 3 70 = 0xc00000000000000000 && E.shift_left (-3) 2 = -12 && ok in
  let ok = E.shift_right big 64 = 0x123456789 && E.shift_right (-5) 1 = -3 && ok in
  if ok then 0ul else 1ul
