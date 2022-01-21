module SteelNull

open Steel.Effect
open Steel.Reference

let main () =
  let r = null #UInt32.t in
  if is_null r then
    0ul
  else
    1ul
