module Basic

open FStar.UInt32

let foo (x:UInt32.t) =
  let y = x in
  let z = x in
  y `add_underspec` z
