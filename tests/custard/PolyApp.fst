module PolyApp
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

let main () : ML I32.t =
  let p = PolyLib.swap { PolyLib.left = 1ul; PolyLib.right = 2ul } in
  if p.left = 2ul && p.right = 1ul then 0l else 1l
