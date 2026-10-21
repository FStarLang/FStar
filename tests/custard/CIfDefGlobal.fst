module CIfDefGlobal

open FStar.All
module U32 = FStar.UInt32

let rec helper (n:U32.t) : Tot U32.t (decreases (U32.v n)) =
  if U32.eq n 0ul then 7ul else helper (U32.sub n 1ul)

let result : U32.t =
  if CIfDef.first then helper 2ul else 11ul
