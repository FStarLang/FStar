module ListC
module L = FStar.List.Tot
module U32 = FStar.UInt32
let f (l: list U32.t) : bool = L.isEmpty l
let main () : U32.t = if f [1ul] then 0ul else 1ul
