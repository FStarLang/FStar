module ColA
module U32 = FStar.UInt32
let f (x: U32.t) : U32.t = U32.add_mod x 1ul
