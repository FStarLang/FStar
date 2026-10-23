module Foreign
module U32 = FStar.UInt32

let hook (_proof:unit) (x:U32.t) : U32.t = U32.add_mod x 4ul
let value : U32.t = 6ul
let identity (#a:Type0) (x:a) : a = x
let other (x:U32.t) : U32.t = x
