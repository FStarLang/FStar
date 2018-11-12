module Opaque_i

let make_opaque (#a:Type) (x:a) = x
let reveal_opaque (#a:Type) (x:a)  = ()
