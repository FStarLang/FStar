module OPLSS
module UInt8 = FStar.UInt8
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer
let bytes = Seq.seq UInt8.t
let lbytes l = b:bytes{Seq.length b = l}

assume
val random (l:nat) : EXT (lbytes l)
