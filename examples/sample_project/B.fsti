module B
open FStar.HyperStack.ST
open FStar.Buffer

val validate:
    argc:UInt32.t
  -> argv:Buffer.buffer string{Buffer.length argv == UInt32.v argc}
  -> Stack bool
    (requires (fun h -> True))
    (ensures (fun h _ h' -> True))

