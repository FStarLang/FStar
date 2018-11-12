module A
open FStar.HyperStack.ST
open FStar.Buffer

val main: 
    argc:Int32.t{Int32.v argc > 0}
  -> argv:Buffer.buffer string{Buffer.length argv == Int32.v argc}
  -> Stack Int32.t 
    (requires (fun h -> True))
    (ensures (fun h _ h' -> True))
