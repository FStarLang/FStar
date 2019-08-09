module LowStar.RST.Loops

open LowStar.Resource
open LowStar.RST
module HS = FStar.HyperStack
module AR = LowStar.RST.Array
module A = LowStar.Array
module U32 = FStar.UInt32
open FStar.Mul

inline_for_extraction
val while
  (res:resource)
  (inv: (rmem res -> Type0))
  (guard: (rmem res -> GTot bool))
  (test: (unit -> RST bool
    res
    (fun _ -> res)
    (requires fun h -> inv h)
    (ensures fun h0 b h1 ->
      b == guard h0 /\
      h0 == h1)
  ))
  (body: (unit -> RST unit
    res
    (fun _ -> res)
    (requires fun h -> guard h /\ inv h)
    (ensures fun h0 _ h1 -> inv h1)
  ))
  : RST unit
    res
    (fun _ -> res)
    (requires fun h -> inv h)
    (ensures fun _ _ h1 -> inv h1 /\ ~(guard h1))

inline_for_extraction
val for
  (start:U32.t)
  (finish:U32.t{U32.v finish >= U32.v start})
  (context: resource)
  (loop_inv: (rmem context -> nat -> Type0))
  (f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> RST unit
    (context)
    (fun _ -> context)
    (fun h -> loop_inv h (U32.v i))
    (fun h0 _ h1 -> U32.(loop_inv h0 (v i) /\ loop_inv h1 (v i + 1)))
  ))
  : RST unit
    (context)
    (fun _ -> context)
    (fun h -> loop_inv h (U32.v start))
    (fun _ _ h1 -> loop_inv h1 (U32.v finish))
