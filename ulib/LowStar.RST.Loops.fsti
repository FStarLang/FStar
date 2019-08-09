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
  (res:Ghost.erased resource)
  (inv: (rmem (Ghost.reveal res) -> Type0))
  (guard: (rmem (Ghost.reveal res) -> GTot bool))
  (test: (unit -> RST bool
    (Ghost.reveal res)
    (fun _ -> Ghost.reveal res)
    (requires fun h -> inv h)
    (ensures fun h0 b h1 ->
      b == guard h0 /\
      h0 == h1)
  ))
  (body: (unit -> RST unit
    (Ghost.reveal res)
    (fun _ -> Ghost.reveal res)
    (requires fun h -> guard h /\ inv h)
    (ensures fun h0 _ h1 -> inv h1)
  ))
  : RST unit
    (Ghost.reveal res)
    (fun _ -> Ghost.reveal res)
    (requires fun h -> inv h)
    (ensures fun _ _ h1 -> inv h1 /\ ~(guard h1))

inline_for_extraction
val for
  (start:U32.t)
  (finish:U32.t{U32.v finish >= U32.v start})
  (context: Ghost.erased resource)
  (loop_inv: (rmem (Ghost.reveal context) -> nat -> Type0))
  (f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> RST unit
    (Ghost.reveal context)
    (fun _ -> Ghost.reveal context)
    (fun h -> loop_inv h (U32.v i))
    (fun h0 _ h1 -> U32.(loop_inv h0 (v i) /\ loop_inv h1 (v i + 1)))
  ))
  : RST unit
    (Ghost.reveal context)
    (fun _ -> Ghost.reveal context)
    (fun h -> loop_inv h (U32.v start))
    (fun _ _ h1 -> loop_inv h1 (U32.v finish))
