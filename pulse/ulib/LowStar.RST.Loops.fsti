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
  (inv: (res.t -> Type0))
  (guard: (res.t -> GTot bool))
  (test: (unit -> RST bool
    res
    (fun _ -> res)
    (requires fun old -> inv (old res))
    (ensures fun old b modern ->
      b == guard (old res) /\
      old res == modern res)
  ))
  (body: (unit -> RST unit
    res
    (fun _ -> res)
    (requires fun old -> guard (old res) /\ inv (old res))
    (ensures fun old _ modern -> inv (modern res))
  ))
  : RST unit
    res
    (fun _ -> res)
    (requires fun old -> inv (old res))
    (ensures fun _ _ modern -> inv (modern res) /\ ~(guard (modern res)))

inline_for_extraction
val for
  (start:U32.t)
  (finish:U32.t{U32.v finish >= U32.v start})
  (context: resource)
  (loop_inv: (context.t -> nat -> Type0))
  (f:(i:U32.t{U32.(v start <= v i /\ v i < v finish)} -> RST unit
    (context)
    (fun _ -> context)
    (requires (fun old -> loop_inv (old context) (U32.v i)))
    (ensures (fun old _ modern -> U32.(loop_inv (old context) (v i) /\ loop_inv (modern context) (v i + 1))))
  ))
  : RST unit
    (context)
    (fun _ -> context)
    (requires (fun old -> loop_inv (old context) (U32.v start)))
    (ensures (fun _ _ modern -> loop_inv (modern context) (U32.v finish)))
