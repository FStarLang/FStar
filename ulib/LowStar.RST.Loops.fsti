module LowStar.RST.Loops

open LowStar.Resource
open LowStar.RST
module HS = FStar.HyperStack

inline_for_extraction
val while:
    res:resource
  -> inv: (imem (res.view.inv) -> Type0)
  -> guard: (imem (res.view.inv) -> GTot bool)
  -> test: (unit -> RST bool
                      (res)
                      (fun _ -> res)
                      (requires inv)
                      (ensures fun h0 b h1 -> b == guard h0 /\ h0 == h1))
  -> body: (unit -> RST unit
                      (res)
                      (fun _ -> res)
                      (requires fun h -> guard h)
                      (ensures fun _ _ h -> inv h))
  -> RST unit
        (res)
        (fun _ -> res)
        (requires inv)
        (ensures fun _ _ h -> inv h /\ ~(guard h))
