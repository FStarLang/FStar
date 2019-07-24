module LowStar.RST.Loops

open LowStar.Resource
open LowStar.RST
module HS = FStar.HyperStack
module AR = LowStar.RST.Array
module A = LowStar.Array
module U32 = FStar.UInt32
open FStar.Mul

inline_for_extraction
val while:
    res:resource
  -> inv: (res.t -> Type0)
  -> guard: (res.t -> GTot bool)
  -> test: (unit -> RST bool
                      (res)
                      (fun _ -> res)
                      (requires fun h -> inv (sel (view_of res) h))
                      (ensures fun h0 b h1 -> b == guard (sel (view_of res) h0) /\
                               sel (view_of res) h0 == sel (view_of res) h1))
  -> body: (unit -> RST unit
                      (res)
                      (fun _ -> res)
                      (requires fun h -> guard (sel (view_of res) h))
                      (ensures fun _ _ h -> inv (sel (view_of res) h)))
  -> RST unit
        (res)
        (fun _ -> res)
        (requires fun h -> inv (sel (view_of res) h))
        (ensures fun _ _ h -> inv (sel (view_of res) h) /\ ~(guard (sel (view_of res) h)))
