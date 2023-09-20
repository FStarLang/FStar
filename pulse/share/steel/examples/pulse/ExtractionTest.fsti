module ExtractionTest
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

val test_write_10_pub (x:ref U32.t) (#v:erased U32.t)
  : stt unit (pts_to x v) (fun _ -> pts_to x 0ul)

