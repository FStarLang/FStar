module TotalLowStar.Lib
open TotalST
module B = LowStar.Buffer
module U32 = FStar.UInt32
unfold
let ( .() ) (#a:Type) (b:B.buffer a) (i:U32.t)
  : TotST a
    (requires fun m ->
      B.live m b /\
      U32.v i < B.length b)
    (ensures fun m0 x m1 ->
      m0 == m1 /\
      x == Seq.index (B.as_seq m0 b) (U32.v i))
  = reflect_stack _ _ _ (fun () -> B.index b i)

unfold
let ( .()<- ) (#a:Type) (b:B.buffer a) (i:U32.t) (x:a)
  : TotST unit
    (requires fun m ->
      B.live m b /\
      U32.v i < B.length b)
    (ensures fun m0 _ m1 ->
      let open B in
      not (g_is_null b) /\
      modifies (loc_buffer b) m0 m1 /\
      live m1 b /\
      as_seq m1 b == Seq.upd (as_seq m0 b) (U32.v i) x)
  = reflect_stack _ _ _ (fun () -> B.upd b i x)
