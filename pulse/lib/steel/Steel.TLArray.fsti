module Steel.TLArray

module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32

noextract
val t (a:Type0) : Type0

noextract
val v (#a:Type0) (x : t a) : G.erased (list a)

val length (#a:Type0) (x:t a) : GTot nat

noextract
val create (#a:Type0) (l: list a) :
  Pure (t a)
       (requires  True)
       (ensures fun x ->
         Ghost.reveal (v x) == l /\
         length x == normalize_term (List.Tot.length l))

noextract
val get (#a:Type0) (x: t a) (i:U32.t{U32.v i < length x}) :
  Pure a
    (requires True)
    (ensures fun y ->
      U32.v i < L.length (v x) /\
      y == L.index (v x) (U32.v i))
