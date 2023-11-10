module Steel.TLArray

module G = FStar.Ghost
module L = FStar.List.Tot
module US = FStar.SizeT

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
val get (#a:Type0) (x: t a) (i:US.t{US.v i < length x}) :
  Pure a
    (requires True)
    (ensures fun y ->
      US.v i < L.length (v x) /\
      y == L.index (v x) (US.v i))
