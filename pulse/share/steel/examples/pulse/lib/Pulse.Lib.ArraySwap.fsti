module Pulse.Lib.ArraySwap
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

noextract [@@noextract_to "krml"]
let array_swap_post
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (mb': SZ.t)
: Tot prop
=
      SZ.v lb <= SZ.v mb /\
      SZ.v mb <= SZ.v rb /\
      SZ.v mb' == SZ.v lb + (SZ.v rb - SZ.v mb)

inline_for_extraction noextract [@@noextract_to "krml"]
val array_swap
  (#t: Type0)
  (a: A.array t)
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (#s1 #s2: Ghost.erased (Seq.seq t))
: stt SZ.t
  (
    A.pts_to_range a (SZ.v lb) (SZ.v mb) s1 **
    A.pts_to_range a (SZ.v mb) (SZ.v rb) s2
  )
  (fun mb' ->
    A.pts_to_range a (SZ.v lb) (SZ.v mb') s2 **
    A.pts_to_range a (SZ.v mb') (SZ.v rb) s1 **
    pure (array_swap_post lb rb mb mb')
  )
