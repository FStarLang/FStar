module Pulse.Lib.ArraySwap
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

inline_for_extraction noextract [@@noextract_to "krml"]
val array_swap
  (#t: Type0)
  (a: A.array t)
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (#s1 #s2: Ghost.erased (Seq.seq t))
: stt (squash (SZ.v lb <= SZ.v mb /\ SZ.v mb <= SZ.v rb))
  (
    A.pts_to_range a (SZ.v lb) (SZ.v mb) s1 **
    A.pts_to_range a (SZ.v mb) (SZ.v rb) s2
  )
  (fun _ ->
    A.pts_to_range a (SZ.v lb) (SZ.v lb + (SZ.v rb - SZ.v mb)) s2 **
    A.pts_to_range a (SZ.v lb + (SZ.v rb - SZ.v mb)) (SZ.v rb) s1
  )
