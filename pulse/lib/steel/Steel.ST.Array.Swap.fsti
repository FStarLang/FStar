module Steel.ST.Array.Swap
open Steel.ST.Util
include Steel.ST.Array

module SZ = FStar.SizeT

val swap
  (#t: Type0)
  (#s0: Ghost.erased (Seq.seq t))
  (a: array t)
  (n: SZ.t)
  (l: SZ.t)
: ST (Ghost.erased (Seq.seq t))
    (pts_to a full_perm s0)
    (fun s -> pts_to a full_perm s)
    (
      SZ.v n == length a /\
      SZ.v l <= SZ.v n
    )
    (fun s ->
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n /\
      s `Seq.equal` (Seq.slice s0 (SZ.v l) (SZ.v n) `Seq.append` Seq.slice s0 0 (SZ.v l))
    )
