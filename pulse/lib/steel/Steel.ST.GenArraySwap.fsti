module Steel.ST.GenArraySwap
open Steel.ST.Util

module SZ = FStar.SizeT

let array_pts_to_t
  (t: Type)
: Tot Type
= Ghost.erased (Seq.seq t) -> Tot vprop

inline_for_extraction
let array_index_t
  (#t: Type)
  (pts_to: array_pts_to_t t)
: Tot Type
=
  (s: Ghost.erased (Seq.seq t)) ->
  (n: SZ.t) ->
  (i: SZ.t) ->
  ST t
    (pts_to s)
    (fun _ -> pts_to s)
    (
      SZ.v i < Seq.length s /\
      SZ.v n == Seq.length s
    )
    (fun x ->
      SZ.v i < Seq.length s /\
      x == Seq.index s (SZ.v i)
    )

inline_for_extraction
let array_upd_t
  (#t: Type)
  (pts_to: array_pts_to_t t)
: Tot Type
=
  (s: Ghost.erased (Seq.seq t)) ->
  (n: SZ.t) ->
  (i: SZ.t) ->
  (x: t) ->
  ST (Ghost.erased (Seq.seq t))
    (pts_to s)
    (fun s' -> pts_to s')
    (
      SZ.v n == Seq.length s /\
      SZ.v i < SZ.v n
    )
    (fun s' ->
      SZ.v n == Seq.length s /\
      SZ.v i < SZ.v n /\
      Ghost.reveal s' == Seq.upd s (SZ.v i) x
    )

inline_for_extraction
val array_swap_gen
  (#t: Type0)
  (#pts_to: array_pts_to_t t)
  (index: array_index_t pts_to)
  (upd: array_upd_t pts_to)
  (s0: Ghost.erased (Seq.seq t))
  (n: SZ.t)
  (l: SZ.t)
: ST (Ghost.erased (Seq.seq t))
    (pts_to s0)
    (fun s -> pts_to s)
    (
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n
    )
    (fun s ->
      SZ.v n == Seq.length s0 /\
      SZ.v l <= SZ.v n /\
      s `Seq.equal` (Seq.slice s0 (SZ.v l) (SZ.v n) `Seq.append` Seq.slice s0 0 (SZ.v l))
    )
