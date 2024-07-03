module Pulse.Lib.Slice
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

val slice : Type0 -> Type0

val len (#t: Type) : slice t -> SZ.t

val pts_to (#t: Type) (s: slice t) (#[exact (`1.0R)] p: perm) (v: Seq.seq t) : vprop

val pts_to_is_small (#a:Type) (x:slice a) (p:perm) (s:Seq.seq a)
  : Lemma (is_small (pts_to x #p s))
          [SMTPat (is_small (pts_to x #p s))]

val pts_to_len (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s #p v)
    (fun _ -> pts_to s #p v ** pure (Seq.length v == SZ.v (len s)))

val is_from_array (#t: Type) (a: array t) (p: perm) (s: slice t) : vprop

val from_array (#t: Type) (mutb: bool) (a: array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (alen: SZ.t {
    SZ.v alen == A.length a /\
    (mutb == true ==> p == 1.0R)
}) : stt (slice t)
    (A.pts_to a #p v)
    (fun s ->
        pts_to s #p v **
        is_from_array a p s
    )

val to_array (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) (#a: array t) : stt_ghost unit emp_inames
    (pts_to s #p v ** is_from_array a p s)
    (fun _ -> A.pts_to a #p v)

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a #p s)
        (ensures fun res ->
            pts_to a #p s **
            pure (res == Seq.index s (SZ.v i)))


(* Written a.(i) <- v *)
val op_Array_Assignment
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  : stt unit
        (requires
            pts_to a s)
        (ensures fun res ->
            pts_to a (Seq.upd s (SZ.v i) v))

val share
  (#a:Type)
  (arr:slice a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p s)
      (ensures fun _ -> pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (arr:slice a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p0 s0 ** pts_to arr #p1 s1)
      (ensures fun _ -> pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1))

val is_split (#t: Type) (s: slice t) (p: perm) (i: SZ.t) (left: slice t) (right: slice t) : vprop

val is_split_is_small (#t: Type) (s: slice t) (p: perm) (i: SZ.t) (left: slice t) (right: slice t)
  : Lemma (is_small (is_split s p i left right))
          [SMTPat (is_small (is_split s p i left right))]

let split_precond
  (#t: Type) (mutb: bool) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
: Tot prop
= SZ.v i <= Seq.length v /\ (mutb == true ==> p == 1.0R)

let split_post'
    (#t: Type) (s: slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: slice t)
    (s2: slice t)
: Tot vprop
=       exists* v1 v2 .
            pts_to s1 #p v1 **
            pts_to s2 #p v2 **
            is_split s p i s1 s2 **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )

let split_post
    (#t: Type) (s: slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: (slice t & slice t))
: Tot vprop
= let (s1, s2) = res in
    split_post' s p v i s1 s2

val split (#t: Type) (mutb: bool) (s: slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t) : stt (slice t & slice t)
    (requires pts_to s #p v ** pure (split_precond mutb p v i))
    (ensures fun res -> split_post s p v i res)

val join (#t: Type) (s1: slice t) (#p: perm) (#v1: Seq.seq t) (s2: slice t) (#v2: Seq.seq t) (#i: SZ.t) (s: slice t) : stt_ghost unit emp_inames
    (pts_to s1 #p v1 ** pts_to s2 #p v2 ** is_split s p i s1 s2)
    (fun _ -> pts_to s #p (Seq.append v1 v2))
