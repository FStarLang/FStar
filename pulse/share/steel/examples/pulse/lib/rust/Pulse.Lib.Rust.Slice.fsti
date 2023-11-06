module Pulse.Lib.Rust.Slice

open FStar.Ghost
open Steel.FractionalPermission
open Pulse.Lib.Core

module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = FStar.Tactics.V2

module V = Pulse.Lib.Rust.Vec
module A = Pulse.Lib.Rust.Array

val slice ([@@@strictly_positive] a:Type0) : Type0

val length (#a:Type0) (x:slice a) : GTot nat

val pts_to (#a:Type0) (x:slice a) (#[T.exact (`full_perm)] p:perm) (s: Seq.seq a) : vprop

val pts_to_len (#a:Type0) (x:slice a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (pts_to x s)
      (fun _ → pts_to x s ** pure (length x == Seq.length s))

(* Written x.(i) *)
val op_Array_Access
  (#a:Type0)
  (x:slice a)
  (i:SZ.t)
  (#p:perm)
  (#s:Ghost.erased (Seq.seq a){SZ.v i < Seq.length s})
  : stt a
     (requires pts_to x #p s)
     (ensures fun res ->
        pts_to x #p s **
        pure (res == Seq.index s (SZ.v i)))

(* Written x.(i) <- v *)
val op_Array_Assignment
  (#a:Type0)
  (x:slice a)
  (i:SZ.t)
  (v:a)
  (#s:Ghost.erased (Seq.seq a) {SZ.v i < Seq.length s})
  : stt unit
      (requires pts_to x s)
      (ensures fun res ->
         pts_to x (Seq.upd s (SZ.v i) v))

val vec_as_slice (#a:Type0) (x:V.vec a) : slice a

val to_vec_pts_to (#a:Type0) (x:V.vec a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a)
  : stt_ghost unit emp_inames
      (requires pts_to (vec_as_slice x) s)
      (ensures fun _ -> V.pts_to x s)

val vec_to_slice_pts_to (#a:Type0) (x:V.vec a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a)
  : stt_ghost unit emp_inames
      (requires V.pts_to x s)
      (ensures fun _ -> pts_to (vec_as_slice x) s)

val array_as_slice (#a:Type0) (x:A.array a) : slice a

val to_array_pts_to (#a:Type0) (x:A.array a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a)
  : stt_ghost unit emp_inames
      (requires pts_to (array_as_slice x) s)
      (ensures fun _ -> A.pts_to x s)

val array_to_slice_pts_to (#a:Type0) (x:A.array a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a)
  : stt_ghost unit emp_inames
      (requires A.pts_to x s)
      (ensures fun _ -> pts_to (array_as_slice x) s)
