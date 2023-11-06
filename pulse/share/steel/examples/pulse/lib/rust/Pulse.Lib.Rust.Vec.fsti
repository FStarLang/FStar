module Pulse.Lib.Rust.Vec

open FStar.Ghost
open Steel.FractionalPermission
open Pulse.Lib.Core

module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = FStar.Tactics.V2

val vec ([@@@strictly_positive] a:Type0) : Type0

val length (#a:Type0) (x:vec a) : GTot nat

val pts_to (#a:Type0) (x:vec a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a) : vprop

val pts_to_len (#a:Type0) (x:vec a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (pts_to x #p s)
      (fun _ → pts_to x #p s ** pure (length x == Seq.length s))

val alloc 
  (#a:Type0)
  (x:a)
  (n:SZ.t)
  : stt (vec a) 
      (requires emp)
      (ensures fun v ->
         pts_to v (Seq.create (SZ.v n) x) **
         pure (length v == SZ.v n))

(* Written x.(i) *)
val op_Array_Access
  (#a:Type0)
  (x:vec a)
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
  (x:vec a)
  (i:SZ.t)
  (v:a)
  (#s:Ghost.erased (Seq.seq a) {SZ.v i < Seq.length s})
  : stt unit
      (requires pts_to x s)
      (ensures fun res ->
         pts_to x (Seq.upd s (SZ.v i) v))

val free (#a:Type0) (x:vec a) (#s:Ghost.erased (Seq.seq a))
  : stt unit
      (requires pts_to x s)
      (ensures fun _ -> emp)
