module Pulse.Lib.Vec

open FStar.Ghost
open Steel.FractionalPermission
open Pulse.Lib.Core

module SZ = FStar.SizeT
module Seq = FStar.Seq
module T = FStar.Tactics.V2

module A = Pulse.Lib.Array.Core

val vec ([@@@strictly_positive] a:Type0) : Type u#0

val length (#a:Type0) (v:vec a) : GTot nat

val is_full_vec (#a:Type0) (v:vec a) : prop

val pts_to (#a:Type0) (v:vec a) (#[T.exact (`full_perm)] p:perm) (s:Seq.seq a) : vprop

val pts_to_len (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (pts_to v #p s)
      (fun _ → pts_to v #p s ** pure (length v == Seq.length s))

val alloc 
  (#a:Type0)
  (x:a)
  (n:SZ.t)
  : stt (vec a)
        (requires emp)
        (ensures fun v ->
           pts_to v (Seq.create (SZ.v n) x) **
           pure (length v == SZ.v n /\ is_full_vec v))

(* Written x.(i) *)
val op_Array_Access
  (#a: Type0)
  (v:vec a)
  (i:SZ.t)
  (#p:perm)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  : stt a
        (requires pts_to v #p s)
        (ensures fun res ->
           pts_to v #p s **
           pure (res == Seq.index s (SZ.v i)))


(* Written x.(i) <- v *)
val op_Array_Assignment
  (#a:Type0)
  (v:vec a)
  (i:SZ.t)
  (x:a)
  (#s:Ghost.erased (Seq.seq a) { SZ.v i < Seq.length s })
  : stt unit
        (requires pts_to v s)
        (ensures fun _ -> pts_to v (Seq.upd s (SZ.v i) x))

val free
  (#a:Type0)
  (v:vec a)
  (#s:Ghost.erased (Seq.seq a))
  : stt unit
        (requires
           pts_to v s **
           pure (is_full_vec v))
        (ensures fun _ -> emp)

val vec_to_array (#a:Type0) (v:vec a) : A.array a

val to_array_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (pts_to v #p s)
      (fun _ → A.pts_to (vec_to_array v) #p s)

val to_vec_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  : stt_ghost unit emp_inames
      (A.pts_to (vec_to_array v) #p s)
      (fun _ → pts_to v #p s)
