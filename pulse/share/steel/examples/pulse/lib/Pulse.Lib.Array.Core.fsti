module Pulse.Lib.Array.Core
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq

val array (a:Type u#0) : Type u#0

val length (#a:Type u#0) (x:array a) : GTot nat

val is_full_array (#a:Type u#0) (x:array a) : prop

val pts_to (#a:Type u#0) (x:array a) (p:perm) (s: Seq.seq a) : vprop

val alloc 
        (#elt: Type)
        (x: elt)
        (n: SZ.t)
  : stt (array elt) 
        (requires emp)
        (ensures fun a ->
            pts_to a full_perm (Seq.create (SZ.v n) x) **
            pure (length a == SZ.v n /\ is_full_array a))

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a p s)
        (ensures fun res ->
            pts_to a p s **
            pure (res == Seq.index s (SZ.v i)))


(* Written x.(i) <- v *)
val op_Array_Assignment
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  : stt unit
        (requires
            pts_to a full_perm s)
        (ensures fun res ->
            pts_to a full_perm (Seq.upd s (SZ.v i) v))

val free
        (#elt: Type)
        (a: array elt)
        (#s: Ghost.erased (Seq.seq elt))
  : stt unit
        (requires
            pts_to a full_perm s **
            pure (is_full_array a))
        (ensures fun _ ->
            emp)