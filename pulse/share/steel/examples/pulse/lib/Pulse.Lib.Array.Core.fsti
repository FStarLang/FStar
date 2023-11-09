module Pulse.Lib.Array.Core
open FStar.Tactics.V2
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq

val array ([@@@strictly_positive] a:Type u#0) : Type u#0

val length (#a:Type u#0) (x:array a) : GTot nat

type elseq (a:Type) (l:SZ.t) = s:erased (Seq.seq a) { Seq.length s == SZ.v l }

type larray t (n:nat) = a:array t { length a == n }

val is_full_array (#a:Type u#0) (x:array a) : prop

val pts_to (#a:Type u#0) (x:array a) (#[exact (`full_perm)] p:perm) (s: Seq.seq a) : vprop

val pts_to_len (#t:Type0) (a:array t) (#p:perm) (#x:Seq.seq t)
    : stt_ghost unit emp_inames
          (pts_to a #p x)
          (fun _ → pts_to a #p x ** pure (length a == Seq.length x))

val alloc 
        (#elt: Type)
        (x: elt)
        (n: SZ.t)
  : stt (array elt) 
        (requires emp)
        (ensures fun a ->
            pts_to a (Seq.create (SZ.v n) x) **
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
            pts_to a #p s)
        (ensures fun res ->
            pts_to a #p s **
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
            pts_to a s)
        (ensures fun res ->
            pts_to a (Seq.upd s (SZ.v i) v))

val free
        (#elt: Type)
        (a: array elt)
        (#s: Ghost.erased (Seq.seq elt))
  : stt unit
        (requires
            pts_to a s **
            pure (is_full_array a))
        (ensures fun _ ->
            emp)

val with_local
  (#a:Type0)
  (init:a)
  (len:SZ.t)
  (#pre:vprop)
  (ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) **
                                     (pure (is_full_array arr) **
                                      pure (length arr == SZ.v len))))
                                   (fun r -> post r ** exists_ (pts_to arr)))
  : stt ret_t pre post