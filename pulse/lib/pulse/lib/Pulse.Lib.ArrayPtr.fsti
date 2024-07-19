module Pulse.Lib.ArrayPtr
open FStar.Tactics.V2
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module A = Pulse.Lib.Array

(* This module can be used only for Pulse programs extracted to C, not Rust. *)

val ptr : Type0 -> Type0

[@@erasable]
val footprint : Type0 -> Type0

val pts_to (#t: Type) (s: ptr t) (#[exact (`1.0R)] p: perm) (fp: footprint t) (v: Seq.seq t) : slprop

val pts_to_is_slprop2 (#a:Type) (x:ptr a) (p:perm) (fp: footprint a) (s:Seq.seq a)
  : Lemma (is_slprop2 (pts_to x #p fp s))
          [SMTPat (is_slprop2 (pts_to x #p fp s))]

val is_from_array (#t: Type) (p: perm) (fp: footprint t) (a: A.array t) : slprop

val from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) : stt (ptr t)
    (A.pts_to a #p v)
    (fun s -> exists* fp . pts_to s #p fp v ** is_from_array p fp a)

val to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#fp: footprint t) (#v: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s #p fp v ** is_from_array p fp a ** pure (
        Seq.length v == A.length a
    ))
    (fun _ -> A.pts_to a #p v)

(* Written x.(i) *)
val op_Array_Access
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (#p: perm)
        (#fp: footprint t)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  : stt t
        (requires
            pts_to a #p fp s)
        (ensures fun res ->
            pts_to a #p fp s **
            pure (res == Seq.index s (SZ.v i)))

(* Written a.(i) <- v *)
val op_Array_Assignment
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (v: t)
        (#fp: footprint t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  : stt unit
        (requires
            pts_to a fp s)
        (ensures fun res ->
            pts_to a fp (Seq.upd s (SZ.v i) v))

val share
  (#a:Type)
  (arr:ptr a)
  (#s:Ghost.erased (Seq.seq a))
  (#fp: footprint a)
  (#p:perm)
: stt_ghost unit emp_inames
      (requires pts_to arr #p fp s)
      (ensures fun _ -> pts_to arr #(p /. 2.0R) fp s ** pts_to arr #(p /. 2.0R) fp s)

[@@allow_ambiguous]
val gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  (#fp: footprint a)
: stt_ghost unit emp_inames
      (requires pts_to arr #p0 fp s0 ** pts_to arr #p1 fp s1)
      (ensures fun _ -> pts_to arr #(p0 +. p1) fp s0 ** pure (s0 == s1))

val adjacent (#t: Type): footprint t -> footprint t -> prop

val merge (#t: Type): (fp1: footprint t) -> (fp2: footprint t {adjacent fp1 fp2}) -> footprint t

val merge_assoc (#t: Type): (fp1: footprint t) -> (fp2: footprint t) -> (fp3: footprint t) -> Lemma
    (ensures (
        ((adjacent fp1 fp2 /\ adjacent (merge fp1 fp2) fp3) <==> (adjacent fp1 fp2 /\ adjacent fp2 fp3)) /\
        ((adjacent fp2 fp3 /\ adjacent fp1 (merge fp2 fp3)) <==> (adjacent fp1 fp2 /\ adjacent fp2 fp3)) /\
        ((adjacent fp1 fp2 /\ adjacent fp2 fp3) ==> 
            merge (merge fp1 fp2) fp3 == merge fp1 (merge fp2 fp3)
        )
    ))
    [SMTPatOr [
        [SMTPat (adjacent fp1 fp2); SMTPat (adjacent (merge fp1 fp2) fp3)];
        [SMTPat (adjacent fp2 fp3); SMTPat (adjacent fp1 (merge fp2 fp3))];
        [SMTPat (adjacent fp1 fp2); SMTPat (adjacent fp2 fp3)];
    ]]

let split_postcond
    (#t: Type) (fp: footprint t) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (v1: Seq.seq t) (v2: Seq.seq t) (fp1: footprint t) (fp2: footprint t)
: Tot prop
=
                adjacent fp1 fp2 /\
                merge fp1 fp2 == fp /\
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)

val split (#t: Type) (s: ptr t) (#p: perm) (#fp: footprint t) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t) : stt (ptr t)
    (requires pts_to s #p fp v ** pure (SZ.v i <= Seq.length v))
    (ensures fun s' ->
        exists* v1 v2 fp1 fp2 .
            pts_to s #p fp1 v1 **
            pts_to s' #p fp2 v2 **
            pure (split_postcond fp v i v1 v2 fp1 fp2)
    )

val join (#t: Type) (s1: ptr t) (#p: perm) (#fp1: footprint t) (#v1: Seq.seq t) (s2: ptr t) (#fp2: footprint t {adjacent fp1 fp2}) (#v2: Seq.seq t) : stt_ghost unit emp_inames
    (pts_to s1 #p fp1 v1 ** pts_to s2 #p fp2 v2)
    (fun _ -> pts_to s1 #p (merge fp1 fp2) (Seq.append v1 v2))
