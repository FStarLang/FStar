module Pulse.Lib.Pervasives
include Pulse.Main
include Pulse.Lib.Core
include Pulse.Lib.Array
include Pulse.Lib.Reference
include Steel.FractionalPermission
include FStar.Ghost

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val perform
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : stt a pre post
let perform f = f ()

val perform_ghost
  (#a #is #pre #post : _)
  (f : unit -> stt_ghost is a pre post)
  : stt_ghost is a pre post
let perform_ghost f = f ()

val perform_atomic
  (#a #is #pre #post : _)
  (f : unit -> stt_atomic is a pre post)
  : stt_atomic is a pre post
let perform_atomic f = f ()

(* TEMPORARY! REMOVE! *)
let inames_ext (is1 is2 : inames)
  : Lemma (requires forall i. Set.mem i is1 <==> Set.mem i is2)
          (ensures is1 == is2)
          [SMTPat (is1 == is2)]
  = Set.lemma_equal_intro is1 is2

let inames_join_emp_r (is1 : inames)
  : Lemma (join_inames is1 emp_inames == is1) [SMTPat (join_inames is1 emp_inames)]
  = Set.lemma_equal_intro (join_inames is1 emp_inames) is1

let inames_join_emp_l (is1 : inames)
  : Lemma (join_inames emp_inames is1 == is1) [SMTPat (join_inames emp_inames is1)]
  = Set.lemma_equal_intro (join_inames emp_inames is1) is1

let inames_join_self (is1 : inames)
  : Lemma (join_inames is1 is1 == is1) [SMTPat (join_inames is1 is1)]
  = Set.lemma_equal_intro (join_inames is1 is1) is1

assume val ref_apply (#a #b:Type) (r:ref (a -> b)) (x:a) (#f:erased (a -> b))
  : stt b
    (requires pts_to r f)
    (ensures fun y -> pts_to r f ** pure (y == (reveal f) x))

let tfst (x:'a & 'b & 'c) : 'a = Mktuple3?._1 x
let tsnd (x:'a & 'b & 'c) : 'b = Mktuple3?._2 x
let tthd (x:'a & 'b & 'c) : 'c = Mktuple3?._3 x
