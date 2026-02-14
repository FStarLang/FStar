module Pulse.Class.PtsTo
#lang-pulse

open FStar.Tactics.Typeclasses { noinst }
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Tactics.V2
open FStar.Ghost

let full_default () : Tac unit = exact (`1.0R)

[@@FStar.Tactics.Typeclasses.fundeps [1]; // The pointer determines the representation
   pulse_unfold]
class has_pts_to (p r : Type) = {
  [@@@pulse_unfold]
  pts_to : p -> (#[full_default()] f : perm) -> r -> slprop;
}

(* Always full permission *)
[@@pulse_unfold]
let ( |-> ) #p #r {| has_pts_to p r |} x y = pts_to #p #r x y

[@@pulse_unfold; pulse_eager_unfold]
let live #p #r {| has_pts_to p r |} (x: p) (#[full_default()] f: perm) =
  exists* y. pts_to x #f y

(* We can always have an erased value. *)
[@@pulse_unfold]
instance pts_to_erased (p r : Type) (_ : has_pts_to p r) : has_pts_to p (erased r) = {
  pts_to = (fun r #f v -> pts_to r #f (reveal v));
}

noeq
type frac a =
  | Frac : f:perm -> a -> frac a

[@@pulse_unfold; noinst]
instance pts_to_frac (p a : Type) (d : has_pts_to p a) : has_pts_to p (frac a) = {
  pts_to = (fun p #f' (Frac f v) -> d.pts_to p #(f' *. f) v);
}

(* Handle lseq by ignoring the refinement. *)
[@@pulse_unfold]
instance pts_to_lseq (p a : Type) (n : nat) (d : has_pts_to p (Seq.seq a)) : has_pts_to p (Seq.lseq a n) = {
  pts_to = d.pts_to;
}

let observe #a (p: a -> slprop) #x :
    stt_ghost a emp_inames (p x) (fun y -> p x ** rewrites_to y x) =
  lift_neutral_ghost #a #emp_inames (return_neutral #a x (fun _ -> p x))

let value_of #p #r {| has_pts_to p r |} (x: p) (#f: perm) (#v: r) =
  observe (pts_to x #f) #v