module Pulse.Class.PtsTo
#lang-pulse

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Tactics.V2
open FStar.Ghost

let full_default () : Tac unit = exact (`1.0R)

[@@FStar.Tactics.Typeclasses.fundeps [1]] // The pointer determines the representation
class has_pts_to (p r : Type) = {
  [@@@pulse_unfold]
  pts_to : p -> (#[full_default()] f : perm) -> r -> slprop;
}

(* Always full permission *)
[@@pulse_unfold]
let ( |-> ) #p #r {| has_pts_to p r |} = pts_to #p #r

(* We can always have an erased value. *)
[@@pulse_unfold]
instance pts_to_erased (p r : Type) (_ : has_pts_to p r) : has_pts_to p (erased r) = {
  pts_to = (fun r #f v -> pts_to r #f (reveal v));
}
