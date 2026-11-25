module Pulse.Class.PtsTo.Base
#lang-pulse

open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Tactics.V2

let full_default () : Tac unit = exact (`1.0R)

(* Instances of this class must be determined by the pointer type alone:
   instance search for [has_pts_to p ?r] must not depend on [?r]. *)
[@@FStar.Tactics.Typeclasses.fundeps [1]; // The pointer determines the representation
   pulse_unfold]
class has_pts_to (p r : Type) = {
  [@@@pulse_unfold]
  pts_to : p -> (#[full_default()] f : perm) -> r -> slprop;
}

noeq
type frac a =
  | Frac : f:perm -> a -> frac a

(* [x |-> y]: points-to with full permission. Overloaded with
   Pulse.Class.PtsTo.FracOp.( |-> ) in Pulse.Class.PtsTo, see there. *)
[@@pulse_unfold]
let ( |-> ) #p #r {| has_pts_to p r |} (x: p) (y: r) = pts_to #p #r x y
