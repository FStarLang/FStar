module Pulse.Class.PtsTo
#lang-pulse

include Pulse.Class.PtsTo.FracOp
include Pulse.Class.PtsTo.Base
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost

(* [( |-> )] is overloaded: Pulse.Class.PtsTo.Base.( |-> ) takes a [y:r] and
   means full permission; Pulse.Class.PtsTo.FracOp.( |-> ) takes a
   [Frac f v : frac r]. The former is included last, so it is the scope-order
   default, e.g. for [exists* y. x |-> y]. The latter is chosen when the
   right-hand side has type [frac _], being the more specific.

   There are no instances for [erased r] or [Seq.lseq a n]: the class has a
   functional dependency [p -> r], so [r] is resolved from the pointer before
   the right-hand side is checked, and [reveal] or refinement subtyping
   takes care of those. *)

[@@pulse_unfold; pulse_eager_unfold]
let live #p #r {| has_pts_to p r |} (x: p) (#[full_default()] f: perm) =
  exists* y. pts_to x #f y

let observe #a (p: a -> slprop) #x :
    stt_ghost (erased a) emp_inames (p x) (fun y -> p x ** rewrites_to y (hide x)) =
  lift_neutral_ghost #_ #emp_inames (return_neutral #_ (hide x) (fun _ -> p x))

let value_of #p #r {| has_pts_to p r |} (x: p) (#f: perm) (#v: r) =
  observe (pts_to x #f) #v
