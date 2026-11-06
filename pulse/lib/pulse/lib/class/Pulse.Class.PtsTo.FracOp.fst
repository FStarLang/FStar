module Pulse.Class.PtsTo.FracOp
#lang-pulse

open Pulse.Lib.Core
open Pulse.Class.PtsTo.Base

(* [x |-> Frac f v]: points-to with an explicit permission. This is a separate
   overload of [( |-> )], see Pulse.Class.PtsTo. *)
[@@pulse_unfold]
let ( |-> ) #p #r {| has_pts_to p r |} (x: p) (y: frac r) : slprop =
  match y with
  | Frac f v -> pts_to #p #r x #f v
