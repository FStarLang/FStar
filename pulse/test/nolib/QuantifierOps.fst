module QuantifierOps

#lang-pulse
open Pulse.Nolib

let ( exists* ) : #a:Type -> (a -> slprop) -> slprop = admit()
let ( forall+ ) : #a:Type -> (a -> slprop) -> slprop = admit()

let test =
  forall+ (x : int).
    exists* (y : int).
      emp

let test2 =
  exists* (y : int).
    forall+ (x : int).
      emp

fn def ()
  preserves
    forall+ (x : int).
      exists* (y : int).
        emp
{
  ()
}
