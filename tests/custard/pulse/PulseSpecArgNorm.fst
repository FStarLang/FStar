module PulseSpecArgNorm
#lang-pulse
(* Issue #4828.  An argument in a position extraction erases is not
   normalized: [p14 x] and [q14 y] each unfold to 2^14 conjuncts, which
   exceeds the --custard_norm_budget the Makefile sets.  An [slprop]
   implicit of a concrete [fn] and a [prop] implicit of an ordinary function
   are both such positions. *)
open Pulse

unfold let p0 (x:int) : slprop = pure (x == x)
unfold let p1 (x:int) : slprop = p0 x ** p0 (x + 1)
unfold let p2 (x:int) : slprop = p1 x ** p1 (x + 1)
unfold let p3 (x:int) : slprop = p2 x ** p2 (x + 1)
unfold let p4 (x:int) : slprop = p3 x ** p3 (x + 1)
unfold let p5 (x:int) : slprop = p4 x ** p4 (x + 1)
unfold let p6 (x:int) : slprop = p5 x ** p5 (x + 1)
unfold let p7 (x:int) : slprop = p6 x ** p6 (x + 1)
unfold let p8 (x:int) : slprop = p7 x ** p7 (x + 1)
unfold let p9 (x:int) : slprop = p8 x ** p8 (x + 1)
unfold let p10 (x:int) : slprop = p9 x ** p9 (x + 1)
unfold let p11 (x:int) : slprop = p10 x ** p10 (x + 1)
unfold let p12 (x:int) : slprop = p11 x ** p11 (x + 1)
unfold let p13 (x:int) : slprop = p12 x ** p12 (x + 1)
unfold let p14 (x:int) : slprop = p13 x ** p13 (x + 1)

unfold let q0 (x:int) : prop = x == x
unfold let q1 (x:int) : prop = q0 x /\ q0 (x + 1)
unfold let q2 (x:int) : prop = q1 x /\ q1 (x + 1)
unfold let q3 (x:int) : prop = q2 x /\ q2 (x + 1)
unfold let q4 (x:int) : prop = q3 x /\ q3 (x + 1)
unfold let q5 (x:int) : prop = q4 x /\ q4 (x + 1)
unfold let q6 (x:int) : prop = q5 x /\ q5 (x + 1)
unfold let q7 (x:int) : prop = q6 x /\ q6 (x + 1)
unfold let q8 (x:int) : prop = q7 x /\ q7 (x + 1)
unfold let q9 (x:int) : prop = q8 x /\ q8 (x + 1)
unfold let q10 (x:int) : prop = q9 x /\ q9 (x + 1)
unfold let q11 (x:int) : prop = q10 x /\ q10 (x + 1)
unfold let q12 (x:int) : prop = q11 x /\ q11 (x + 1)
unfold let q13 (x:int) : prop = q12 x /\ q12 (x + 1)
unfold let q14 (x:int) : prop = q13 x /\ q13 (x + 1)

let id_with_spec (#p:prop) (x:int) : int = x

fn step (#p:slprop) (y:int)
  requires emp
  returns r:int
  ensures emp
{
  id_with_spec #(q14 y) y
}

fn main (x:int)
  requires emp
  returns r:int
  ensures emp
{
  step #(p14 x) x
}
