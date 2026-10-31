module RewriteEachMatchReturns

#lang-pulse
open Pulse

(* The elaborator annotates a match with the type its branches are checked
   against, so the [if] in [q] (checked at [small]) and the pattern below
   (checked at no particular type) differ in their [returns] annotations.
   [rewrite each] matches up to them. *)
let small = n:nat{n < 10}
assume val p : small -> slprop
let q (b:bool) : slprop = p (if b then 1 else 2)

fn test (b:bool) (x:small)
  requires q b ** pure (x == (if b then 1 else 2))
  ensures p x
{
  unfold (q b);
  rewrite each (if b then 1 else 2) as x;
}
