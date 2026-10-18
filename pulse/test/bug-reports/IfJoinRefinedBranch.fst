module IfJoinRefinedBranch
#lang-pulse
open Pulse

(* The postcondition of the conditional joins the values of [res] in its
   branches with an unannotated [match], which Core must check against the
   expected type rather than type at its first branch, a refinement of
   [UInt32.t] that the other branch, [g c], does not have. *)

let g (a: UInt32.t) : r:UInt32.t{r == a} = a

fn f (c: UInt32.t)
  returns r: UInt32.t
{
  let mut res : UInt32.t = 0ul;
  if (c = 2ul) {
    res := 0ul;
  } else {
    res := g c;
  };
  !res
}
