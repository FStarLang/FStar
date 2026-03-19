(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module AuxPredicate
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* This example illustrates how to work with auxiliary predicates.
   The style is quite explicit, with folds and unfolds.
   It could be improved by automated support for foldig & unfolding
   in the prover *)

// Defining a slprop using F* syntax. We do not yet allow
// writing Pulse syntax for slprops in predicates 
let my_inv (r:R.ref int) : slprop
  = exists* v.
      pts_to r v ** 
      pure ( (v==0 \/ v == 1) )
    



fn invar_introduces_ghost (r:R.ref int)
  requires pts_to r 0
  ensures  pts_to r 1
{
  r := 0;

  fold (my_inv r); //to prove the precondition of the while loop

  while 
   (  //unfold the predicate to expose its contents to the prover context
      unfold my_inv;
      let vr = !r;
      let res = (vr = 0);
      //show that the condition restores the invariant by explicitly folding it back
      res
   )
  invariant my_inv r
  {
    // Same in the body;
    // unfold to expose it
    r := 1;
    // fold it back to show its preserved
    fold (my_inv r)
  };

  // unfold after the loop for the postcondition 
}



// If you don't introduce the indirection of my_inv
// it just works without further ado

fn invar_introduces_ghost_alt (r:R.ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  r := 0;

  while (let vr = !r; (vr = 0))
    invariant live r
    invariant pure (!r == 0 \/ !r == 1)
  {
    r := 1;
  }
}
