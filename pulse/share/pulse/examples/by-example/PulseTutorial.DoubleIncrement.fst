module PulseTutorial.DoubleIncrement
#lang-pulse
open Pulse
open FStar.Preorder
open Pulse.Class.PtsTo
module MR = Pulse.Lib.MonotonicGhostRef

atomic
fn incr_atomic (r:ref int) (#n:erased int)
requires r |-> n
returns i:int
ensures r |-> i 
ensures pure (i == n + 1)
{ admit() } //for this example, assume we have a primitive atomic increment operation

(* We have a library of PCMs that allows building a monotonic reference out of any preorder *)

(* For a mononotonic counter: the preorder is <= *)
let increases : preorder int = fun x y -> (x <= y == true)
(* The type of ghost reference to a monotonic counter *)
let ghost_monotonic_ref = MR.mref increases

// Ghost monotonic references come with two main assertions:
// 1. MR.pts_to mr #f v: the ghost reference points to value v (with fractionn f, but we'll just use 1.0R)
// 2. MR.snapshot mr v: stable knowledge that the ghost reference's value is at least v (this is freely duplicable)

(* The core invariant, related the current value of the counter to the value of the ghost reference *)
[@@pulse_unfold]
let inv_core (x:ref int) (mr:ghost_monotonic_ref)
: timeless_slprop
= exists* (j:int). (x |-> j) ** MR.pts_to mr #1.0R j


fn increment (x:ref int) (#mr:ghost_monotonic_ref) (#i:iname) (#v0:erased int)
requires inv i (inv_core x mr) //x and mr are related, i.e., their values are equal
requires MR.snapshot mr v0     //and the value pf m,r
ensures inv i (inv_core x mr)  //x and mr are still related
ensures exists* v1. MR.snapshot mr v1 ** pure (v1 >= v0 + 1) //and value of mr is at least one more than it was before
{
    with_invariants unit emp_inames i (inv_core x mr) (MR.snapshot mr v0)
        (fun _ -> exists* v1. MR.snapshot mr v1 ** pure (v1 >= v0 + 1))
    fn _ { //open the invariant i, so we can use it 
        MR.recall_snapshot mr; //Ghost step: this tells us that v0 <= current value of x
        drop_ (MR.snapshot mr v0); //we don't need the snapshot of v0 anymore
        let res = incr_atomic x; //to the actual increment
        MR.update mr res; //Ghost step: update the ghost reference to the new value
        MR.take_snapshot mr #1.0R res; //Take a new snapshot of the ghost reference at the current value
    }
}

//And here's a double increment
fn double_increment (x:ref int) (#mr:ghost_monotonic_ref) (#i:iname) (#v0:erased int)
preserves inv i (inv_core x mr)
requires MR.snapshot mr v0
ensures exists* v1. MR.snapshot mr v1 ** pure (v1 >= v0 + 2) // value of mr is at least two more than it was before
{
    increment x;
    increment x;
}