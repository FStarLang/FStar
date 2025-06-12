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

module PulseByExample

open Pulse.Lib.Core

(* 
  Things to note:
  - syntax extension notation
  - 1 or more arguments
  - precondition and postcondition
*)

//SNIPPET_START: five
#lang-pulse

let fstar_five : int = 5

fn five ()
  requires emp
  returns n:int
  ensures pure (n == 5)
{ 
  fstar_five
}


let pulse_five_in_fstar = five ()
//SNIPPET_END: five


fn five_alt ()
  requires emp
  returns n:(n:int { n == 5 })
  ensures emp
{ 
  5
}


open Pulse.Lib.Reference
module R = Pulse.Lib.Reference

(* 
  Things to note:
  - separating conjunction
  - tick for erased, implicit values
  - default full permission
  - heap reference, read and write
*)
fn ref_swap (r1:ref int) (r2:ref int)
  requires
    R.pts_to r1 'n1 **
    R.pts_to r2 'n2
  ensures
    R.pts_to r1 'n2 **
    R.pts_to r2 'n1

{
  let v1 = !r1;
  r1 := !r2;
  r2 := v1
}

fn ref_non_zero (r1:ref int) (n1:Ghost.erased int)
requires
  R.pts_to r1 n1
returns b:bool
ensures R.pts_to r1 n1 ** pure (b == (Ghost.reveal n1 <> 0))
{
  (0 <> !r1);
}

fn id (r:ref int)
  requires
    R.pts_to r 'n
  returns r':ref int
  ensures
    R.pts_to r' 'n ** pure (r == r')
{
  r;
}

fn set (r:ref int) (x:int)
requires R.pts_to r 'n
ensures R.pts_to r x
{
  r := x;
}

fn go () () ()
{
  ()
}

fn test (r:ref int)
  requires 
    R.pts_to r 'n
  ensures
    R.pts_to r 2
{
  go (set r 1) (set r 4) (set r 2);
}

open Pulse.Lib.Array
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
open Pulse.Lib.BoundedIntegers

(* 
  Things to note:
  - heap array, read and write
  - exists* and forall in spec
  - machine integers, ops on bounded integers
*)


fn arr_swap (#t:Type0) (n i j:SZ.t) (a:larray t (v n))
  requires
    A.pts_to a 's0 **
    pure (Seq.length 's0 == v n /\ i < n /\ j < n)
  ensures
    exists* s. 
    A.pts_to a s **
    pure (Seq.length 's0 == v n /\ Seq.length s == v n /\ i < n /\ j < n
       /\ (forall (k:nat). k < v n /\ k <> v i /\ k <> v j ==> Seq.index 's0 k == Seq.index s k)
       /\ Seq.index 's0 (v i) == Seq.index s (v j)
       /\ Seq.index 's0 (v j) == Seq.index s (v i))  
{
  let vi = a.(i);
  a.(i) <- a.(j);
  a.(j) <- vi;
}


(* 
  Things to note:
  - control flow: while loop, if
  - mutable local reference, read and write
  - variable permission
*)

fn max (n:SZ.t) (a:larray nat (v n))
  requires
    A.pts_to a #'p 's **
    pure (Seq.length 's == v n)
  returns r:nat
  ensures
    A.pts_to a #'p 's **
    pure (Seq.length 's == v n /\
          (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i : SZ.t = 0sz;
  let mut max : nat = 0;
  while ((!i < n))
  invariant b. exists* (vi:SZ.t) (vmax:nat).
    A.pts_to a #'p 's **
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax)
       /\ b == (vi < n))
  {
    let vi = !i;
    let v = a.(vi);
    i := vi + 1sz;
    if (v > !max) {
      max := v;
    }
  };
  !max;
}

//this option should become the default, once I shake out the handling of address-taking
#push-options "--ext 'pulse:rvalues'"

fn max_alt (n:SZ.t) (a:larray nat (v n))
  requires
    A.pts_to a #'p 's **
    pure (Seq.length 's == v n)
  returns r:nat
  ensures
    A.pts_to a #'p 's **
    pure (Seq.length 's == v n /\
          (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i = 0sz;
  let mut max : nat = 0;
  while ((i < n))
  invariant b. exists* (vi:SZ.t) (vmax:nat).
    A.pts_to a #'p 's **
    R.pts_to i vi **
    R.pts_to max vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax)
       /\ b == (vi < n))
  {
    let v = a.(i);
    i := i + 1sz;
    if (v > max) {
      max := v;
    }
  };
  max
}

#pop-options