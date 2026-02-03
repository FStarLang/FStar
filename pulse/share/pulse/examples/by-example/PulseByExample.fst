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

(* 
  Things to note:
  - syntax extension notation
  - 1 or more arguments
  - precondition and postcondition
*)

//SNIPPET_START: five
#lang-pulse
open Pulse.Lib.Pervasives
let fstar_five : int = 5

fn five ()
  returns n:int
  ensures pure (n == 5)
{ 
  fstar_five
}


let pulse_five_in_fstar = five ()
//SNIPPET_END: five


fn five_alt ()
  returns n:(n:int { n == 5 })
{ 
  5
}


open Pulse.Lib.Reference
open Pulse.Class.PtsTo
module R = Pulse.Lib.Reference

(* 
  Things to note:
  - separating conjunction
  - tick for erased, implicit values
  - default full permission
  - heap reference, read and write
*)
fn ref_swap (r1 r2:ref int)
  requires
    r1 |-> 'n1 **
    r2 |-> 'n2
  ensures
    r1 |-> 'n2 **
    r2 |-> 'n1

{
  let v1 = !r1;
  r1 := !r2;
  r2 := v1
}

fn ref_non_zero (r1:ref int) (n1:Ghost.erased int)
requires
  r1 |-> n1
returns b:bool
ensures r1 |-> n1
ensures pure (b == (Ghost.reveal n1 <> 0))
{
  (0 <> !r1);
}

fn id (r:ref int)
  requires
    r |-> 'n
  returns r':ref int
  ensures
    r' |-> 'n ** pure (r == r')
{
  r;
}

fn set (r:ref int) (x:int)
requires r |-> 'n
ensures r |-> x
{
  r := x;
}

fn go () () ()
{
  ()
}

fn test (r:ref int)
  requires 
    r |-> 'n
  ensures
    r |-> 2
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
    a |-> 's0 **
    pure (Seq.length 's0 == v n /\ i < n /\ j < n)
  ensures
    exists* s. 
    a |-> s **
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
    a |-> Frac 'p 's **
    pure (Seq.length 's == v n)
  returns r:nat
  ensures
    a |-> Frac 'p 's **
    pure (Seq.length 's == v n /\
          (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i : SZ.t = 0sz;
  let mut max : nat = 0;
  while (!i < n)
  invariant exists* (vi:SZ.t) (vmax:nat).
    a |-> Frac 'p 's **
    i |-> vi **
    max |-> vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax))
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

fn max_alt (n:SZ.t) (a:larray nat (v n))
  requires
    a |-> Frac 'p 's **
    pure (Seq.length 's == v n)
  returns r:nat
  ensures
    a |-> Frac 'p 's **
    pure (Seq.length 's == v n /\
          (forall (i:nat). i < v n ==> Seq.index 's i <= r))
{
  let mut i = 0sz;
  let mut max : nat = 0;
  while (!i < n)
  invariant exists* (vi:SZ.t) (vmax:nat).
    a |-> Frac 'p 's **
    i |-> vi **
    max |-> vmax **
    pure (vi <= n
       /\ (forall (j:nat). j < v vi ==> Seq.index 's j <= vmax))
  {
    let v = a.(!i);
    i := !i + 1sz;
    if (v > !max) {
      max := v;
    }
  };
  !max
}
