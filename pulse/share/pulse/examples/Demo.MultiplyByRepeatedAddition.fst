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

module Demo.MultiplyByRepeatedAddition
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.UInt32

module U32 = FStar.UInt32
open FStar.Mul
let rec multiply (x y:nat) : z:nat { z == x * y} =
    if x = 0 then 0
    else multiply (x - 1) y + y


fn mult (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr : nat = 0;
    let mut acc : nat = 0;
    while ((!ctr < x))
    invariant
    exists* (c a:nat).
        pts_to ctr c **
        pts_to acc a **
        pure (a == (c * y) /\
              c <= x)
    {
        acc := !acc + y;
        ctr := !ctr + 1;
    };
    !acc
}


open Pulse.Lib.BoundedIntegers
fn mult32 (x y:U32.t)
    requires pure (fits #U32.t (v x * v y))
    returns z:U32.t
    ensures pure (v z == v x * v y)
{  
    let mut ctr = 0ul;
    let mut acc = 0ul;
    while ((!ctr < x))
    invariant
    exists* c (a : UInt32.t). // FIXME: this type should have been instantiate by fundeps?
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              v a == (v c * v y))
    {
        acc := !acc + y;
        ctr := !ctr + 1ul;
    };
    !acc
}

open FStar.UInt32
let i (x:U32.t) : GTot int = U32.v x 

fn mult32' (x y:U32.t)
    requires pure (i x * i y <= 0xffffffff)
    returns z:U32.t
    ensures pure (i z == i x * i y)
{  
    let mut ctr = 0ul;
    let mut acc = 0ul;
    while ((!ctr <^ x))
    invariant
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <=^ x /\
              i a == (i c * i y))
    {
        acc := !acc +^ y;
        ctr := !ctr +^ 1ul;
    };
    !acc
}