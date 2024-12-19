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

module ExistsErasedAndPureEqualities
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

assume
val some_pred (x:R.ref int) (v:int) : slprop

//Intro exists* with an erased variable fails
[@@expect_failure]

fn test1 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures some_pred x v
{
    introduce exists* (v_:erased int). (
        pure (v == v_)
    ) with _;
  
    ()
}


//Intro exists* with an erased variable in an equality bound on the left,
//fails weirdly with an SMT failure, where it tries to prove earsed int == int
//and hide v == v
//Intro exists* with an erased variable fails
[@@expect_failure]

fn test2 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures some_pred x v
{
    introduce exists* (v_:erased int). (
        pure (v == v_)
    ) with _;
  
    ()
}


//If you don't use an erased variable, this works fine if the variable is on the left

fn test3 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures emp
{
    introduce exists* (v_:int). (
        pure (v_ == v)
    ) with _;
  
    admit()
}


//but fails if the variable is on the right
[@@expect_failure]

fn test4 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures emp
{
    introduce exists* (v_:int). (
        pure (v == v_)
    ) with _;
  
    admit()
}
