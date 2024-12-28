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

module PartialApp
#lang-pulse
open Pulse.Lib.Pervasives


fn my_fn (#t:Type0) (x y:t) 
  requires emp
  ensures emp
{
  ()
}


// Line 22 is a partial application that returns _:t -> unit.
// We should warn the user in case this return type was unintentional. 

fn app (#t:Type0) (v:t)
  requires emp
  ensures emp
{
  my_fn v;
  my_fn v v;
  ()
}
