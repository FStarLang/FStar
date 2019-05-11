(*
   Copyright 2008-2019 Microsoft Research

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
module Point.Test

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST
open LowStar.RST.Pointer

open Point

let move_test (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel_x p h0 == sel_x p h1 /\
                sel_y p h0 == sel_y p h1) = 
  move_up p;
  move_up p;
  move_left p;
  move_up p;  
  move_down p;
  move_right p;
  move_down p;
  move_up p;  
  move_right p;
  move_down p;
  move_left p;
  move_down p;
  move_right p;
  move_down p;
  move_left p;
  move_up p
