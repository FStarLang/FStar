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

(* Moving a point up-down-left-right *)

let move_test (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> as_resource (point_view p))
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

(* Allocating two pointers, packing them up as a point, and calling move *)

let alloc_move_test ()
  : RST unit empty_resource
             (fun _ -> empty_resource)
             (fun _ -> True)
             (fun _ _ _ -> True) = 
  // allocate two pointers (with values 4 and 2)
  let ptr1 = rst_frame 
               #empty_resource #_ #_ #(fun ptr1 -> ptr_resource ptr1)
               empty_resource 
               (fun _ -> ptr_alloc 4) in
  let ptr2 = rst_frame 
               #(ptr_resource ptr1) #_ #_ #(fun ptr2 -> ptr_resource ptr1 <*> ptr_resource ptr2)
               (ptr_resource ptr1) 
               (fun _ -> ptr_alloc 2) in
  // pack the pointers up as a point
  let p = pack ptr1 ptr2 in 
  // call the test function on the point
  move_test p;
  // unpack the point as two pointers
  let (ptr1,ptr2) = unpack p in 
  // read the values of the two pointers
  let x = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                    #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                    (ptr_resource ptr2) 
                    (fun _ -> ptr_read ptr1) in 
  let y = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                    #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                    (ptr_resource ptr1) 
                    (fun _ -> ptr_read ptr2) in 
  // check that the values of the unpacked pointers are also 4 and 2
  assert (x = 4 /\ y = 2);
  // deallocate the two pointers
  rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_ 
            #(fun _ -> ptr_resource ptr1)
            (ptr_resource ptr1) 
            (fun _ -> ptr_free ptr2);
  rst_frame #(ptr_resource ptr1) #_ #_ 
            #(fun _ -> empty_resource)
            (empty_resource) 
            (fun _ -> ptr_free ptr1)

(* Testing a loop over move *)

open LowStar.RST.Loops

val while_move_test (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> sel_x p h1 == 3)

let while_move_test p =
  while (as_resource (point_view p))
        (fun _ -> True)
        (fun p -> p.x_view <> 3)
        (fun () -> let x = get_x p in x <> 3)
        (fun () -> let x = get_x p in
          if x < 3 then move_right p
          else if x >= 3 then move_left p)
