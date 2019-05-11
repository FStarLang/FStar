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
module EqPoint.Test

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST
open LowStar.RST.Pointer

open EqPoint

let move_test (p:point)
  : RST unit (as_resource (eq_point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel_x p h0 == sel_x p h1 /\
                sel_y p h0 == sel_y p h1) = 
  move_up p;
  move_up p;
  move_up p;  
  move_down p;
  move_down p;
  move_up p;  
  move_down p;
  move_down p;
  move_down p;
  move_up p

(*
// WIP
let move_test_alloc_aux (x:B.pointer int) 
  : RST unit (ptr_resource x) (fun _ -> True) (fun _ _ _ -> True) =
      with_new_ptr #(ptr_resource x) 0 #_ #(fun _ -> True) #(fun _ _ _ -> True) 
      (fun y -> 
        reveal_ptr ();
        reveal_star ();
        assert (r_disjoint (ptr_resource x) (ptr_resource y));
        let p = mk_point x y in
        ()
      )

let move_test_alloc ()
  : RST unit empty_resource (fun _ -> True) (fun _ _ _ -> True) =
  with_new_ptr #empty_resource 0 #_ #(fun _ -> True) #(fun _ _ _ -> True) 
  (fun x -> 
    frame (star_includes_right empty_resource) 
    (fun _ -> 
      move_test_alloc_aux x
    )
  )
*)
