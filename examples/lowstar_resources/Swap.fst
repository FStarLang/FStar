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
module Swap

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.RST
open LowStar.RST.Pointer

open FStar.Tactics

let swap (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (r_ptr ptr1 <*> r_ptr ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 == sel (r_ptr ptr2) h1 /\
                             sel (r_ptr ptr2) h0 == sel (r_ptr ptr1) h1) =
  let x = frame_left #(r_ptr ptr2) (r_ptr_read ptr1) in
  let y = frame_right #(r_ptr ptr1) (r_ptr_read ptr2) in
  frame_left #(r_ptr ptr2) (r_ptr_write ptr1 y);
  frame_right #(r_ptr ptr1) (r_ptr_write ptr2 x)

val n_swap (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (r_ptr ptr1 <*> r_ptr ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 == sel (r_ptr ptr1) h1 /\
                          sel (r_ptr ptr2) h0 == sel (r_ptr ptr2) h1)

// --log_queries
#reset-options "--max_fuel 0 --max_ifuel 0 --use_two_phase_tc false --__temp_fast_implicits --using_facts_from '* -LowStar.Monotonic -FStar.Monotonic.HyperHeap -FStar.Monotonic.HyperStack -FStar.Reflection -FStar.Tactics -FStar.ModifiesGen -FStar.HyperStack -FStar.Monotonic.Heap -LowStar.Buffer -FStar.Calc -LowStar.RST.reveal_star_inv' --query_stats --print_z3_statistics --z3cliopt smt.qi.eager_threshold=100 --log_queries --z3refresh"
let n_swap #a ptr1 ptr2 =                      
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;

  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2



(*
let swap_incl (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (r_ptr ptr1 <*> r_ptr ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 == sel (r_ptr ptr2) h1 /\
                             sel (r_ptr ptr2) h0 == sel (r_ptr ptr1) h1) =
  let x = r_include (star_includes_left (r_ptr ptr1) (r_ptr ptr2))
                    (fun _ -> r_ptr_read ()) in
  let y = r_include (star_includes_right (r_ptr ptr1) (r_ptr ptr2))
                    (fun _ -> r_ptr_read ()) in
  r_include (star_includes_left (r_ptr ptr1) (r_ptr ptr2))
            (fun _ -> r_ptr_write y);
  r_include (star_includes_right (r_ptr ptr1) (r_ptr ptr2))
            (fun _ -> r_ptr_write x)

let n_swap_incl (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (r_ptr ptr1 <*> r_ptr ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 == sel (r_ptr ptr1) h1 /\
                             sel (r_ptr ptr2) h0 == sel (r_ptr ptr2) h1) = 
                             
  swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2;
  swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2;
  swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2;
  swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2;
  swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2; swap_incl ptr1 ptr2
*)
