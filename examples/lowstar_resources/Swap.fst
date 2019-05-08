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
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 === sel (r_ptr ptr2) h1 /\
                             sel (r_ptr ptr2) h0 === sel (r_ptr ptr1) h1) =
  let x = frame_left #_ #_ #(r_ptr ptr2) (fun _ -> r_ptr_read #_ #ptr1 ()) in
  let y = frame_right #_ #(r_ptr ptr1) (fun _ -> r_ptr_read #_ #ptr2 ()) in
  frame_left #_ #_ #(r_ptr ptr2) (fun _ -> r_ptr_write #_ #ptr1 y);
  frame_right #_ #(r_ptr ptr1) (fun _ -> r_ptr_write #_ #ptr2 x)

let n_swap (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (r_ptr ptr1 <*> r_ptr ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> sel (r_ptr ptr1) h0 == sel (r_ptr ptr1) h1 /\
                             sel (r_ptr ptr2) h0 == sel (r_ptr ptr2) h1) = 
                             
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
