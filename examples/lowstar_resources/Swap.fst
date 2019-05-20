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

open LowStar.Resource
open LowStar.RST
open LowStar.RST.Pointer

(* Swapping values of pointers using the generic frame operation *)

let swap (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (ptr_resource ptr1 <*> ptr_resource ptr2)
             (fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> 
                sel (ptr_view ptr1) h0 == sel (ptr_view ptr2) h1 /\
                sel (ptr_view ptr2) h0 == sel (ptr_view ptr1) h1) = 
  let x = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                    #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                    (ptr_resource ptr2) 
                    (fun _ -> ptr_read ptr1) in 
  let y = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                    #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                    (ptr_resource ptr1) 
                    (fun _ -> ptr_read ptr2) in 
  rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
            #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
            (ptr_resource ptr2) 
            (fun _ -> ptr_write ptr1 y);
  rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
            #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
            (ptr_resource ptr1) 
            (fun _ -> ptr_write ptr2 x)

(* Doing a large even number of swaps *)

val n_swap (#a:Type) (ptr1 ptr2:B.pointer a)
  : RST unit (ptr_resource ptr1 <*> ptr_resource ptr2)
             (fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
             (fun _ -> True)
             (fun h0 x h1 -> 
                sel (ptr_view ptr1) h0 == sel (ptr_view ptr1) h1 /\
                sel (ptr_view ptr2) h0 == sel (ptr_view ptr2) h1) 

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -LowStar.Monotonic -FStar.Monotonic.HyperHeap -FStar.Monotonic.HyperStack -FStar.Reflection -FStar.Tactics -FStar.ModifiesGen -FStar.HyperStack -FStar.Monotonic.Heap -LowStar.Buffer -FStar.Calc -LowStar.RST.reveal_star_inv' --z3cliopt smt.qi.eager_threshold=100"
let n_swap #a ptr1 ptr2 =
                             
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  // 20

  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  // 40

  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  // 60

  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  // 80

  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;  
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2;
  swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2; swap ptr1 ptr2   // 100
#reset-options

(* Allocating two pointers, swapping them, and freeing the memory *)

let alloc_swap_free (#a:Type) (x:a) (y:a)
  : RST (a & a) (empty_resource)
                (fun _ -> empty_resource)
                (fun _ -> True)
                (fun _ (x',y') _ -> x' == y /\ y' == x) = 
  reveal_star ();
  // allocating two pointers
  let ptr1 = rst_frame 
               #empty_resource #_ #_ #(fun ptr1 -> ptr_resource ptr1)
               empty_resource 
               (fun _ -> ptr_alloc x) in
  let ptr2 = rst_frame 
               #(ptr_resource ptr1) #_ #_ #(fun ptr2 -> ptr_resource ptr1 <*> ptr_resource ptr2)
               (ptr_resource ptr1) 
               (fun _ -> ptr_alloc y) in
  // running the swap function
  swap ptr1 ptr2;
  // reading the values of the pointers after swapping them
  let x' = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                     #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                     (ptr_resource ptr2) 
                     (fun _ -> ptr_read ptr1) in 
  let y' = rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_
                     #(fun _ -> ptr_resource ptr1 <*> ptr_resource ptr2)
                     (ptr_resource ptr1) 
                     (fun _ -> ptr_read ptr2) in 
  // freeing the memory
  rst_frame #(ptr_resource ptr1 <*> ptr_resource ptr2) #_ #_ 
            #(fun _ -> ptr_resource ptr1)
            (ptr_resource ptr1) 
            (fun _ -> ptr_free ptr2);
  rst_frame #(ptr_resource ptr1) #_ #_ 
            #(fun _ -> empty_resource)
            (empty_resource) 
            (fun _ -> ptr_free ptr1);
  // returning the swapped values of pointers
  (x',y')
