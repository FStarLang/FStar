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
module LowStar.RST.Pointer.TwoIndex

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST.TwoIndex

open LowStar.BufferOps

(* View and resource for (heap-allocated, freeable) pointer resources *)

abstract
let ptr_view (#a:Type) (ptr:B.pointer a) : view a = 
  reveal_view ();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr) in 
  let inv h = B.live h ptr /\ B.freeable ptr in
  let sel h = Seq.index (B.as_seq h ptr) 0 in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let ptr_resource (#a:Type) (ptr:B.pointer a) = 
  as_resource (ptr_view ptr)

let reveal_ptr ()
  : Lemma ((forall a (ptr:B.pointer a) .{:pattern as_loc (fp (ptr_resource ptr))} 
             as_loc (fp (ptr_resource ptr)) == B.loc_addr_of_buffer ptr) /\
           (forall a (ptr:B.pointer a) h .{:pattern inv (ptr_resource ptr) h} 
             inv (ptr_resource ptr) h <==> B.live h ptr /\ B.freeable ptr) /\
           (forall a (ptr:B.pointer a) h .{:pattern sel (ptr_view ptr) h} 
             sel (ptr_view ptr) h == Seq.index (B.as_seq h ptr) 0)) = 
  ()

(* Reading and writing using a pointer resource *)

let ptr_read (#a:Type)
             (ptr:B.pointer a)
           : RST a (ptr_resource ptr)
                   (fun _ -> ptr_resource ptr)
                   (fun _ -> True)
                   (fun h0 x h1 -> 
                      sel (ptr_view ptr) h0 == x /\ 
                      x == sel (ptr_view ptr) h1) =
  reveal_rst_inv ();
  !* ptr

let ptr_write (#a:Type)
              (ptr:B.pointer a)
              (x:a)
            : RST unit (ptr_resource ptr)
                       (fun _ -> ptr_resource ptr)
                       (fun _ -> True)
                       (fun _ _ h1 -> 
                          sel (ptr_view ptr) h1 == x) =
  reveal_rst_inv ();
  reveal_modifies ();
  ptr *= x



(* Unscoped allocation and deallocation of pointer resources *)

let ptr_alloc (#a:Type)
              (init:a)
            : RST (B.pointer a) (empty_resource)
                                (fun ptr -> ptr_resource ptr)
                                (fun _ -> True)
                                (fun _ ptr h1 -> 
                                   sel (ptr_view ptr) h1 == init) =
  reveal_rst_inv ();
  reveal_modifies ();
  B.malloc HS.root init 1ul

let ptr_free (#a:Type)
             (ptr:B.pointer a)
           : RST unit (ptr_resource ptr)
                      (fun ptr -> empty_resource)
                      (fun _ -> True)
                      (fun _ ptr h1 -> True) =
  reveal_rst_inv ();
  reveal_modifies ();
  B.free ptr

(* Scoped allocation of (heap-allocated, freeable) pointer resources *)

unfold
let with_new_ptr_pre (res:resource) =
  pre:r_pre res{forall h0 h1 . 
                  pre h0 /\ 
                  sel (view_of res) h0 == sel (view_of res) h1 
                  ==> 
                  pre h1}

unfold
let with_new_ptr_post (res0:resource) (a:Type) (res1:a -> resource) =
  post:r_post res0 a res1{forall h0 h1 x h2 h3 . 
                            sel (view_of res0) h0 == sel (view_of res0) h1 /\
                            post h1 x h2 /\
                            sel (view_of (res1 x)) h2 == sel (view_of (res1 x)) h3 
                            ==>
                            post h0 x h3}

let with_new_ptr (#res:resource)
                 (#a:Type)
                 (init:a)
                 (#b:Type)
                 (#pre:with_new_ptr_pre res)
                 (#post:with_new_ptr_post res b (fun _ -> res))
                 (f:(ptr:B.pointer a -> RST b (res <*> (ptr_resource ptr))
                                              (fun _ -> res <*> (ptr_resource ptr))
                                              (fun h -> pre h /\ sel (ptr_view ptr) h == init) 
                                              (post))) 
               : RST b res (fun _ -> res) pre post = 
  reveal_star ();
  let ptr = 
    rst_frame 
      #res #_ #_ 
      #(fun ptr -> res <*> ptr_resource ptr)
      res 
      (fun _ -> ptr_alloc init) in
  let x = f ptr in 
  rst_frame
    #(res <*> ptr_resource ptr) #_ #_ 
    #(fun _ -> res)
    res 
    (fun _ -> ptr_free ptr);
  x
