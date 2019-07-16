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
module LowStar.RST.Pointer

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions

open LowStar.Resource
open LowStar.RST

include LowStar.RST.Pointer.Views

(* Reading and writing using a pointer resource *)

let ptr_read (#a:Type)
             (ptr:A.array a)
           : RST a (ptr_resource ptr)
                   (fun _ -> ptr_resource ptr)
                   (fun _ -> True)
                   (fun h0 x h1 ->
                      (sel (ptr_view ptr) h0).x == x /\
                      sel (ptr_view ptr) h0 == sel (ptr_view ptr) h1) =
  reveal_ptr();
  A.index ptr 0ul

let ptr_write (#a:Type)
              (ptr:A.array a)
              (x:a)
            : RST unit (ptr_resource ptr)
                       (fun _ -> ptr_resource ptr)
                       (fun h -> P.allows_write (sel (ptr_view ptr) h).p)
                       (fun h0 _ h1 ->
                          (sel (ptr_view ptr) h0).p == (sel (ptr_view ptr) h1).p /\
                          (sel (ptr_view ptr) h1).x == x) =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  A.upd ptr 0ul x;
  admit()


(* Unscoped allocation and deallocation of pointer resources *)

let ptr_alloc (#a:Type)
              (init:a)
            : RST (A.array a) (empty_resource)
                                (fun ptr -> ptr_resource ptr)
                                (fun _ -> True)
                                (fun _ ptr h1 ->
                                   A.freeable ptr /\
                                   sel (ptr_view ptr) h1 == {x = init; p = FStar.Real.one}) =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  A.alloc init 1ul

let ptr_free (#a:Type)
             (ptr:A.array a)
           : RST unit (ptr_resource ptr)
                      (fun ptr -> empty_resource)
                      (fun h -> A.freeable ptr /\ P.allows_write (sel (ptr_view ptr) h).p)
                      (fun _ ptr h1 -> True) =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  A.free ptr

let ptr_share
  (#a: Type)
  (ptr: A.array a)
  : RST (A.array a)
    (ptr_resource ptr)
    (fun ptr1 -> ptr_resource ptr <*> ptr_resource ptr1)
    (fun h0 -> True)
    (fun h0 ptr1 h1 ->
      (sel (ptr_view ptr) h0).x == (sel (ptr_view ptr) h1).x /\
      (sel (ptr_view ptr) h1).x == (sel (ptr_view ptr1) h1).x /\
      (sel (ptr_view ptr) h1).p == P.half_permission (sel (ptr_view ptr) h0).p /\
      (sel (ptr_view ptr1) h1).p == P.half_permission (sel (ptr_view ptr) h0).p /\
      A.mergeable ptr ptr1 /\
      P.summable_permissions (sel (ptr_view ptr) h1).p (sel (ptr_view ptr1) h1).p)
  =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  let ptr1 = A.share ptr in
  admit();
  ptr1

let ptr_merge
  (#a: Type)
  (ptr1: A.array a)
  (ptr2: A.array a)
  : RST unit
    (ptr_resource ptr1 <*> ptr_resource ptr2)
    (fun _ -> ptr_resource ptr1)
    (fun h0 -> A.mergeable ptr1 ptr2 /\ P.summable_permissions (sel (ptr_view ptr1) h0).p (sel (ptr_view ptr2) h0).p)
    (fun h0 _ h1 ->
      P.summable_permissions (sel (ptr_view ptr1) h0).p (sel (ptr_view ptr2) h0).p /\
      (sel (ptr_view ptr1) h0).x == (sel (ptr_view ptr1) h1).x /\
      (sel (ptr_view ptr1) h1).p == P.sum_permissions (sel (ptr_view ptr1) h0).p (sel (ptr_view ptr2) h0).p)
  =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  admit();
  A.merge ptr1 ptr2


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
                 (f:(ptr:A.array a -> RST b (res <*> (ptr_resource ptr))
                                              (fun _ -> res <*> (ptr_resource ptr))
                                              (fun h -> pre h /\ sel (ptr_view ptr) h == {x = init; p = FStar.Real.one})
                                              (fun h0 x h1 -> post h0 x h1 /\ P.allows_write (sel (ptr_view ptr) h1).p)))
               : RST b res (fun _ -> res) pre post =
  reveal_star ();
  admit();
  let ptr =
    rst_frame
      res
      #empty_resource
      (fun ptr -> res <*> ptr_resource ptr)
      #(fun ptr -> ptr_resource ptr)
      #res
      (fun _ -> ptr_alloc init)
  in
  let x = f ptr in
  rst_frame
    (res <*> ptr_resource ptr)
    #(ptr_resource ptr)
    (fun _ -> res)
    #(fun _ -> empty_resource)
    #res
    (fun _ -> ptr_free ptr);
    admit();
  x
