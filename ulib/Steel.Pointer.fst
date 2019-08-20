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
module Steel.Pointer

open FStar.HyperStack.ST
module A = LowStar.Array
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module P = LowStar.Permissions

open Steel.Resource
open Steel.RST
open Steel.Pointer.Views

include Steel.Pointer.Views

(**** Unscoped allocation and deallocation of pointer resources *)

let ptr_alloc
  (#a:Type)
  (init:a)
  : RST (pointer a) (empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> True)
    (fun _ ptr h1 ->
      A.freeable ptr /\
      get ptr h1 == init /\
      get_perm ptr h1 = FStar.Real.one
    ) =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  A.alloc init 1ul

let ptr_free
  (#a:Type)
  (ptr:pointer a)
  : RST unit (ptr_resource ptr)
    (fun ptr -> empty_resource)
    (fun h0 -> A.freeable ptr /\ P.allows_write (get_perm ptr h0))
    (fun _ _ _ -> True) =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  A.free ptr

(**** Reading and writing using a pointer resource *)


let ptr_read
  (#a:Type)
  (ptr:pointer a)
  : RST a (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> True)
    (fun h0 x h1 ->
      get ptr h0 == x /\
      h0 == h1
    ) =
  reveal_ptr();
  A.index ptr 0ul

let ptr_write
  (#a:Type)
  (ptr:pointer a)
  (x:a)
  : RST unit (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun h0 -> P.allows_write (get_perm ptr h0))
    (fun h0 _ h1 ->
      get_perm ptr h0 == get_perm ptr h1 /\
      get ptr h1 == x
    ) =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  A.upd ptr 0ul x;
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr h1


let ptr_share
  (#a: Type)
  (ptr: pointer a)
  : RST (pointer a)
    (ptr_resource ptr)
    (fun ptr1 -> ptr_resource ptr <*> ptr_resource ptr1)
    (fun _ -> True)
    (fun h0 ptr1 h1 ->
      get ptr h1 == get ptr h0  /\
      get ptr1 h1 == get ptr h0  /\
      get_perm ptr h1 == P.half_permission (get_perm ptr h0) /\
      get_perm ptr1 h1 == P.half_permission (get_perm ptr h0) /\
      A.gatherable ptr ptr1 /\
      P.summable_permissions (get_perm ptr h1) (get_perm ptr1 h1))
  =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  let ptr1 = A.share ptr in
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr h1;
  ptr1

let ptr_merge
  (#a: Type)
  (ptr1: pointer a)
  (ptr2: pointer a)
  : RST unit
    (ptr_resource ptr1 <*> ptr_resource ptr2)
    (fun _ -> ptr_resource ptr1)
    (fun h0 -> A.gatherable ptr1 ptr2 /\
      P.summable_permissions (get_perm ptr1 h0) (get_perm ptr2 h0)
    )
    (fun h0 _ h1 ->
      P.summable_permissions (get_perm ptr1 h0) (get_perm ptr2 h0) /\
      get ptr1 h1 == get ptr1 h0 /\
      get_perm ptr1 h1 == P.sum_permissions (get_perm ptr1 h0) (get_perm ptr2 h0)
     )
  =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  A.gather ptr1 ptr2;
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr1 h1
