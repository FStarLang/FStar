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

module P = LowStar.Permissions
module A = LowStar.Array
module HST = FStar.HyperStack.ST

include Steel.Pointer.Views

open Steel.RST

(**** Unscoped allocation and deallocation of pointer resources *)

let ptr_alloc #a init =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  A.alloc init 1ul

let ptr_free #a ptr =
  reveal_ptr();
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  A.free ptr

(**** Reading and writing using a pointer resource *)


let ptr_read #a ptr =
  reveal_ptr();
  A.index ptr 0ul

let ptr_write #a ptr x =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  A.upd ptr 0ul x;
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr h1


let ptr_share #a ptr =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  let ptr1 = A.share ptr in
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr h1;
  ptr1

let ptr_merge #a ptr1 ptr2 =
  (**) reveal_ptr();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  A.gather ptr1 ptr2;
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr1 h1
