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
module A = Steel.Array
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module Fext = FStar.FunctionalExtensionality

include Steel.Pointer.Views

open Steel.RST

#set-options "--max_fuel 0 --max_ifuel 0"

(**** Unscoped allocation and deallocation of pointer resources *)

val array_to_pointer (#a: Type) (p: pointer a) : RST unit
  (A.array_resource p)
  (fun _ -> ptr_resource p)
  (fun _ -> True)
  (fun h0 _ h1 ->
   get_val p h1 == Seq.index (A.as_rseq p h0) 0 /\
   get_perm p h1 == A.get_rperm p h0
  )

let array_to_pointer #a p =
  cast_to_refined_view (A.array_resource p)  (fun (av: A.varray #a p) ->
    { ptr_x = Seq.index av.A.s 0; ptr_p = av.A.p }
  )

assume val pointer_to_array (#a: Type) (p: pointer a) : RST unit
  (ptr_resource p)
  (fun _ -> A.array_resource p)
  (fun _ -> True)
  (fun h0 _ h1 ->
   get_val p h0 == Seq.index (A.as_rseq p h1) 0 /\
   get_perm p h0 == A.get_rperm p h1
  )

let vptr_to_varray (#a: Type) (p: pointer a) : vptr a -> GTot (A.varray p) = fun av ->
   { A.s = Seq.init_ghost 1 (fun _ -> av.ptr_x); A.p = av.ptr_p }

let bijective_resource_refinement (#a: Type) (p: pointer a)
  : Lemma (A.array_resource p == refine_view (ptr_resource p) (vptr_to_varray p))
  [SMTPat (refine_view (ptr_resource p) (vptr_to_varray p))]
=
  let old_res = A.array_resource p in
  let new_res = refine_view (ptr_resource p) (vptr_to_varray p) in
  assert(old_res.t == new_res.t);
  assert(old_res.view.fp == new_res.view.fp);
  assert(old_res.view.inv == new_res.view.inv);
  // That will require functional extensionality
  Fext.extensionality_g HS.mem (fun _ -> A.varray p)
    old_res.view.sel new_res.view.sel;
  assert(Fext.on_domain_g HS.mem old_res.view.sel == old_res.view.sel);
  assert(Fext.on_domain_g HS.mem new_res.view.sel == new_res.view.sel);
  let aux (h: HS.mem) : Lemma (old_res.view.sel h == new_res.view.sel h) =
    let old_view : A.varray p = { A.s = A.as_seq h p; A.p = A.get_perm h p 0 } in
    A.reveal_array ();
    assert(sel_of old_res.view h == old_view);
    let ptr_view : vptr a = { ptr_x = Seq.index (A.as_seq h p) 0; ptr_p = A.get_perm h p 0} in
    assert(sel_of (ptr_resource p).view h == ptr_view);
    let new_view : A.varray p = {
      A.s = Seq.init_ghost 1 (fun _ -> Seq.index (A.as_seq h p) 0);
      A.p = A.get_perm h p 0
    } in
    assume(Seq.init_ghost 1 (fun _ -> Seq.index (A.as_seq h p) 0) == A.as_seq h p);
    assert(sel_of new_res.view h == vptr_to_varray p ptr_view);
    assert((vptr_to_varray p ptr_view).A.p == new_view.A.p);
    assume((vptr_to_varray p ptr_view).A.s == Seq.init_ghost 1 (fun _ -> ptr_view.ptr_x));
    assume((vptr_to_varray p ptr_view).A.s == new_view.A.s);
    assert(vptr_to_varray p ptr_view == new_view)
  in
  Classical.forall_intro aux;
  assume(Fext.on_domain_g HS.mem old_res.view.sel == Fext.on_domain_g HS.mem new_res.view.sel);
  assert(old_res.view.sel == new_res.view.sel)

let ptr_alloc #a init =
  let ptr = A.alloc init 1ul in
  array_to_pointer ptr;
  return ptr

let ptr_free #a ptr =
  pointer_to_array ptr;
  A.free ptr

(**** Reading and writing using a pointer resource *)

let ptr_read #a ptr =
  pointer_to_array ptr;
  let x = A.index ptr 0ul in
  array_to_pointer ptr;
  return x

let ptr_write #a ptr x =
  pointer_to_array ptr;
  A.upd ptr 0ul x;
  array_to_pointer ptr

(*
let ptr_share #a ptr =
  pointer_to_array ptr;
  let ptr1 = A.share ptr in
  rst_frame
    (A.array_resource ptr <*> A.array_resource ptr1)
    (fun _ -> ptr_resource ptr <*> A.array_resource ptr1)
    (fun _ -> array_to_pointer ptr);
  rst_frame
    ( ptr_resource ptr <*> A.array_resource ptr1)
    (fun _ -> ptr_resource ptr <*> ptr_resource ptr1)
    (fun _ -> array_to_pointer ptr1);
  ptr1

let ptr_merge #a ptr1 ptr2 =
  (**) A.reveal_array();
  (**) reveal_rst_inv ();
  (**) reveal_modifies ();
  (**) reveal_star ();
  A.gather ptr1 ptr2;
  (**) let h1 = HST.get () in
  (**) A.live_array_used_in ptr1 h1
*)
