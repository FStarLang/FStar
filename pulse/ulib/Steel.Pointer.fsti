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

include Steel.Pointer.Views

open Steel.RST


#set-options "--max_fuel 0 --max_ifuel 0"

(**** Unscoped allocation and deallocation of pointer resources *)

val ptr_alloc
  (#a:Type)
  (init:a)
  : RST (pointer a)
    (empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> True)
    (fun _ ptr h1 ->
      A.freeable ptr /\
      get_val ptr h1 == init /\
      get_perm ptr h1 == P.full_permission
    )

val ptr_free
  (#a:Type)
  (ptr:pointer a)
  : RST unit
    (ptr_resource ptr)
    (fun ptr -> empty_resource)
    (fun h0 -> A.freeable ptr /\ P.allows_write (get_perm ptr h0))
    (fun _ _ _ -> True)

(**** Reading and writing using a pointer resource *)

val ptr_read
  (#a:Type)
  (ptr:pointer a)
  : RST a
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> True)
    (fun h0 x h1 ->
      get_val ptr h0 == x /\ get_val ptr h1 == x /\
      get_perm ptr h0 == get_perm ptr h1
    )

val ptr_write
  (#a:Type)
  (ptr:pointer a)
  (x:a)
  : RST unit
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun h0 -> P.allows_write (get_perm ptr h0))
    (fun h0 _ h1 ->
      get_perm ptr h0 == get_perm ptr h1 /\
      get_val ptr h1 == x
    )

(*
val ptr_share
  (#a: Type)
  (ptr: pointer a)
  : RST (pointer a)
    (ptr_resource ptr)
    (fun ptr1 -> ptr_resource ptr <*> ptr_resource ptr1)
    (fun _ -> True)
    (fun h0 ptr1 h1 ->
      get_val ptr h1 == get_val ptr h0  /\
      get_val ptr1 h1 == get_val ptr h0  /\
      get_perm ptr h1 == P.half_permission (get_perm ptr h0) /\
      get_perm ptr1 h1 == P.half_permission (get_perm ptr h0) /\
      A.gatherable ptr ptr1 /\
      P.summable_permissions (get_perm ptr h1) (get_perm ptr1 h1))

val ptr_merge
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
      get_val ptr1 h1 == get_val ptr1 h0 /\
      get_perm ptr1 h1 == P.sum_permissions (get_perm ptr1 h0) (get_perm ptr2 h0)
     )
*)
