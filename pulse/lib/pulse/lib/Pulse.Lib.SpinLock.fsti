(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at


   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.SpinLock

open Pulse.Lib.Pervasives

module T = FStar.Tactics.V2

val lock : Type0

val lock_alive (l:lock) (#[T.exact (`full_perm)] p:perm)  (v:vprop) : vprop

val lock_acquired (l:lock) : vprop

val new_lock (v:vprop { is_big v })
  : stt lock v (fun l -> lock_alive l v)

val acquire (#v:vprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v) (fun _ -> v ** lock_alive l #p v ** lock_acquired l)

val release (#v:vprop) (#p:perm) (l:lock)
  : stt unit (lock_alive l #p v ** lock_acquired l ** v) (fun _ -> lock_alive l #p v)

val share (#v:vprop) (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #p v)
      (fun _ -> lock_alive l #(half_perm p) v ** lock_alive l #(half_perm p) v)

val gather (#v:vprop) (#p:perm) (l:lock)
  : stt_ghost unit emp_inames
      (lock_alive l #(half_perm p) v ** lock_alive l #(half_perm p) v)
      (fun _ -> lock_alive l #p v)

val free (#v:vprop) (l:lock)
  : stt unit (lock_alive l #full_perm v ** lock_acquired l) (fun _ -> emp)
