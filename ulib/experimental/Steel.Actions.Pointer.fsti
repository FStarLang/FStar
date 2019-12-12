(*
   Copyright 2019 Microsoft Research

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
module Steel.Actions.Pointer
open Steel.Heap
open Steel.HProp
open Steel.Memory
open FStar.Real
open Steel.Permissions
open Steel.Actions
module U32 = FStar.UInt32


val sel (#a:_) (r:ref a) (m:hheap (ptr r))
  : a

/// sel respect pts_to
val sel_lemma (#a:_) (r:ref a) (p:permission) (m:hheap (ptr_perm r p))
  : Lemma (interp (ptr r) m /\
           interp (pts_to r p (sel r m)) m)


/// upd requires a full permission
val upd (#a:_) (r:ref a) (v:a)
  : m_action (ptr_perm r full_permission) unit (fun _ -> pts_to r full_permission v)


val alloc (#a:_) (v:a)
  : m_action emp (ref a) (fun x -> pts_to x full_permission v)
