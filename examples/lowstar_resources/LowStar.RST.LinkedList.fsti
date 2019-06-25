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
module LowStar.RST.LinkedList

open LowStar.Resource
open LowStar.RST

module L = FStar.List.Tot

val llist (a:Type0) : Type0
val llist_resource (#a:Type0) (x:llist a) : resource
val llist_view (#a:Type0) (x:llist a) : list a

val llist_cons (#a:Type) (x:llist a) (v:a)
  : RST (llist a)
        (llist_resource x)
        (fun x' -> llist_resource x')
        (requires fun _ -> True)
        (ensures fun _ x' _ -> llist_view x' == v :: llist_view x)

val llist_head (#a:Type) (x:llist a)
  : RST a
        (llist_resource x)
        (fun _ -> llist_resource x)
        (requires fun _ -> Cons? (llist_view x))
        (ensures fun _ hd _ -> Cons? (llist_view x) /\ hd == L.hd (llist_view x))

val llist_tail (#a:Type) (x:llist a)
  : RST (llist a)
        (llist_resource x)
        (fun x' -> llist_resource x')
        (requires fun _ -> Cons? (llist_view x))
        (ensures fun _ x' _ -> Cons? (llist_view x) /\ llist_view x' == L.tl (llist_view x))

val llist_map (#a:Type) (f:a -> a) (x:llist a)
  : RST (llist a)
        (llist_resource x)
        (fun x' -> llist_resource x')
        (requires fun _ -> True)
        (ensures fun _ x' _ -> llist_view x' == L.map f (llist_view x))
