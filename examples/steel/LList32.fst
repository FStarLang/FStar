(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Aseem Rastogi
*)

module LList32

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util
open LList.ST

module G = FStar.Ghost

/// Monomorphization of LList.ST for UInt32

#set-options "--ide_id_info_off"

type u32 = FStar.UInt32.t

inline_for_extraction
let llist_node = llist_node u32

inline_for_extraction
let llist = llist u32

let lpts_to (ll:llist) (l:list u32) = lpts_to ll l

let cons (#l:G.erased (list u32)) (x:u32) (ll:llist)
  : STT llist
        (ll `lpts_to` l)
        (fun ll -> ll `lpts_to` (x::l))
  = cons x ll

let peek (#l:G.erased (list u32)) (ll:llist) (_:squash (Cons? l))
  : ST u32
       (ll `lpts_to` l)
       (fun _ -> ll `lpts_to` l)
       (requires True)
       (ensures fun x -> x == Cons?.hd l)
  = peek ll ()

let destruct (#l:G.erased (list u32)) (ll:llist) (_:squash (Cons? l))
  : ST (u32 & llist)
       (ll `lpts_to` l)
       (fun (_, ll) -> ll `lpts_to` Cons?.tl l)
       (requires True)
       (ensures fun (x, _) -> x == Cons?.hd l)
  = destruct ll ()
