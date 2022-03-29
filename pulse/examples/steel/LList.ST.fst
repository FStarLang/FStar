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

module LList.ST

open Steel.Memory
open Steel.ST.Effect
open Steel.ST.Util

open Steel.ST.Reference

#set-options "--ide_id_info_off"

let rec is_list #a ll l : Tot vprop (decreases l) =
  match l with
  | [] -> pure (ll == null)
  | hd::tl ->
    exists_ (fun (node:llist_node a) ->
             pts_to ll full_perm node
               `star`
             pure (node.data == hd)
               `star`
             is_list node.next tl)

let empty a = null

module T = FStar.Tactics

let intro #_ #_ l node ll _ =
  intro_pure (node.data == Cons?.hd l);
  intro_exists
    node
    (fun node -> pts_to ll full_perm node
                `star`
              pure (node.data == Cons?.hd l)
                `star`
              is_list node.next (Cons?.tl l));
  assert (exists_ (fun node -> pts_to ll full_perm node
                              `star`
                            pure (node.data == Cons?.hd l)
                              `star`
                            is_list node.next (Cons?.tl l)) ==
          is_list ll (Cons?.hd l::Cons?.tl l))
      by (T.norm [delta_only [`%is_list]; zeta; iota]);

  rewrite 
   (exists_ (fun node -> pts_to ll full_perm node
                        `star`
                      pure (node.data == Cons?.hd l)
                        `star`
                      is_list node.next (Cons?.tl l)))

   (is_list ll l)
   
let elim_aux (#opened:_) (#a:Type0)
  (hd:G.erased a)
  (tl:G.erased (list a))
  (ll:llist a)
  : STGhost (G.erased (llist_node a)) opened
      (is_list ll (G.reveal hd::tl))
      (fun node ->
       pts_to ll full_perm node
         `star`
       is_list node.next tl)
      (requires True)
      (ensures fun node -> eq2 #a node.data hd)
  = assert (is_list ll (G.reveal hd::tl) ==
            exists_ (fun node -> pts_to ll full_perm node
                                `star`
                              pure (eq2 #a node.data hd)
                                `star`
                              is_list node.next tl))
      by (T.norm [delta_only [`%is_list]; zeta; iota]);

    rewrite (is_list ll (G.reveal hd::tl))
            (exists_ (fun node -> pts_to ll full_perm node
                                 `star`
                               pure (eq2 #a node.data hd)
                                 `star`
                               is_list node.next tl));
    let node = elim_exists () in
    elim_pure (eq2 _ _);
    node

let elim #opened #a l ll p =
  rewrite
    (is_list ll l)
    (is_list ll (Cons?.hd l::Cons?.tl l));
  elim_aux (Cons?.hd l) (Cons?.tl l) ll
  
let empty_pts_to #_ a =
  intro_pure (empty a == null);
  rewrite (pure _)
          (is_list (empty a) [])

let cons #_ #l x ll =
  let node = {
    data = x;
    next = ll;
  } in
  let head = alloc node in
  rewrite (ll `is_list` l)
          (node.next `is_list` l);
  intro (x::l) node head ();
  return head

let peek #_ #l ll p =
  let w = elim l ll p in
  let node = read ll in
  intro l w ll p;
  return node.data
