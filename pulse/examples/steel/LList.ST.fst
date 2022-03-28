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

module T = FStar.Tactics

let intro_is_list (#opened:_) (#a:Type0)
  (hd:G.erased a)
  (tl:G.erased (list a))
  (node:G.erased (llist_node a))
  (ll:llist a)
  : STGhost unit opened
      (pts_to ll full_perm node
         `star`
       is_list node.next tl)
      (fun _ -> is_list ll (G.reveal hd::tl))
      (requires eq2 #a node.data hd)
      (ensures fun _ -> True)
  = intro_pure (eq2 #a node.data hd);
    intro_exists
      (G.reveal node)
      (fun node -> pts_to ll full_perm node
                  `star`
                pure (eq2 #a node.data hd)
                  `star`
                is_list node.next tl);
    assert (exists_ (fun node -> pts_to ll full_perm node
                                `star`
                              pure (eq2 #a node.data hd)
                                `star`
                              is_list node.next tl) ==
            is_list ll (G.reveal hd::tl))
      by (T.norm [delta_only [`%is_list]; zeta; iota]);

    rewrite 
     (exists_ (fun node -> pts_to ll full_perm node
                          `star`
                        pure (eq2 #a node.data hd)
                          `star`
                        is_list node.next tl))

     (is_list ll (G.reveal hd::tl))

let elim_is_list (#opened:_) (#a:Type0)
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

let elim_is_list_aux (#opened:_) (#a:Type0)
  (l:G.erased (list a))
  (ll:llist a)
  (_:squash (Cons? l))
  : STGhost (G.erased (llist_node a)) opened
      (is_list ll l)
      (fun node ->
       pts_to ll full_perm node
         `star`
       is_list node.next (Cons?.tl l))
      (requires True)
      (ensures fun node -> eq2 #a node.data (Cons?.hd l))
  = rewrite
      (is_list ll l)
      (is_list ll (Cons?.hd l::Cons?.tl l));
    elim_is_list (Cons?.hd l) (Cons?.tl l) ll

let empty a = null

let empty_pts_to #_ a =
  intro_pure (empty a == null);
  rewrite (pure _)
          (is_list (empty a) [])

let empty_pts_to_inversion #_ a l =
  match l with
  | [] -> noop ()
  | hd::tl ->
    rewrite (is_list (empty a) l)
            (is_list (empty a) (hd::tl));
    let node = elim_is_list hd tl (empty a) in
    pts_to_not_null (empty a);
    assert (l == []);
    intro_is_list hd tl node (empty a);
    rewrite (is_list (empty a) (hd::tl))
            (is_list (empty a) l)

let cons #_ #l x ll =
  let node = {
    data = x;
    next = ll;
  } in
  let head = alloc node in
  rewrite (ll `is_list` l)
          (node.next `is_list` l);
  intro_is_list (G.hide x) l (G.hide node) head;
  return head

let peek #_ #l ll p =
  let w = elim_is_list_aux l ll p in
  let node = read ll in
  intro_is_list (Cons?.hd l) (Cons?.tl l) w ll;
  rewrite (ll `is_list` (Cons?.hd l::Cons?.tl l))
          (ll `is_list` l);
  return node.data

let intro #_ #_ l node ll _ =
  intro_is_list (Cons?.hd l) (Cons?.tl l) node ll;
  rewrite (is_list ll (Cons?.hd l::Cons?.tl l))
          (is_list ll l)

let elim #opened #a l ll p =
  let n = elim_is_list_aux l ll p in
  G.reveal n
