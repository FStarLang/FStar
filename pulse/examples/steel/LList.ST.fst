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

noeq
type llist_node (a:Type0) : Type0 = {
  data : a;
  next : ref (llist_node a);
}

type llist a = ref (llist_node a)

let rec lpts_to #a ll l : Tot vprop (decreases l) =
  match l with
  | [] -> pure (ll == null)
  | hd::tl ->
    exists_ (fun (node:llist_node a) ->
             pts_to ll full_perm node
               `star`
             pure (node.data == hd)
               `star`
             lpts_to node.next tl)

module T = FStar.Tactics

let intro_lpts_to (#opened:_) (#a:Type0)
  (hd:G.erased a)
  (tl:G.erased (list a))
  (node:G.erased (llist_node a))
  (ll:llist a)
  : STGhost unit opened
      (pts_to ll full_perm node
         `star`
       lpts_to node.next tl)
      (fun _ -> lpts_to ll (G.reveal hd::tl))
      (requires eq2 #a node.data hd)
      (ensures fun _ -> True)
  = intro_pure (eq2 #a node.data hd);
    intro_exists
      (G.reveal node)
      (fun node -> pts_to ll full_perm node
                  `star`
                pure (eq2 #a node.data hd)
                  `star`
                lpts_to node.next tl);
    assert (exists_ (fun node -> pts_to ll full_perm node
                                `star`
                              pure (eq2 #a node.data hd)
                                `star`
                              lpts_to node.next tl) ==
            lpts_to ll (G.reveal hd::tl))
      by (T.norm [delta_only [`%lpts_to]; zeta; iota]);

    rewrite 
     (exists_ (fun node -> pts_to ll full_perm node
                          `star`
                        pure (eq2 #a node.data hd)
                          `star`
                        lpts_to node.next tl))

     (lpts_to ll (G.reveal hd::tl))

let elim_lpts_to (#opened:_) (#a:Type0)
  (hd:G.erased a)
  (tl:G.erased (list a))
  (ll:llist a)
  : STGhost (G.erased (llist_node a)) opened
      (lpts_to ll (G.reveal hd::tl))
      (fun node ->
       pts_to ll full_perm node
         `star`
       lpts_to node.next tl)
      (requires True)
      (ensures fun node -> eq2 #a node.data hd)
  = assert (lpts_to ll (G.reveal hd::tl) ==
            exists_ (fun node -> pts_to ll full_perm node
                                `star`
                              pure (eq2 #a node.data hd)
                                `star`
                              lpts_to node.next tl))
      by (T.norm [delta_only [`%lpts_to]; zeta; iota]);

    rewrite (lpts_to ll (G.reveal hd::tl))
            (exists_ (fun node -> pts_to ll full_perm node
                                 `star`
                               pure (eq2 #a node.data hd)
                                 `star`
                               lpts_to node.next tl));
    let node = elim_exists () in
    elim_pure (eq2 _ _);
    node

let elim_lpts_to_aux (#opened:_) (#a:Type0)
  (l:G.erased (list a))
  (ll:llist a)
  (_:squash (Cons? l))
  : STGhost (G.erased (llist_node a)) opened
      (lpts_to ll l)
      (fun node ->
       pts_to ll full_perm node
         `star`
       lpts_to node.next (Cons?.tl l))
      (requires True)
      (ensures fun node -> eq2 #a node.data (Cons?.hd l))
  = rewrite
      (lpts_to ll l)
      (lpts_to ll (Cons?.hd l::Cons?.tl l));
    elim_lpts_to (Cons?.hd l) (Cons?.tl l) ll

let empty a = null

let empty_pts_to #_ a =
  intro_pure (empty a == null);
  rewrite (pure _)
          (lpts_to (empty a) [])

let empty_pts_to_inversion #_ a l =
  match l with
  | [] -> noop ()
  | hd::tl ->
    rewrite (lpts_to (empty a) l)
            (lpts_to (empty a) (hd::tl));
    let node = elim_lpts_to hd tl (empty a) in
    pts_to_not_null (empty a);
    assert (l == []);
    intro_lpts_to hd tl node (empty a);
    rewrite (lpts_to (empty a) (hd::tl))
            (lpts_to (empty a) l)

let cons #_ #l x ll =
  let node = {
    data = x;
    next = ll;
  } in
  let head = alloc node in
  rewrite (ll `lpts_to` l)
          (node.next `lpts_to` l);
  intro_lpts_to (G.hide x) l (G.hide node) head;
  return head

let peek #_ #l ll p =
  let w = elim_lpts_to_aux l ll p in
  let node = read ll in
  intro_lpts_to (Cons?.hd l) (Cons?.tl l) w ll;
  rewrite (ll `lpts_to` (Cons?.hd l::Cons?.tl l))
          (ll `lpts_to` l);
  return node.data

let destruct #_ #l ll p =
  let w = elim_lpts_to_aux l ll p in
  let node = read ll in
  rewrite (lpts_to w.next (Cons?.tl l))
          (lpts_to node.next (Cons?.tl l));
  free ll;
  return (node.data, node.next)
