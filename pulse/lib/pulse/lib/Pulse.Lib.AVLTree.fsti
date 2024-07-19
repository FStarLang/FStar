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

   Author: Sheera Shamsu
*)

//Pulse AVL tree interface. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
open Pulse.Lib.Pervasives

module T = Pulse.Lib.Spec.AVLTree
module G = FStar.Ghost

//val node (a:Type u#0) : Type u#0

//val node_ptr (a:Type u#0) : Type u#0

val tree_t  (a:Type u#0): Type u#0

val is_tree #t (ct:tree_t t) (ft:T.tree t)
: Tot slprop (decreases ft)

val height (#t:Type0) (x:tree_t t) (#ft:G.erased (T.tree t))
  : stt nat
(requires is_tree x ft)
(ensures fun n -> is_tree x ft ** pure (n == T.height ft))

val is_empty (#t:Type) (x:tree_t t) (#ft:G.erased(T.tree t))
   : stt bool
  (requires is_tree x ft)
  (ensures fun b -> is_tree x ft ** pure (b <==> (T.is_empty ft)))

val create (t:Type0)
   : stt (tree_t t)
  (requires emp)
  (ensures fun x -> is_tree x T.Leaf)

val mem (#t:eqtype) (x:tree_t t) (v: t) (#ft:G.erased (T.tree t))
     : stt bool
(requires is_tree x ft)
(ensures fun b -> is_tree x ft ** pure (b <==> (T.mem ft v)))

val  insert_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t) (#l: G.erased(T.tree t))
    : stt (tree_t t )
(requires is_tree tree l) 
(ensures fun y -> (is_tree y (T.insert_avl cmp l key)))

val  delete_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t) (#l: G.erased(T.tree t))
    : stt (tree_t t )
(requires is_tree tree l) 
(ensures fun y -> (is_tree y (T.delete_avl cmp l key)))
