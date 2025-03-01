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
#lang-pulse
open Pulse.Lib.Pervasives

module T = Pulse.Lib.Spec.AVLTree
module G = FStar.Ghost

val tree_t  (a:Type u#0): Type u#0

val is_tree #t ([@@@mkey] ct:tree_t t) (ft:T.tree t)
: Tot slprop (decreases ft)

fn height (#t:Type0) (x:tree_t t) (#ft:G.erased (T.tree t))
  requires is_tree x ft
  returns  n : nat
  ensures  is_tree x ft ** pure (n == T.height ft)

fn is_empty (#t:Type) (x:tree_t t) (#ft:G.erased(T.tree t))
  requires is_tree x ft
  returns  b : bool
  ensures  is_tree x ft ** pure (b <==> (T.is_empty ft))

fn create (t:Type0)
  returns  x : tree_t t
  ensures  is_tree x T.Leaf

fn mem (#t:eqtype) (x:tree_t t) (v: t) (#ft:G.erased (T.tree t))
  requires is_tree x ft
  returns  b : bool
  ensures  is_tree x ft ** pure (b <==> (T.mem ft v))

fn insert_avl
  (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
  (#l: G.erased(T.tree t))
  requires is_tree tree l
  returns  y : tree_t t
  ensures  is_tree y (T.insert_avl cmp l key)

fn delete_avl
  (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
  (#l: G.erased(T.tree t))
  requires is_tree tree l
  returns  y : tree_t t
  ensures  is_tree y (T.delete_avl cmp l key)
