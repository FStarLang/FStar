(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.LinkedList

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
open FStar.List.Tot
module U32 = FStar.UInt32
open Pulse.Lib.BoundedIntegers

val llist (t:Type0) : Type0

val is_list #t ([@@@mkey]x:llist t) (l:list t)
  : Tot slprop

fn is_empty (#t:Type) (x:llist t)
    requires is_list x 'l
    returns b:bool
    ensures is_list x 'l ** pure (b <==> ('l == []))

fn head (#t:Type0) (x:llist t) (#l:erased (list t){Cons? l})
    requires is_list x l
    returns v:t
    ensures is_list x l ** pure (v == List.Tot.hd l)

fn length (#t:Type0) (x:llist t)
          (#l:erased (list t))
  requires is_list x l
  returns n:nat
  ensures is_list x l ** pure (n == List.Tot.length l)

fn create (t:Type)
  requires emp
  returns x : llist t
  ensures is_list x []

fn cons (#t:Type) (v:t) (x:llist t)
  requires is_list x 'l
  returns  y : llist t
  ensures  is_list y (v::'l)

fn rec append (#t:Type0) (x y:llist t)
  requires is_list x 'l1 ** is_list y 'l2 ** pure (Cons? 'l1)
  ensures is_list x ('l1 @ 'l2)

fn move_next (#t:Type) (x:llist t)
  requires is_list x 'l ** pure (Cons? 'l)
  returns y:llist t
  ensures exists* tl.
      is_list y tl **
      (is_list y tl @==> is_list x 'l) **
      pure (Cons? 'l /\ tl == Cons?.tl 'l)

fn length_iter (#t:Type) (x: llist t)
  requires is_list x 'l
  returns n:nat
  ensures is_list x 'l ** pure (n == List.Tot.length 'l)

fn is_last_cell (#t:Type) (x:llist t)
  requires is_list x 'l ** pure (Cons? 'l)
  returns  b : bool
  ensures  is_list x 'l ** pure (b == (List.Tot.length 'l = 1))

fn append_at_last_cell (#t:Type) (x y:llist t)
  requires
    is_list x 'l1 **
    is_list y 'l2 **
    pure (List.Tot.length 'l1 == 1)
  ensures
    is_list x (List.Tot.append 'l1 'l2)

fn append_iter (#t:Type) (x y:llist t)
  requires is_list x 'l1 ** is_list y 'l2 ** pure (Cons? 'l1)
  ensures is_list x ('l1 @ 'l2)

fn detach_next (#t:Type) (x:llist t)
  requires is_list x 'l ** pure (Cons? 'l)
  returns y:llist t
  ensures exists* hd tl.
    is_list x [hd] **
    is_list y tl **
    pure ('l == hd::tl)

fn split (#t:Type0) (x:llist t) (n:U32.t) (#xl:erased (list t))
 requires is_list x xl ** pure (Cons? xl /\ 0 < v n /\ v n <= List.Tot.length xl)
 returns  y : llist t
 ensures
   exists* l1 l2. 
     is_list x l1 **
     is_list y l2 **
     pure (xl == l1 @ l2 /\
           List.Tot.length l1 == v n)

fn insert (#kk:Type0) (x:llist kk) (item:kk) (pos:U32.t) (#xl:erased (list kk))
  requires is_list x xl ** pure (Cons? xl /\ 0 < v pos /\ v pos < List.Tot.length xl)
  ensures
    exists* l0 l1.
      is_list x (l0 @ item :: l1) **
      pure (
          xl == l0 @ l1 /\
          List.Tot.length l0 == v pos
        )

fn delete (#kk:Type0) (x:llist kk) (item:kk) (pos:U32.t) (#xl:erased (list kk))
  requires is_list x xl ** pure (Cons? xl /\ 0 < v pos /\ v pos < List.Tot.length xl)
  ensures
    exists* l0 l1.
      is_list x (l0 @ item :: l1) **
      pure (
          xl == l0 @ l1 /\
          List.Tot.length l0 == v pos
        )
