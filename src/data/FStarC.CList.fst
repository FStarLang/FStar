(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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

module FStarC.CList

open FStar.Tactics.Typeclasses
open FStarC.Class.Ord
open FStarC.Class.Listlike

type clist (a:Type0) : Type0 =
  | CNil : clist a
  | CCons : a -> clist a -> clist a
  | CCat  : clist a -> clist a -> clist a

let ccat (#a:Type0) (xs ys : clist a) : clist a =
  match xs, ys with
  | CNil, _ -> ys
  | _, CNil -> xs
  | _ -> CCat xs ys

let rec view (#a:Type0) (l:clist a) : Tot (view_t a (clist a)) =
  match l with
  | CNil -> VNil
  | CCons x xs -> VCons x xs
  | CCat (CCat xs ys) zs -> view (CCat xs (CCat ys zs))
  | CCat xs ys ->
    match view xs with
    | VNil -> view ys
    | VCons x xs' -> VCons x (CCat xs' ys)

instance listlike_clist (a:Type0) : Tot (listlike a (t a)) = {
  empty = CNil;
  cons = CCons;
  view = view;
}

instance monoid_clist (a:Type0) : Tot (monoid (t a)) = {
  mzero = CNil;
  mplus = ccat;
}

instance showable_clist (a:Type0) (_ : showable a) : Tot (showable (t a)) = {
  show = (fun l -> show (to_list l));
}

instance eq_clist (a:Type0) (d : deq a) : Tot (deq (t a)) = {
  (=?) = (fun l1 l2 -> to_list l1 =? to_list l2);
}

instance ord_clist (a:Type0) (d : ord a) : Tot (ord (t a)) = {
  super = solve;
  cmp = (fun l1 l2 -> cmp (to_list l1) (to_list l2));
}

let rec map (#a #b : Type0) (f : a -> b) (l : clist a) : clist b =
  match l with
  | CNil -> CNil
  | CCons x xs -> CCons (f x) (map f xs)
  | CCat xs ys -> ccat (map f xs) (map f ys)

let rec existsb (#a : Type0) (p : a -> bool) (l : clist a) : bool =
  match l with
  | CNil -> false
  | CCons x xs -> p x || existsb p xs
  | CCat xs ys -> existsb p xs || existsb p ys

let rec for_all (#a : Type0) (p : a -> bool) (l : clist a) : bool =
  match l with
  | CNil -> true
  | CCons x xs -> p x && for_all p xs
  | CCat xs ys -> for_all p xs && for_all p ys

let rec partition (#a : Type0) (p : a -> bool) (l : clist a) : clist a * clist a =
  match l with
  | CNil -> (CNil, CNil)
  | CCons x xs ->
    let (ys, zs) = partition p xs in
    if p x then (CCons x ys, zs) else (ys, CCons x zs)
  | CCat xs ys ->
    let (ys, zs) = partition p xs in
    let (us, vs) = partition p ys in
    (ccat ys us, ccat zs vs)

let rec collect (#a #b : Type0) (f : a -> clist b) (l : clist a) : clist b =
  match l with
  | CNil -> CNil
  | CCons x xs -> ccat (f x) (collect f xs)
  | CCat xs ys -> ccat (collect f xs) (collect f ys)
