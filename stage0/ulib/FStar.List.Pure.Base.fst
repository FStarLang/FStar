(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.List.Pure.Base

open FStar.List.Tot.Base

(** Functions on list with a pure specification *)

(** [map2] takes a pair of list of the same length [x1; ...; xn] [y1; ... ; yn]
 and return the list [f x1 y1; ... ; f xn yn] *)
val map2 (#a1 #a2 #b: Type)
  (f: a1 -> a2 -> b)
  (l1:list a1)
  (l2:list a2)
  : Pure (list b)
    (requires (length l1 == length l2))
    (ensures (fun _ -> True))
    (decreases l1)
let rec map2 #a1 #a2 #b f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x1::xs1, x2::xs2 -> f x1 x2 :: map2 f xs1 xs2

(** [map3] takes three lists of the same length [x1; ...; xn]
    [y1; ... ; yn] [z1; ... ; zn] and return the list
    [f x1 y1 z1; ... ; f xn yn zn] *)
val map3 (#a1 #a2 #a3 #b: Type)
  (f: a1 -> a2 -> a3 -> b)
  (l1:list a1)
  (l2:list a2)
  (l3:list a3)
  : Pure (list b)
    (requires (let n = length l1 in
      (n == length l2 /\
        n == length l3)))
    (ensures (fun _ -> True))
    (decreases l1)
let rec map3 #a1 #a2 #a3 #b f l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x1::xs1, x2::xs2, x3::xs3 -> f x1 x2 x3 :: map3 f xs1 xs2 xs3

(** [zip] takes a pair of list of the same length and returns
    the list of index-wise pairs *)
val zip (#a1 #a2:Type) (l1:list a1) (l2:list a2)
  : Pure (list (a1 & a2))
    (requires (let n = length l1 in n == length l2))
    (ensures (fun _ -> True))
let zip #a1 #a2 l1 l2 = map2 (fun x y -> x, y) l1 l2

(** [zip3] takes a 3-tuple of list of the same length and returns
    the list of index-wise 3-tuples *)
val zip3 (#a1 #a2 #a3:Type) (l1:list a1) (l2:list a2) (l3:list a3)
  : Pure (list (a1 & a2 & a3))
    (requires (let n = length l1 in n == length l2 /\ n == length l3))
    (ensures (fun _ -> True))
let zip3 #a1 #a2 #a3 l1 l2 l3 = map3 (fun x y z -> x,y,z) l1 l2 l3
