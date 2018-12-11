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
module FStar.BigOps

private
let __reduce__ = ()

unfold let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%__reduce__];
     primops;
     simplify]
     x

[@__reduce__]
let rec foldr_gtot' (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b) : GTot b =
  match l with
  | [] -> x
  | hd::tl -> f hd (foldr_gtot' tl f x)
unfold
let foldr_gtot (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b) : GTot b =
  normal (foldr_gtot' l f x)

unfold
let map_gtot (f:'a -> GTot 'b) (x:list 'a) = foldr_gtot x (fun x tl -> f x :: tl) []

[@__reduce__]
private
let map_op' (#a:Type) (#b:Type) (#c:Type) (op:b -> c -> GTot c) (f:a -> GTot b) (l:list a) (z:c) : GTot c =
  foldr_gtot #a #c l (fun x acc -> f x `op` acc) z

unfold
let big_and f l : prop = normal (map_op' (fun x y -> x /\ y) f l True)
unfold
let big_or f l : prop = normal (map_op' (fun x y -> x \/ y) f l False)

[@__reduce__]
private
let rec pairwise_op' (#a:Type) (#b:Type) (op:b -> b -> GTot b) (f:a -> a -> b) (l:list a) (z:b) : GTot b =
  match l with
  | [] -> z
  | hd::tl -> map_op' op (f hd) tl z `op` pairwise_op' op f tl z
unfold
let pairwise_and (#a:Type) (f:a -> a -> Type0) (l:list a) : prop = normal (pairwise_op' (fun x y -> x /\ y) f l True)
unfold
let pairwise_or (#a:Type) (f:a -> a -> Type0) (l:list a) : prop = normal (pairwise_op' (fun x y -> x \/ y) f l False)


val big_op_nil
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (z:c)
  : Lemma (map_op' op f [] z == z)

val big_op_cons
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (hd:a) (tl:list a) (z:c)
  : Lemma (map_op' op f (hd::tl) z == f hd `op` map_op' op f tl z)

val big_and_nil (#a:Type) (f:a -> Type)
  : Lemma (big_and f [] == True)

val big_and_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_and f (hd :: tl) == (f hd /\ big_and f tl))

val big_or_nil (#a:Type) (f:a -> Type)
  : Lemma (big_or f [] == False)

val big_or_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_or f (hd :: tl) == (f hd \/ big_or f tl))

val pairwise_and_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_and f [] == True)

val pairwise_and_cons (#a:Type) (f:a -> a -> Type0) (hd:a) (tl:list a)
  : Lemma (pairwise_and f (hd::tl) == (big_and (f hd) tl /\ pairwise_and f tl))

val pairwise_or_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_or f [] == False)

val pairwise_or_cons (#a:Type) (f:a -> a -> Type0) (hd:a) (tl:list a)
  : Lemma (pairwise_or f (hd::tl) == (big_or (f hd) tl \/ pairwise_or f tl))
