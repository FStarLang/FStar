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
module L = FStar.List.Tot

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

val normal_eq (#a:Type) (f:a)
  : Lemma (f == normal f)

[@__reduce__]
let rec foldr_gtot' (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b) : GTot b =
  match l with
  | [] -> x
  | hd::tl -> f hd (foldr_gtot' tl f x)

[@__reduce__] unfold
let foldr_gtot (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b) : GTot b =
  normal (foldr_gtot' l f x)

[@__reduce__]
let map_gtot' (f:'a -> GTot 'b) (x:list 'a) = foldr_gtot x (fun x tl -> f x :: tl) []
[@__reduce__] unfold
let map_gtot (f:'a -> GTot 'b) (x:list 'a) = normal (map_gtot' f x)

[@__reduce__] private
let map_op' (#a:Type) (#b:Type) (#c:Type) (op:b -> c -> GTot c) (f:a -> GTot b) (l:list a) (z:c) : GTot c =
  foldr_gtot #a #c l (fun x acc -> f x `op` acc) z

[@__reduce__]
let big_and' f l = map_op' l_and f l True
[@__reduce__] unfold
let big_and f l = normal (big_and' f l)

[@__reduce__]
let big_or' f l = map_op' l_or f l False
[@__reduce__] unfold
let big_or f l = normal (big_or' f l)

[@__reduce__]
private
let rec pairwise_op' (#a:Type) (#b:Type) (op:b -> b -> GTot b) (f:a -> a -> b) (l:list a) (z:b) : GTot b =
  match l with
  | [] -> z
  | hd::tl -> map_op' op (f hd) tl z `op` pairwise_op' op f tl z

[@__reduce__]
let pairwise_and' (#a:Type) (f:a -> a -> Type) (l:list a) = pairwise_op' l_and f l True
[@__reduce__] unfold
let pairwise_and (#a:Type) (f:a -> a -> Type) (l:list a) = normal (pairwise_and' f l)

[@__reduce__]
let pairwise_or' (#a:Type) (f:a -> a -> Type) (l:list a) = pairwise_op' l_or f l False
[@__reduce__] unfold
let pairwise_or (#a:Type) (f:a -> a -> Type) (l:list a) = normal (pairwise_or' f l)

////////////////////////////////////////////////////////////////////////////////
val big_op_nil
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (z:c)
  : Lemma (map_op' op f [] z == z)

val big_op_cons
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (hd:a) (tl:list a) (z:c)
  : Lemma (map_op' op f (hd::tl) z == f hd `op` map_op' op f tl z)

////////////////////////////////////////////////////////////////////////////////
val big_and_nil (#a:Type) (f:a -> Type)
  : Lemma (big_and f [] == True)

val big_and_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_and f (hd :: tl) == (f hd /\ big_and f tl))

val big_and_prop (#a:Type) (f:a -> Type) (l:list a)
  : Lemma (big_and f l `subtype_of` unit)

val big_and_forall (#a:Type) (f: a -> Type) (l:list a)
  : Lemma (big_and f l <==> (forall x. L.memP x l ==> f x))

////////////////////////////////////////////////////////////////////////////////
val big_or_nil (#a:Type) (f:a -> Type)
  : Lemma (big_or f [] == False)

val big_or_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_or f (hd :: tl) == (f hd \/ big_or f tl))

val big_or_prop (#a:Type) (f:a -> Type) (l:list a)
  : Lemma (big_or f l `subtype_of` unit)

val big_or_exists (#a:Type) (f: a -> Type) (l:list a)
  : Lemma (big_or f l <==> (exists x. L.memP x l /\ f x))

////////////////////////////////////////////////////////////////////////////////
let symmetric (#a:Type) (f: a -> a -> Type) =
  forall x y. f x y <==> f y x

let reflexive (#a:Type) (f: a -> a -> Type) =
  forall x. f x x

let anti_reflexive (#a:Type) (f: a -> a -> Type) =
  forall x. ~(f x x)

////////////////////////////////////////////////////////////////////////////////
val pairwise_and_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_and f [] == True)

val pairwise_and_cons (#a:Type) (f:a -> a -> Type0) (hd:a) (tl:list a)
  : Lemma (pairwise_and f (hd::tl) == (big_and (f hd) tl /\ pairwise_and f tl))

val pairwise_and_prop (#a:Type) (f:a -> a -> Type) (l:list a)
  : Lemma (pairwise_and f l `subtype_of` unit)

val pairwise_and_forall (#a:Type) (f: a -> a -> Type) (l:list a)
  : Lemma
    (requires symmetric f /\ (L.no_repeats_p l \/ reflexive f))
    (ensures (pairwise_and f l <==> (forall x y. L.memP x l /\ L.memP y l /\ x =!= y ==> f x y)))

////////////////////////////////////////////////////////////////////////////////
val pairwise_or_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_or f [] == False)

val pairwise_or_cons (#a:Type) (f:a -> a -> Type0) (hd:a) (tl:list a)
  : Lemma (pairwise_or f (hd::tl) == (big_or (f hd) tl \/ pairwise_or f tl))

val pairwise_or_prop (#a:Type) (f:a -> a -> Type) (l:list a)
  : Lemma (pairwise_or f l `subtype_of` unit)

val pairwise_or_exists (#a:Type) (f: a -> a -> Type) (l:list a)
  : Lemma
    (requires symmetric f /\ (L.no_repeats_p l \/ anti_reflexive f))
    (ensures (pairwise_or f l <==> (exists x y. L.memP x l /\ L.memP y l /\ x =!= y /\ f x y)))

