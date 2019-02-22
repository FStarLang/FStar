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
module Bug171c

open FStar.List.Tot

val sorted: #a:Type -> (a -> a -> Tot bool) -> list a -> Tot bool
let rec sorted #a f l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> f x y && sorted f (y::xs)

type permutation (#a:eqtype) (l1:list a) (l2:list a) =
    length l1 == length l2 /\ (forall n. mem n l1 == mem n l2)

type total_order (#a:eqtype) (f:a -> a -> Tot bool) =
    (forall a. f a a)                                         (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 == a2)       (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality      *)

val insert : #a:eqtype -> f:(a -> a -> Tot bool) -> i:a -> l:list a ->
             Pure  (list a)
                   (requires (total_order f /\ sorted f l))
                   (ensures (fun r -> sorted f r))
let rec insert #a f i l =
  match l with
  | [] -> [i]
  | hd::tl ->
     if f i hd then i::l
     else hd::(insert f i tl)
