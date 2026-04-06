(*
   Copyright 2014 Chantal Keller and Microsoft Research

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


module BinarySearch

open FStar.Seq


(* (\**********************************************************************\) *)
(* (\* Definition of a total order                                        *\) *)
(* (\**********************************************************************\) *)

(* opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) = *)
(*     (forall a. f a a)                                           (\* reflexivity   *\) *)
(*     /\ (forall a1 a2. f a1 a2 /\ f a2 a1  ==> a1 = a2)          (\* anti-symmetry *\) *)
(*     /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (\* transitivity  *\) *)
(*     /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (\* totality *\) *)


(**********************************************************************)
(* The binary search algorithm                                        *)
(**********************************************************************)

val bsearch_rec : t:(seq int) -> a:int
                  -> i:nat{i <= length t} -> j:int{-1 <= j /\ j < length t}
                  -> Tot (option (r:nat{r < length t}))   (decreases %[(j+1)-i])
let rec bsearch_rec t a i j =
  if i > j then
    None
  else
    let mid = (i + j)/2 in
    let b = index t mid in
    if b = a then               (* a = b *)
      Some mid
    else if b < a then          (* b < a *)
      bsearch_rec t a (mid+1) j
    else                        (* a < b *)
      bsearch_rec t a i (mid-1)


val bsearch : t:(seq int) -> int -> Tot (option (r:nat{r < length t}))
let bsearch t a = bsearch_rec t a 0 ((length t)-1)


(**********************************************************************)
(* Correctness                                                        *)
(**********************************************************************)

val bsearch_rec_correct : t:(seq int)
                          -> a:int -> i:nat{i <= length t} -> j:int{-1 <= j /\ j < length t}
                          -> Lemma
                               (requires True)
                               (ensures (Some? (bsearch_rec t a i j) ==>
                                           (Some?.v (bsearch_rec t a i j) >= i) /\
                                           (Some?.v (bsearch_rec t a i j) <= j) /\
                                           (index t (Some?.v (bsearch_rec t a i j)) = a)))
                               (decreases %[(j+1)-i])
let rec bsearch_rec_correct t a i j =
  if i > j then
    ()
  else
    let mid = (i + j)/2 in
    let b = index t mid in
    if b = a then               (* a = b *)
      ()
    else if b < a then          (* b < a *)
      bsearch_rec_correct t a (mid+1) j
    else                        (* a < b *)
      bsearch_rec_correct t a i (mid-1)


val bsearch_correct : t:(seq int) -> a:int
                      -> Lemma
                           (requires True)
                           (ensures (Some? (bsearch t a) ==>
                                       (Some?.v (bsearch t a) >= 0) /\
                                       (Some?.v (bsearch t a) < (length t)) /\
                                       (index t (Some?.v (bsearch t a)) = a)))
let bsearch_correct t a =
  bsearch_rec_correct t a 0 ((length t)-1)


(* (\**********************************************************************\) *)
(* (\* Completeness                                                       *\) *)
(* (\**********************************************************************\) *)

val hint1 : y:int -> a:int -> Lemma
  (requires True)
    (ensures (forall x. (((x <= y) /\ (y < a) /\ (x = a)) ==> False)))
let hint1 y a = ()

val hint2 : t:(seq int) -> a:int -> mid:int
  -> Lemma
       (requires
          (forall i1 i2.
            {:pattern index t i1; index t i2}
             (0 <= i1) ==> (i1 <= i2) ==> (i2 < length t) ==> (index t i1 <= index t i2)) /\
          (0 <= mid) /\
          (mid < length t) /\
          (index t mid < a))
       (ensures
          (forall p. (((0 <= p) /\ (p < length t) /\ (index t p = a) /\ (p <= mid)) ==> False)))
let hint2 t a mid = ()

val hint3 : y:int -> a:int -> Lemma
  (requires True)
    (ensures (forall x. (((y <= x) /\ (a < y) /\ (x = a)) ==> False)))
let hint3 y a = ()

val hint4 : t:(seq int) -> a:int -> mid:int
  -> Lemma
       (requires
          (forall i1 i2. 
              {:pattern index t i1; index t i2} 
            (0 <= i1) ==> (i1 <= i2) ==> (i2 < length t) ==> (index t i1 <= index t i2)) /\
          (0 <= mid) /\
          (mid < length t) /\
          (a < index t mid))
       (ensures
          (forall p. (((0 <= p) /\ (p < length t) /\ (index t p = a) /\ (mid <= p)) ==> False)))
let hint4 t a mid = hint3 (index t mid) a

val bsearch_rec_complete : t:(seq int)
                  -> a:int -> i:nat{i <= length t} -> j:int{-1 <= j /\ j < length t}
                  -> Lemma
                       (requires (forall i1 i2. (0 <= i1) ==> (i1 <= i2) ==> (i2 < length t) ==> (index t i1 <= index t i2)) /\
                                 (forall p. 0 <= p ==> p < length t ==> index t p = a ==> p < i ==> False) /\
                                 (forall p. 0 <= p ==> p < length t ==> index t p = a ==> j < p ==> False))
                       (ensures ((None? (bsearch_rec t a i j)) ==>
                                   (forall p. i <= p ==> p <= j ==> index t p = a ==> False)))
                       (decreases %[(j+1)-i])
let rec bsearch_rec_complete t a i j =
  if i > j then
    ()
  else
    let mid = (i + j)/2 in
    let b = index t mid in
    if b = a then               (* a = b *)
      ()
    else if b < a then (        (* b < a *)
      hint2 t a mid;
      bsearch_rec_complete t a (mid+1) j
    ) else (                    (* a < b *)
      hint4 t a mid;
      bsearch_rec_complete t a i (mid-1)
    )

val bsearch_complete :
  t:(seq int) -> a:int
  -> Lemma
       (requires (forall i1 i2. (0 <= i1) ==> (i1 <= i2) ==> (i2 < length t) ==> (index t i1 <= index t i2)))
       (ensures ((None? (bsearch t a)) ==>
                 (forall p. 0 <= p ==> p < length t ==> index t p <> a)))
let bsearch_complete t a =
  bsearch_rec_complete t a 0 ((length t)-1)
