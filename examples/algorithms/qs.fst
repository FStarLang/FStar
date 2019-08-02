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
module QS

open FStar.List

(* Specification of sortedness according to some comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

(* A lemma about List.partition ... duh *)
val partition_lemma: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures ((fun l1 l2 -> 
                                     (length l1 + length l2 = length l
                                      /\ (forall x. mem x l1 ==> f x)
                                      /\ (forall x. mem x l2 ==> not (f x))
                                      /\ (forall x. mem x l = (mem x l1 || mem x l2))))
                                        (fst (partitionT f l))
                                        (snd (partitionT f l))))
                           (* [SMTPat (partitionT f l)] (\* injected to the solver *\) *)
let rec partition_lemma f l = match l with 
  | [] -> ()
  | hd::tl -> partition_lemma f tl


opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)

val sorted_concat_lemma:  #a:Type
               ->  f:(a -> a -> Tot bool)
               ->  l1:list a{sorted f l1}
               ->  l2:list a{sorted f l2}
               ->  pivot:a
               ->  Lemma (requires (total_order a f
                                    /\ (forall y. mem y l1 ==> not(f pivot y))
                                    /\ (forall y. mem y l2 ==> f pivot y))
)                         (ensures (sorted f (l1@(pivot::l2))))
                          [SMTPat (sorted f (l1@(pivot::l2)))]
let rec sorted_concat_lemma f l1 l2 pivot = match l1 with 
  | [] -> ()
  | hd::tl -> sorted_concat_lemma f tl l2 pivot


(* The implementation of quicksort: happily, the code is completely unpolluted by proof. *)
val sort: f:('a -> 'a -> Tot bool){total_order 'a f}
      ->  l:list 'a
      ->  Tot (m:list 'a{sorted f m /\ (forall x. mem x l = mem x m)})
              (decreases (length l))
let rec sort f = function
  | [] -> []
  | pivot::tl -> 
    let hi, lo  = partitionT (f pivot) tl in 
    partition_lemma (f pivot) tl;
    (sort f lo)@(pivot::sort f hi)
