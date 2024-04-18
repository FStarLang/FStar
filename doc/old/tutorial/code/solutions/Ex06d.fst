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
module Ex06d
#set-options "--z3rlimit_factor 2"

(* Instead of a Boolean check that an element belongs to a list, count
the number of occurrences of an element in a list *)
val count : #t:eqtype -> t -> list t -> Tot nat
let rec count #t (x:t) (l:list t) = match l with
  | hd::tl -> if hd=x then 1 + count x tl else count x tl
  | [] -> 0


let mem #t x l = count #t x l > 0


val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2


val append_count: #t:eqtype -> l:list t -> m:list t
               -> Lemma (requires True)
                        (ensures (forall x. count x (append l m) = (count x l + count x m)))
let rec append_count #t l m = match l with
  | [] -> ()
  | hd::tl -> append_count tl m


val append_mem: #t:eqtype -> l:list t -> m:list t
               -> Lemma (requires True)
                        (ensures (forall x. mem x (append l m) = (mem x l || mem x m)))
let append_mem #t l m = append_count l m


val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl


(* Specification of sortedness according to some comparison function f *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> f x y && sorted f (y::xs)


val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2


val partition_lemma: #t:eqtype -> f:(t -> Tot bool)
                   -> l:list t
                   -> Lemma (requires True)
                            (ensures ((length (fst (partition f l)) + length (snd (partition f l)) = length l
                                  /\ (forall x. mem x (fst (partition f l)) ==> f x)
                                  /\ (forall x. mem x (snd (partition f l)) ==> not (f x))
                                  /\ (forall x. mem x l = (mem x (fst (partition f l)) || mem x (snd (partition f l))))
                                  /\ (forall x. count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))))
let rec partition_lemma #t f l = match l with
    | [] -> ()
    | hd::tl -> partition_lemma f tl


(* Defining a new predicate symbol *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)


val sorted_concat_lemma: #a:eqtype
                      -> f:(a -> a -> Tot bool)
                      -> l1:list a{sorted f l1}
                      -> l2:list a{sorted f l2}
                      -> pivot:a
                      -> Lemma (requires (total_order a f
                                       /\ (forall y. mem y l1 ==> not (f pivot y))
                                       /\ (forall y. mem y l2 ==> f pivot y)))
                               (ensures (sorted f (append l1 (pivot::l2))))

let rec sorted_concat_lemma #a f l1 l2 pivot = 
  match l1 with
  | [] -> ()
  | hd::tl -> sorted_concat_lemma f tl l2 pivot


val sort: #t:eqtype -> f:(t -> t -> Tot bool){total_order t f}
       -> l:list t
       -> Tot (m:list t{sorted f m /\ (forall i. mem i l = mem i m) /\ (forall i. count i l = count i m)})
              (decreases (length l))
let rec sort #t f l = match l with
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (f pivot) tl in
    partition_lemma (f pivot) tl;
    let lo' = sort f lo in
    let hi' = sort f hi in
    append_count lo' (pivot::hi');
    append_mem lo' (pivot::hi');
    sorted_concat_lemma f lo' hi' pivot;
    append lo' (pivot::hi')
