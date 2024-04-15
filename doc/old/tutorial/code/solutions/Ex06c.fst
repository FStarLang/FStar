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
module Ex06c


val mem: #t:eqtype-> t -> list t -> Tot bool
let rec mem #t a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl


(* append now duplicates the elements of the first list *)
val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: hd :: append tl l2


val append_mem:  #t:eqtype -> l1:list t
              -> l2:list t
              -> Lemma (requires True)
                       (ensures (forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)))
                       [SMTPat (append l1 l2)]
let rec append_mem #t l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2


val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl


val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> x <= y && sorted (y::xs)


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
                                  /\ (forall x. mem x l = (mem x (fst (partition f l)) || mem x (snd (partition f l)))))))
                            [SMTPat (partition f l)]
let rec partition_lemma #t f l = match l with
    | [] -> ()
    | hd::tl -> partition_lemma f tl


val sorted_concat_lemma: l1:list int{sorted l1}
                      -> l2:list int{sorted l2}
                      -> pivot:int
                      -> Lemma (requires ((forall y. mem y l1 ==> not (pivot <= y))
                                       /\ (forall y. mem y l2 ==> pivot <= y)))
                               (ensures (sorted (append l1 (pivot::l2))))
                               [SMTPat (sorted (append l1 (pivot::l2)))]
let rec sorted_concat_lemma l1 l2 pivot = match l1 with
    | [] -> ()
    | hd::tl -> sorted_concat_lemma tl l2 pivot


type match_head (l1:list int) (l2:list int) =
  (l1 = [] /\ l2 = []) \/
  (exists h t1 t2. l1 = h::t1 /\ l2 = h::t2)

val dedup: l:list int{sorted l} -> Tot (l2:list int{sorted l2 /\ (forall i. mem i l = mem i l2) /\ match_head l l2})
  let rec dedup l =
    match l with
    | [] -> []
    | [x] -> [x]
    | h::h2::t ->
      if h = h2 then dedup (h2::t)
      else  h::dedup (h2::t)


let cmp i j = i <= j
val sort: l:list int -> Tot (m:list int{sorted m /\ (forall i. mem i l = mem i m)})
                            (decreases (length l))
let rec sort l = match l with
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (cmp pivot) tl in
    let l' = append (sort lo) (pivot::sort hi) in
    assert (forall i. mem i (pivot::sort hi) = mem i (append [pivot] (sort hi)));
    dedup l'
