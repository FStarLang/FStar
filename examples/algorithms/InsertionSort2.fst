(** This module implements a stable insertion sort. **)
module InsertionSort2
(** @author A Manning **)
open FStar.List.Tot
open GenericSort
open GenericStability

val insert': #a:eqtype -> x:a -> l:(list a) -> k:(a -> Tot int) -> Tot (list a)
let rec insert' #a x l k =
  match l with
  | [] -> [x]
  | hd::tl ->
    if k x <= k hd then x::l
    else hd::(insert' x tl k)

val insert'_sorted: #a:eqtype -> x:a -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k))
  (ensures(sorted (insert' x l k) k))
let rec insert'_sorted #a x l k =
  match l with
  | [] | [_] -> ()
  | hd::tl ->
    if k x <= k hd then ()
    else insert'_sorted x tl k

val insert'_stable: #a:eqtype -> x:a -> t:int -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k))
  (ensures(filter_eq t (insert' x l k) k = filter_eq t ([x]@l) k ))
let rec insert'_stable #a x t l k =
  match l with
  | [] -> ()
  | hd::tl ->
    if k x <= k hd then filter_eq_append t [x] (insert' x tl k) k
    else insert'_stable x t tl k

val insert'_permutation: #a:eqtype -> x:a -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(ensures (permutation_2 (insert' x l k) l [x]))
let rec insert'_permutation #a x l k =
  match l with
  | [] | [_] -> ()
  | hd::tl ->
    if k x <= k hd then ()
    else insert'_permutation x tl k

val insertionsort': #a:eqtype -> l:(list a) -> k:(a -> Tot int) -> Tot (list a)
let rec insertionsort' #a l k =
  match l with
  | [] | [_] -> l
  | a::b::tl -> insert' a (insertionsort' (b::tl) k) k

val insertionsort'_sorted: #a:eqtype -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(ensures(sorted (insertionsort' l k) k))
let rec insertionsort'_sorted #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    insertionsort'_sorted (b::tl) k;
    insert'_sorted a (insertionsort' (b::tl) k) k

val insertionsort'_stable: #a:eqtype -> t:int -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(ensures is_stable t (insertionsort' l k) l k)
let rec insertionsort'_stable #a t l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    insertionsort'_stable t (b::tl) k;
    insertionsort'_sorted (b::tl) k;
    insert'_stable a t (insertionsort' (b::tl) k) k

val insertionsort'_permutation: #a:eqtype -> l:(list a) -> k:(a -> Tot int) ->
  Lemma(ensures(permutation (insertionsort' l k) l))
let rec insertionsort'_permutation #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    insertionsort'_permutation (b::tl) k;
    insert'_permutation a (insertionsort' (b::tl) k) k

val insertionsort: #a:eqtype -> t:int -> l:(list a) -> k:(a -> Tot int) ->
  Tot (l':list a{sorted l' k /\ is_stable t l l' k /\ permutation l l'})
let insertionsort #a t l k =
  insertionsort'_permutation l k;
  insertionsort'_stable t l k;
  insertionsort'_sorted l k;
  insertionsort' l k
