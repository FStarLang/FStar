(**
  @summary: This module defines sorting stability on the integers.
  @author: A Manning
**)
module GenericStability
open FStar.List.Tot
open FStar.ListProperties
open GenericSort
(*
  This module is heavily inspired by Leino and Lucio's 2012 paper,
  'An Assertional Proof of the Stability and Correctness of Natural Mergesort'.
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf
*)


(**
  filterEq returns the elements of a list that have the same key as n.
**)
val filter_eq: #a:Type -> (x:int) -> (xs: list a) -> k:(a -> Tot int) -> Tot (list a)
let rec filter_eq #a x xs k =
  match xs with
  | [] -> []
  | hd::tl
    -> if k hd = x then
        hd::(filter_eq x tl k)
      else filter_eq x tl k

val filter_eq_contains: #a:eqtype -> (k:int) -> (xs: list a) -> key:(a -> Tot int) ->
  Lemma(ensures(forall x. (mem x xs /\ key x = k) <==> mem x (filter_eq k xs key)))
let rec filter_eq_contains #a k xs key =
  match xs with
  | [] -> ()
  | hd::tl ->
    filter_eq_contains k tl key

val filter_eq_append: #a:eqtype -> (x:int) -> (l1: list a) -> (l2: list a) -> k:(a -> Tot int) ->
  Lemma(ensures((filter_eq x l1 k)@(filter_eq x l2 k) = filter_eq x (l1@l2) k))
let rec filter_eq_append #a x l1 l2 k =
  match l1 with
  | [] -> ()
  | hd::tl ->
    filter_eq_append x tl l2 k

val filter_eq_not_contains: #a:eqtype -> (x:int) -> (l: list a) -> k:(a -> Tot int) ->
  Lemma(ensures (filter_eq x l k) = [] <==> ~(exists e. (mem e l /\ k e = x)))
let rec filter_eq_not_contains #a x l k =
  match l with
  | [] -> ()
  | hd::tl ->
    filter_eq_not_contains x tl k;
    mem_existsb (fun y -> k y = x) l

val is_stable: #a:eqtype -> int -> list a -> list a -> (a -> Tot int) -> Tot bool
let is_stable #a x l1 l2 k = (filter_eq x l1 k = filter_eq x l2 k)

type stable (#a:eqtype) (l1:list a) (l2:list a) = forall x k. is_stable x l1 l2 k

val filter_eq_single: #a:eqtype ->
  (x:int) ->
  (l: list a{is_Cons l /\ length l = 1}) ->
  k:(a -> Tot int) ->
  Lemma(ensures((k (hd l) = x ) ==> filter_eq x l k = [hd l]))
let filter_eq_single #a x l k = ()

val filter_eq_sorted_lt:  #a:eqtype -> x: int -> l:list a{is_Cons l} -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k /\ x < k (hd l)))
  (ensures(filter_eq x l k = []))
let filter_eq_sorted_lt #a x l k =
  sorted_lt x l k;
  filter_eq_not_contains x l k


val filter_eq_first: #a:eqtype ->
  (x:int) ->
  (l1: list a{is_Cons l1}) ->
  (l2: list a{is_Cons l2}) ->
  k:(a -> Tot int) ->
  Lemma(requires (sorted l1 k) /\ (k (hd l2) = x ) /\  (k (hd l1) > k (hd l2)))
  (ensures (k (hd l2) = x ) ==> filter_eq x (l1@l2) k = ((filter_eq x ((hd l2)::l1) k )@(filter_eq x (tl l2) k)))
let filter_eq_first #a x l1 l2 k =
  filter_eq_append x l1 l2 k;
  filter_eq_sorted_lt x l1 k

val stable_lift: #a:eqtype ->
  (x:int) ->
  (l1: list a{is_Cons l1}) ->
  (l2: list a{is_Cons l2}) ->
  k:(a -> Tot int) ->
  Lemma(requires (sorted l1 k) /\ (k (hd l1) > k (hd l2)))
  (ensures (is_stable x (l1@l2) (((hd l2)::l1)@(tl l2)) k))
let stable_lift #a x l1 l2 k =
  filter_eq_append x l1 l2 k;
  append_assoc (filter_eq x l1 k) (filter_eq x [hd l2] k) (filter_eq x (tl l2) k);
  if (k (hd l2) = x) then(
    filter_eq_append x ((hd l2)::l1) (tl l2) k;
    filter_eq_first x l1 l2 k)
  else filter_eq_append x ((hd l2)::l1) (tl l2) k

val stable_append_l: #a:eqtype ->
  (x:int) ->
  (l: list a) ->
  (r: list a) ->
  (r': list a) ->
  k:(a -> Tot int) ->
  Lemma(ensures(is_stable x r r' k ==> is_stable x (l@r) (l@r') k))
let rec stable_append_l #a x l r r' k =
  match l with
  | [] -> ()
  | hd::tl -> stable_append_l x tl r r' k

val stable_append_r: #a:eqtype ->
  (x:int) ->
  (l: list a) ->
  (l': list a) ->
  (r: list a) ->
  k:(a -> Tot int) ->
  Lemma(requires(is_stable x l l' k))
  (ensures(is_stable x (l@r) (l'@r) k))
let rec stable_append_r #a x l l' r k =
  filter_eq_append x l r k;
  filter_eq_append x l' r k
