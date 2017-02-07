(**
  @summary: This module defines sorting stability on generic lists.
  @author: A Manning
**)
module GenericStability
open FStar.List.Tot
open FStar.List.Tot
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
  Lemma (ensures (forall x. (mem x xs /\ key x = k) <==> mem x (filter_eq k xs key)))
let rec filter_eq_contains #a k xs key =
  match xs with
  | [] -> ()
  | hd::tl ->
    filter_eq_contains k tl key

val filter_eq_append: #a:eqtype -> (l1: list a) -> (l2: list a) -> k:(a -> Tot int) ->
  Lemma (ensures (forall x. (filter_eq x l1 k)@(filter_eq x l2 k) = filter_eq x (l1@l2) k))
let rec filter_eq_append #a l1 l2 k =
  match l1 with
  | [] -> ()
  | hd::tl ->
    filter_eq_append tl l2 k

val filter_eq_not_contains: #a:eqtype -> (l: list a) -> k:(a -> Tot int) ->
  Lemma (ensures (forall x. (filter_eq x l k) = [] <==> ~(exists e. (mem e l /\ k e = x))))
let rec filter_eq_not_contains #a l k =
  match l with
  | [] -> ()
  | hd::tl ->
    filter_eq_not_contains tl k

val filter_eq_single: #a:eqtype ->
  (l: list a{Cons? l /\ length l = 1}) ->
  k:(a -> Tot int) ->
  Lemma (ensures (forall x. (k (hd l) = x ) ==> filter_eq x l k = [hd l]))
let filter_eq_single #a l k = ()

val filter_eq_sorted_lt:  #a:eqtype -> l:list a{Cons? l} -> k:(a -> Tot int) ->
  Lemma (requires (sorted l k))
        (ensures (forall x. (x < k (hd l)) ==> (filter_eq x l k = [])))
let filter_eq_sorted_lt #a l k =
  sorted_lt l k;
  filter_eq_not_contains l k

val filter_eq_first: #a:eqtype ->
  (l1: list a{Cons? l1}) ->
  (l2: list a{Cons? l2}) ->
  k:(a -> Tot int) ->
  Lemma (requires (sorted l1 k) /\  (k (hd l1) > k (hd l2)))
        (ensures (forall x. (k (hd l2) = x ) ==>
    filter_eq x (l1@l2) k = ((filter_eq x ((hd l2)::l1) k )@(filter_eq x (tl l2) k))))
let filter_eq_first #a l1 l2 k =
  filter_eq_append l1 l2 k;
  filter_eq_sorted_lt l1 k

type stable (#a:eqtype) (l1:list a) (l2:list a) (k:(a -> Tot int)) = forall x. (filter_eq x l1 k = filter_eq x l2 k)

val stable_lift: #a:eqtype ->
  (l1: list a{Cons? l1}) ->
  (l2: list a{Cons? l2}) ->
  k:(a -> Tot int) ->
  Lemma (requires (sorted l1 k) /\ (k (hd l1) > k (hd l2)))
        (ensures (stable (l1@l2) (((hd l2)::l1)@(tl l2)) k))
let stable_lift #a l1 l2 k =
  filter_eq_append l1 l2 k;
  filter_eq_append ((hd l2)::l1) (tl l2) k;
  filter_eq_first l1 l2 k;
  filter_eq_append ((hd l2)::l1) (tl l2) k

val stable_append_l: #a:eqtype ->
  (l: list a) ->
  (r: list a) ->
  (r': list a) ->
  k:(a -> Tot int) ->
  Lemma (ensures (stable r r' k ==> stable (l@r) (l@r') k))
let rec stable_append_l #a l r r' k =
  match l with
  | [] -> ()
  | hd::tl -> stable_append_l tl r r' k

val stable_append_r: #a:eqtype ->
  (l: list a) ->
  (l': list a) ->
  (r: list a) ->
  k:(a -> Tot int) ->
  Lemma (requires (stable l l' k))
        (ensures(stable (l@r) (l'@r) k))
let rec stable_append_r #a l l' r k =
  filter_eq_append l r k;
  filter_eq_append l' r k

val stable_transitive: #a:eqtype
  -> (l1:list a)
  -> (l2:list a)
  -> (l3:list a)
  -> k:(a -> Tot int)
  -> Lemma (requires (stable l1 l2 k /\ stable l2 l3 k))
          (ensures (stable l1 l3 k))
let stable_transitive #a l1 l2 l3 k = ()

val stable_append: #a:eqtype
  -> (l1:list a)
  -> (l2:list a)
  -> (r1:list a)
  -> (r2:list a)
  -> k:(a -> Tot int)
  -> Lemma (requires (stable l1 l2 k /\ stable r1 r2 k))
          (ensures (stable (l1@r1) (l2@r2) k))
let stable_append #a l1 l2 r1 r2 k =
  stable_append_r l1 l2 r1 k;
  stable_append_l l2 r1 r2 k
