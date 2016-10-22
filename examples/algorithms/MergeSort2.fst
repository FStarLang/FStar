(**
  This module implements a generic merge sort and proves it's stability.
  A great deal of inspiration taken from
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf.
  Verifies in ~11s for me.
**)
module MergeSort2
(** @author A Manning **)

open FStar.List.Tot
open GenericSort
open GenericStability
(**
  The key function k will appear frequently here.
  As will x, a value that some list is filtered for.
**)

(** First define the merge function without any properties.**)
val merge': #a:eqtype -> (l1:list a) -> (l2:list a) -> k:(a -> Tot int) -> Tot (list a)
let rec merge' #a l1 l2 k = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                        then h1::(merge' tl1 l2 k)
                        else h2::(merge' l1 tl2 k)
(** merging l and r returns a permutation of l and r **)
val merge'_permutation: #a:eqtype ->
  (l1:list a) ->
  (l2:list a) ->
  k:(a -> Tot int) ->
  Lemma(ensures permutation_2 (merge' l1 l2 k) l1 l2)
let rec merge'_permutation #a l1 l2 k = match (l1, l2) with
  | [], _ -> ()
  | _, [] -> ()
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                          then (merge'_permutation tl1 l2 k)
                        else (merge'_permutation l1 tl2 k)
(** merging two sorted lists returns a sorted list **)
val merge'_sorted: #a:eqtype ->
  (l1:list a) ->
  (l2:list a) ->
  k:(a -> Tot int) ->
  Lemma(requires (sorted l1 k /\ sorted l2 k))
    (ensures sorted (merge' l1 l2 k) k)
let rec merge'_sorted #a l1 l2 k =
match (l1, l2) with
  | [], _ -> ()
  | _, [] -> ()
  | h1::tl1, h2::tl2 -> if k h1 <= k h2
                          then (merge'_sorted tl1 l2 k)
                        else (merge'_sorted l1 tl2 k)
(** This identity for merge is important later **)
val merge'_hd: #a:eqtype -> l:list a{is_Cons l} -> r:list a{is_Cons r} -> k:(a -> Tot int) ->
  Lemma(ensures
  ((k (hd l) <= k (hd r)) ==> (merge' l r k = ((hd l)::(merge' (tl l) r k))) /\
  ((k (hd l) > k (hd r)) ==> (merge' l r k = ((hd r)::(merge' l (tl r) k))))))
let rec merge'_hd #a l r k = ()

(** Identity of merging **)
val merge'_l_nil: #a:eqtype -> (l: list a) -> k:(a -> Tot int) ->
  Lemma(ensures ((merge' l [] k) = l))
let merge'_l_nil #a l k = ()
(** Another merge identity **)
val merge'_nil_r: #a:eqtype -> (r: list a) -> k:(a -> Tot int) ->
  Lemma(ensures ((merge' [] r k) = r))
let merge'_nil_r #a r k = ()

(** filtering (l appended to r) wrt x is equivelant to merging l and r, then filtering wrt x **)
val merge'_filter_eq_inv: #a:eqtype -> (x:int) -> (l: list a{is_Cons l}) -> (r: list a{is_Cons r}) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k /\ sorted r k))
    (ensures ((is_Cons l /\ is_Cons r)/\(filter_eq x (l@r) k = filter_eq x (merge' l r k) k)))
let rec merge'_filter_eq_inv #a x l r k =
  if k (hd r) < k (hd l) then
    (stable_lift x l r k;
    merge'_hd l r k;
    if (tl r) = [] then merge'_l_nil l k
    else (merge'_filter_eq_inv x l (tl r) k;
      filter_eq_append x [hd r] (merge' l (tl r) k) k))
  else (merge'_hd l r k;
    if (tl l) = [] then (merge'_nil_r r k)
    else (merge'_filter_eq_inv x (tl l) r k;
      filter_eq_append x [hd l] (merge' (tl l) r k) k))

(** merge is stable **)
val merge'_stable: #a:eqtype -> x:int -> (l: list a{is_Cons l}) -> (r: list a{is_Cons r}) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k /\ sorted r k))
  (ensures is_stable x (l@r) (merge' l r k) k)
let merge'_stable #a x l r k = merge'_filter_eq_inv x l r k

(** Define mergesort, and show that it returns a sorted list **)
val mergesort': #a:eqtype -> l:list a -> k:(a -> Tot int) -> Tot (l':list a{sorted l' k})
let rec mergesort' #a l k =
  match l with
  | [] | [_] -> l
  | a::b::tl ->
    merge'_sorted (merge' [a] [b] k) (mergesort' tl k) k;
    merge' (merge' [a] [b] k) (mergesort' tl k) k

(** Mergesort is stable **)
val mergesort'_stable': #a:eqtype -> x:int -> l:list a -> k:(a -> Tot int) ->
  Lemma(ensures (is_stable x (mergesort' l k) l k))
let rec mergesort'_stable' #a x l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    if tl = [] then merge'_stable x [a] [b] k
    else
      merge'_stable x (merge' [a] [b] k) (mergesort' tl k) k;
      mergesort'_stable' x tl k

(** Mergesort returns a permutation of l**)
val mergesort'_permutation: #a:eqtype -> l:list a -> k:(a -> Tot int) ->
  Lemma(ensures (permutation l (mergesort' l k)))
let rec mergesort'_permutation #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    if tl = [] then ()
    else
      merge'_permutation [a] [b] k;
      merge'_permutation (merge' [a] [b] k) (mergesort' tl k) k;
      mergesort'_permutation tl k

(*
  Ideally, I'd like to type mergesort as stable rather than use is_stable.
*)

(** Finally, we define mergesort and prove it's properties**)
val mergesort: #a:eqtype -> x:int -> l:list a -> k:(a -> Tot int) ->
  Tot (l':list a{sorted l' k /\ permutation l l' /\ (is_stable x l' l k)})
let mergesort #a x l k =
  mergesort'_permutation l k;
  mergesort'_stable' x l k;
  mergesort' l k
