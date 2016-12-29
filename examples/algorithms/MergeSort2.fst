module MergeSort2
(**
  @author: A Manning
  @summary: This module implements a generic merge sort and proves it's stability.
  A great deal of inspiration taken from
  http://research.microsoft.com/en-us/um/people/leino/papers/krml241.pdf.
  Verifies in ~8s for me.
 **)

open FStar.List.Tot
open GenericSort
open GenericStability
(*
  The key function k will appear frequently here.
*)

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
val merge'_filter_eq_inv: #a:eqtype -> (l: list a{is_Cons l}) -> (r: list a{is_Cons r}) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k /\ sorted r k))
    (ensures (forall x. ((is_Cons l /\ is_Cons r)/\ (filter_eq x (l@r) k = filter_eq x (merge' l r k) k))))
let rec merge'_filter_eq_inv #a l r k =
  if k (hd r) < k (hd l) then
    (stable_lift l r k;
    merge'_hd l r k;
    if (tl r) = [] then merge'_l_nil l k
    else (merge'_filter_eq_inv l (tl r) k;
      filter_eq_append [hd r] (merge' l (tl r) k) k))
  else (merge'_hd l r k;
    if (tl l) = [] then (merge'_nil_r r k)
    else (merge'_filter_eq_inv (tl l) r k;
      filter_eq_append [hd l] (merge' (tl l) r k) k))

(** merge is stable **)
val merge'_stable: #a:eqtype -> (l: list a{is_Cons l}) -> (r: list a{is_Cons r}) -> k:(a -> Tot int) ->
  Lemma(requires (sorted l k /\ sorted r k))
  (ensures stable (l@r) (merge' l r k) k)
let merge'_stable #a l r k = merge'_filter_eq_inv l r k

(** split_n splits a list at index n **)
val split_n: #a:eqtype -> (l:list a) -> n:nat{0 < n /\ n < length l} ->
  Tot (l_tup:(list a * list a){(fst l_tup)@(snd l_tup) = l
    /\ length (fst l_tup) < length l
    /\ length (snd l_tup) < length l
    /\ permutation_2 l (fst l_tup) (snd l_tup)})
let rec split_n #a l n =
  match l with
  | hd::tl -> if n = 1 then ([hd],tl)
    else let next = split_n tl (n-1) in ((hd::(fst next)),(snd next))

(** split_half splits a list halfway **)
val split_half: #a:eqtype -> (l:list a{length l >= 2}) ->
  Tot (l_tup:(list a * list a))
let split_half #a l = split_n l ((length l) / 2)

(** Define mergesort **)
val mergesort': #a:eqtype -> l:list a -> k:(a -> Tot int) -> Tot (l':list a) (decreases (length l))
let rec mergesort' #a l k =
  match l with
  | [] | [_] -> l
  | a::b::tl ->
    let splt = split_half l in
    merge' (mergesort' (fst splt) k) (mergesort' (snd splt) k) k

(** Mergesort returns a sorted list **)
val mergesort'_sorted: #a:eqtype -> l:list a -> k:(a -> Tot int) ->
  Lemma(ensures(sorted (mergesort' l k) k))
  (decreases (length l))
let rec mergesort'_sorted #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    let splt = split_half l in
    mergesort'_sorted (fst splt) k;
    mergesort'_sorted (snd splt) k;
    merge'_sorted (mergesort' (fst splt) k) (mergesort' (snd splt) k) k

(** Mergesort returns a permutation of it's input **)
val mergesort'_permutation: #a:eqtype -> l:list a -> k:(a -> Tot int) ->
  Lemma(ensures (permutation l (mergesort' l k)))
  (decreases (length l))
let rec mergesort'_permutation #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    let splt = split_half l in
    mergesort'_permutation (fst splt) k;
    mergesort'_permutation (snd splt) k;
    merge'_permutation (mergesort' (fst splt) k) (mergesort' (snd splt) k) k

(** Mergesort is stable **)
val mergesort'_stable: #a:eqtype -> l:list a -> k:(a -> Tot int) ->
  Lemma(ensures (stable l (mergesort' l k) k))
  (decreases (length l))
let rec mergesort'_stable #a l k =
  match l with
  | [] | [_] -> ()
  | a::b::tl ->
    let splt = split_half l in
    mergesort'_stable (fst splt) k;
    mergesort'_stable (snd splt) k;
    stable_append (fst splt) (mergesort' (fst splt) k) (snd splt) (mergesort' (snd splt) k) k;
    mergesort'_sorted (fst splt) k;
    mergesort'_sorted (snd splt) k;
    merge'_stable (mergesort' (fst splt) k) (mergesort' (snd splt) k) k

(** Finally, we define mergesort and prove it's properties**)
val mergesort: #a:eqtype -> l:list a -> k:(a -> Tot int) ->
  Tot (l':list a{sorted l' k /\ permutation l l' /\ (stable l' l k)})
let mergesort #a l k =
  mergesort'_sorted l k;
  mergesort'_permutation l k;
  mergesort'_stable l k;
  mergesort' l k
