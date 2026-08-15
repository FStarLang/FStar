module OvlCoercions
open FStar.List.Tot
open OvlInt
open OvlBool

(* Regression: these are the shapes that broke when 'compat' first became
   the default. In each case the filter, which only ever compares head
   symbols, wants to eliminate the candidate that name resolution picks
   today -- and that candidate nevertheless checks. *)

(* 1. Implicit coercion. This module's own `sorted` shadows
   FStar.List.Tot.Properties.sorted, opened above, so it is the primary
   candidate and must stay the answer. It returns a bool but is used where
   a prop is expected, so the two head symbols do not match; `b2t` is what
   actually reconciles them. The other candidate takes a comparison
   function first, so after one explicit argument its result is an arrow
   that nothing can eliminate. *)
let rec sorted (l : list int) : bool =
  match l with
  | [] | [_] -> true
  | x :: y :: xs -> x <= y && sorted (y :: xs)

val use_sorted : x:int -> l:list int -> Lemma (sorted (x :: l) ==> True)
let use_sorted x l = ()

(* 2. Subtyping. `OvlInt.id : int -> int` is not eliminated by an expected
   type of `nat -> int`, even though the argument heads do not match. *)
let sub_ok : nat -> int = id

(* 3. When the primary candidate does check, it is kept, so this still
   means OvlBool.f exactly as it did before overloading existed. *)
let primary_kept (x:bool) : bool = f x
