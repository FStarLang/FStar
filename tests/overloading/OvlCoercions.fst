module OvlCoercions
open FStar.List.Tot
open OvlInt
open OvlBool

(* Regression: these are the shapes that broke when 'compat' first became
   the default. In each case the filter, which only ever compares head
   symbols, would eliminate the scope-order candidate even though that
   candidate is the one that checks. Nothing recovers from a wrong
   elimination, so Overload.compatible has to be generous enough not to
   make one. *)

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

(* 3. When nothing discriminates, the scope-order candidate is returned,
   so this means OvlBool.f, as it does with overloading disabled. *)
let primary_kept (x:bool) : bool = f x
