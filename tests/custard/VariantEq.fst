module VariantEq

module U16 = FStar.UInt16

type kind =
  | Known
  | Unknown of U16.t

let by_match (x:kind) : bool =
  match x with
  | Known -> true
  | Unknown _ -> false

let by_equality (x:kind) : bool = Known = x

let two_way (x:kind) (y:kind) : bool = x = y

type pair = { p_a : U16.t; p_b : bool }

let rec_eq (x:pair) (y:pair) : bool = x = y

let tup_eq (x : U16.t & bool) (y : U16.t & bool) : bool = x = y

let opt_eq (x : option U16.t) (y : option U16.t) : bool = x = y

(* An enum is a scalar already; its comparison is C's own. *)
type flag =
  | Lo
  | Hi

let flag_eq (x:flag) (y:flag) : bool = x = y

let main () : FStar.All.ML FStar.Int32.t =
  let a = Known in
  let b = Unknown 3us in
  let p = { p_a = 1us; p_b = true } in
  if by_match a && not (by_equality b) && by_equality a &&
     not (two_way a b) && two_way b b &&
     rec_eq p p && not (rec_eq p { p with p_b = false }) &&
     tup_eq (1us, true) (1us, true) && not (tup_eq (1us, true) (2us, true)) &&
     opt_eq (Some 1us) (Some 1us) && not (opt_eq (Some 1us) None) &&
     flag_eq Lo Lo && not (flag_eq Lo Hi)
  then 0l else 1l
