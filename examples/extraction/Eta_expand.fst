module Eta_expand

open FStar.All

type t =
  | A
  | B

let dec: t -> Type0 = function
  | A -> int
  | B -> bool

let fun_a (x: int) (s: int): int = x
let fun_b (x: bool) (s: int): bool = x

let choose: a:t -> dec a -> int -> dec a = function
  | A -> fun_a
  | B -> fun_b

(* One recurring bug has been shadowing of variables when a function is eta-expanded two or
   more times during extraction. If this is the case, x will be 2 when executing the OCaml code *)
let _ =
  match (choose A 0 2) with
  | 0 -> () (* correct behaviour *)
  | 2 -> failwith "Failure of eta-expansion in FStar.Extraction.ML.Term"
  | _ -> failwith "Unknown failure"
