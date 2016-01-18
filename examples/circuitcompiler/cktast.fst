(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst fixnat.fst
--*)
module Ast
open List
open Fixnat

let natsize = 12

type value =
  | V_nat of (fixnat natsize)

type natop =
  | Natop_plus
(* TODO: Support other arithmetic operations
  | Natop_sub
  | Natop_mult
  | Natop_div
*)

type expr =
  | E_value of value
  | E_natop of natop * expr * expr

(* big step semantics *)
val evalexpr: e:expr -> Tot (v:value)
let rec evalexpr e =
  match e with
  | E_value v -> v
  | E_natop (op,e1,e2) ->
    let v1 = evalexpr e1 in
    let v2 = evalexpr e2 in
      (match op,v1,v2 with
        Natop_plus, V_nat n1, V_nat n2 -> V_nat (Fixnat.add #natsize n1 n2))
