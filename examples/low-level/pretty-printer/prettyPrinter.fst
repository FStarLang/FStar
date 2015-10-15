(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --admit_fsi FStar.Ghost --admit_fsi FStar.Regions.RSTArray;
    other-files:ext.fst set.fsi seq.fsi heap.fst st.fst all.fst list.fst stack.fst listset.fst ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst rstWhile.fst constr.fst word.fst array.fsi arrayAlgos.fst
  --*)

module PrettyPrinter

open FStar.Regions.RST
open FStar.Regions.RSTArray
open ArrayAlgos

open StackAndHeap
open Stack

open FStar.Regions.Heap
open FStar.Regions.Located

open FStar.Ghost

(* Missing definitions from F* *)
assume val string_of_int : int -> Tot string
assume val random_nat: y:nat -> Tot (x:nat{0 <= x /\ x < y})


type expr =
| Add: expr -> expr -> expr
| Sub: expr -> expr -> expr
| Mul: expr -> expr -> expr
| Div: expr -> expr -> expr
| Const: int -> expr


let rec print_add = function
  | Add e1 e2 ->
      print_add e1 ^ " + " ^ print_add e2
  | Sub e1 e2 ->
      print_add e1 ^ " - " ^ print_mul e2
  | e ->
      print_mul e

and print_mul = function
  | Mul e1 e2 ->
      print_mul e1 ^ " * " ^ print_mul e2
  | Div e1 e2 ->
      print_mul e1 ^ " / " ^ print_atomic e2
  | e ->
      print_atomic e

and print_atomic = function
  | Const i ->
      string_of_int i
  | e ->
      "(" ^ print_ e ^ ")"

and print_ e =
  print_add e


(* -------------------------------------------------------------------------- *)

let max = 22

let rec gen h =
  if h = 1 then
    Const (random_nat max)
  else match random_nat 4 with
  | 0 -> Add (gen (h - 1)) (gen (h - 1))
  | 1 -> Sub (gen (h - 1)) (gen (h - 1))
  | 2 -> Mul (gen (h - 1)) (gen (h - 1))
  | 3 -> Div (gen (h - 1)) (gen (h - 1))


let _main =
  let e = gen max in
  let s = print_ e in
  ignore s
