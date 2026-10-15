module BenchCFold
(* Koka's cfold: build a large expression, reassociate it and fold its
   constants; trees rebuilt bottom-up, with sharing of no cells. *)
module U32 = FStar.UInt32

type expr =
  | Var of int
  | Val of int
  | Add of expr & expr
  | Mul of expr & expr

let rec mk_expr (n: int) (v: int) : Tot expr (decreases (if n <= 0 then 0 else n)) =
  if n <= 0 then (if v = 0 then Var 1 else Val v)
  else Add (mk_expr (n - 1) (v + 1), mk_expr (n - 1) (if v > 0 then v - 1 else 0))

let rec append_add (e0 e3: expr) : expr =
  match e0 with
  | Add (e1, e2) -> Add (e1, append_add e2 e3)
  | _ -> Add (e0, e3)

let rec append_mul (e0 e3: expr) : expr =
  match e0 with
  | Mul (e1, e2) -> Mul (e1, append_mul e2 e3)
  | _ -> Mul (e0, e3)

let rec reassoc (e: expr) : expr =
  match e with
  | Add (e1, e2) -> append_add (reassoc e1) (reassoc e2)
  | Mul (e1, e2) -> append_mul (reassoc e1) (reassoc e2)
  | _ -> e

let rec cfold (e: expr) : expr =
  match e with
  | Add (e1, e2) ->
    let e1 = cfold e1 in
    let e2 = cfold e2 in
    (match e1 with
     | Val a ->
       (match e2 with
        | Val b -> Val (a + b)
        | Add (Val b, e) -> Add (Val (a + b), e)
        | Add (e, Val b) -> Add (Val (a + b), e)
        | _ -> Add (e1, e2))
     | _ -> Add (e1, e2))
  | Mul (e1, e2) ->
    let e1 = cfold e1 in
    let e2 = cfold e2 in
    (match e1 with
     | Val a ->
       (match e2 with
        | Val b -> Val (a * b)
        | Mul (Val b, e) -> Mul (Val (a * b), e)
        | Mul (e, Val b) -> Mul (Val (a * b), e)
        | _ -> Mul (e1, e2))
     | _ -> Mul (e1, e2))
  | _ -> e

let rec eval (e: expr) : int =
  match e with
  | Var _ -> 0
  | Val v -> v
  | Add (a, b) -> eval a + eval b
  | Mul (a, b) -> eval a * eval b

(* Expressions of depth 16, whose right spines after reassociation are at
   most 2^16 long: the recursion along them is not a tail call, and deeper
   ones overflow F#'s and C's default stacks. *)
let rec go (k: int) (acc: int) : Tot int (decreases (if k <= 0 then 0 else k)) =
  if k <= 0 then acc else
  let e = mk_expr 16 k in
  let v1 = eval e in
  let v2 = eval (cfold (reassoc e)) in
  go (k - 1) (if v1 = v2 then acc + v1 else acc - 1000000000)

let main () : U32.t =
  if go 16 0 = 9257597 then 0ul else 1ul
