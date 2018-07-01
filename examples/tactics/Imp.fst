module Imp

#set-options "--debug Imp --debug_level SMTQuery"

open FStar.Mul

type rval = int
type reg = | R of n:nat{n < 10}
type regmap = reg -> rval

noeq
type inst =
    | Add : reg -> reg -> reg -> inst
    | Sub : reg -> reg -> reg -> inst
    | Mul : reg -> reg -> reg -> inst
    | Const : rval -> reg -> inst

type prog = list inst

val override : reg -> rval -> regmap -> regmap
let override r v rm =
    fun r' ->
        if r = r'
        then v
        else rm r'

val step : inst -> regmap -> regmap
let step i rm =
    match i with
    | Add r1 r2 r3 -> override r3 (rm r1 + rm r2) rm
    | Sub r1 r2 r3 -> override r3 (rm r1 - rm r2) rm
    | Mul r1 r2 r3 -> override r3 (rm r1 * rm r2) rm
    | Const v r    -> override r v rm

val run : prog -> regmap -> regmap
let run prog rm = List.Tot.fold_left (fun rm i -> step i rm) rm prog

(* Run in all zeros and get the 0th reg *)
val eval : prog -> rval
let eval p = let rm = run p (fun _ -> 0) in rm (R 0)

let equiv p1 p2 = eval p1 == eval p2

let mk42 : prog = [
    Const 1 (R 0);
    Add (R 0) (R 0) (R 1);
    Add (R 1) (R 1) (R 0);
    Add (R 0) (R 0) (R 1);
    Add (R 1) (R 1) (R 0);
    Add (R 0) (R 0) (R 1);
    Add (R 1) (R 0) (R 0);
    Const 6 (R 1);
    Sub (R 0) (R 1) (R 0);
]

let _ = assert_norm (eval mk42 == 42)

let add1 x y : prog = [
    Const x (R 0);
    Const y (R 1);
    Add (R 0) (R 1) (R 0);
]
    
let add2 x y : prog = [
    Const y (R 1);
    Const x (R 0);
    Add (R 0) (R 1) (R 0);
]
    
let add3 x y : prog = [
    Const x (R 0);
    Const y (R 1);
    Add (R 1) (R 0) (R 0);
]
    
let add4 x y : prog = [
    Const y (R 1);
    Const x (R 0);
    Add (R 1) (R 0) (R 0);
]

(* All of these identies are quite easy by normalization. Once we fix
 * #1482, they will not even require SMT. *)
let _ = assert_norm (forall x y. equiv (add1 x y) (add2 x y))
let _ = assert_norm (forall x y. equiv (add1 x y) (add3 x y))
let _ = assert_norm (forall x y. equiv (add1 x y) (add4 x y))
let _ = assert_norm (forall x y. equiv (add2 x y) (add3 x y))
let _ = assert_norm (forall x y. equiv (add2 x y) (add4 x y))
let _ = assert_norm (forall x y. equiv (add3 x y) (add4 x y))

(* Without normalizing, they require fuel, or else fail *)
#push-options "--max_fuel 0"
[@fail] let _ = assert (forall x y. equiv (add1 x y) (add2 x y))
[@fail] let _ = assert (forall x y. equiv (add1 x y) (add3 x y))
[@fail] let _ = assert (forall x y. equiv (add1 x y) (add4 x y))
[@fail] let _ = assert (forall x y. equiv (add2 x y) (add3 x y))
[@fail] let _ = assert (forall x y. equiv (add2 x y) (add4 x y))
[@fail] let _ = assert (forall x y. equiv (add3 x y) (add4 x y))
#pop-options

(* poly5 x = x^5 + x^4 + x^3 + x^2 + x^1 + 1 *)

let poly5 x : prog = [
    Const 1 (R 0);
    Const x (R 1);
    Mul (R 1) (R 1) (R 2);
    Mul (R 1) (R 2) (R 3);
    Mul (R 1) (R 3) (R 4);
    Mul (R 1) (R 4) (R 5);
    Add (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
    Add (R 0) (R 3) (R 0);
    Add (R 0) (R 4) (R 0);
    Add (R 0) (R 5) (R 0);
]

let _ = assert_norm (eval (poly5 1) == 6)
let _ = assert_norm (eval (poly5 2) == 63)
let _ = assert_norm (eval (poly5 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)

(* Bunch of fuel to even prove ground facts *)
#push-options "--max_fuel 12"
let _ = assert (eval (poly5 1) == 6)
let _ = assert (eval (poly5 2) == 63)
let _ = assert (eval (poly5 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
#pop-options

(* A different way of computing it *)
let poly5' x : prog = [
    Const 1 (R 0);
    Const x (R 1);
    Const 1 (R 2);
    Mul (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
    Mul (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
    Mul (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
    Mul (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
    Mul (R 0) (R 1) (R 0);
    Add (R 0) (R 2) (R 0);
]

(* Seems to do the same *)
let _ = assert_norm (eval (poly5' 1) == 6)
let _ = assert_norm (eval (poly5' 2) == 63)
let _ = assert_norm (eval (poly5' 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)

(* Same *)
#push-options "--max_fuel 14"
let _ = assert (eval (poly5' 1) == 6)
let _ = assert (eval (poly5' 2) == 63)
let _ = assert (eval (poly5' 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
#pop-options

[@fail]
let _ = assert (forall x. poly5 x `equiv` poly5' x)

let _ = assert_norm (forall x. poly5 x `equiv` poly5' x)
