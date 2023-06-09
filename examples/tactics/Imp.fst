(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Imp

//#set-options "--debug Imp --debug_level SMTQuery"

open FStar.Mul
open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring
open FStar.Algebra.CommMonoid

type rval = int
type reg = | R of n:nat{n < 10}
type regmap = reg -> rval

noeq
type inst =
    | Add : reg -> reg -> reg -> inst
    | Sub : reg -> reg -> reg -> inst
    | Mul : reg -> reg -> reg -> inst
    | Const : rval -> reg -> inst
    //| If0 : reg -> prog -> prog -> inst
    //| Seq : prog -> inst
and prog = list inst

module L = FStar.List.Tot

let rec size : inst -> pos = function
  | Add _ _ _
  | Sub _ _ _
  | Mul _ _ _
  | Const _ _  -> 1
  //| If0 _ i j -> 1 + size_l i + size_l j
  //| Seq i -> 1 + size_l i

and size_l : prog -> pos = function
  | [] -> 1
  | hd::tl -> size hd + size_l tl
val override : reg -> rval -> regmap -> regmap
let override r v rm =
    fun r' ->
        if r = r'
        then v
        else rm r'

let rec eval' (i:inst) (rm:regmap)
    : Tot regmap (decreases (size i))
    = match i with
      | Add r1 r2 r3 -> override r3 (rm r1 + rm r2) rm
      | Sub r1 r2 r3 -> override r3 (rm r1 - rm r2) rm
      | Mul r1 r2 r3 -> override r3 (rm r1 * rm r2) rm
      | Const v r    -> override r v rm
      //| Seq []       -> rm
//      | Seq (p::ps)   -> eval' (Seq ps) (eval' p rm)
//      | If0 r p0 p1  ->
//          if rm r = 0 
//          then eval' (Seq p0) rm
//          else eval' (Seq p1) rm

(* Run in all zeros and get the 0th reg *)
val eval : prog -> rval
//let eval p = let rm = eval' (Seq p) (fun _ -> 0) in rm (R 0)
let eval p = let rm = List.Tot.fold_left (fun r i -> eval' i r) (fun _ -> 0) p in rm (R 0)

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

(* All of these identities are quite easy by normalization. Once we fix
 * #1482, they will not even require SMT. *)
let _ = assert_norm (forall x y. equiv (add1 x y) (add2 x y))
let _ = assert_norm (forall x y. equiv (add1 x y) (add3 x y))
let _ = assert_norm (forall x y. equiv (add1 x y) (add4 x y))
let _ = assert_norm (forall x y. equiv (add2 x y) (add3 x y))
let _ = assert_norm (forall x y. equiv (add2 x y) (add4 x y))
let _ = assert_norm (forall x y. equiv (add3 x y) (add4 x y))

(* Without normalizing, they require fuel, or else fail *)
#push-options "--max_fuel 0"
[@@expect_failure] let _ = assert (forall x y. equiv (add1 x y) (add2 x y))
[@@expect_failure] let _ = assert (forall x y. equiv (add1 x y) (add3 x y))
[@@expect_failure] let _ = assert (forall x y. equiv (add1 x y) (add4 x y))
[@@expect_failure] let _ = assert (forall x y. equiv (add2 x y) (add3 x y))
[@@expect_failure] let _ = assert (forall x y. equiv (add2 x y) (add4 x y))
[@@expect_failure] let _ = assert (forall x y. equiv (add3 x y) (add4 x y))
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
//#push-options "--max_fuel 12"
//let _ = assert (eval (poly5 1) == 6)
//let _ = assert (eval (poly5 2) == 63)
//let _ = assert (eval (poly5 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
//#pop-options

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
#push-options "--max_fuel 20"
//let _ = assert (eval (poly5' 1) == 6)
//let _ = assert (eval (poly5' 2) == 63)
//let _ = assert (eval (poly5' 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
//let _ = assert (forall x. poly5 x `equiv` poly5' x)
#pop-options

//[@@Pervasives.'expect_failure']
//let _ = assert (forall x. poly5 x `equiv` poly5' x)
//
//#set-options "--z3rlimit 10"
//let _ = assert_norm (forall x. (poly5 (eval (poly5 x)) `equiv` poly5' (eval (poly5' x))))

#set-options "--max_fuel 0"
// --tactic_trace"
let _ = assert (forall x. poly5 x `equiv` poly5' x)
            by (let _ = forall_intros () in
                compute ();
                (* dump "after norm"; *)
                canon_semiring int_cr;
                (* dump "final"; *)
                ())

// Takes long.. try again later
//let _ = assert (forall x. (poly5 (eval (poly5 x)) `equiv` poly5' (eval (poly5' x))))
//          by (let _ = forall_intros () in
//           compute ();
//           dump "after norm";
//           canon_semiring int_cr;
//           dump "final")
//    
