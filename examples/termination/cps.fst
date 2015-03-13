(*
   Copyright 2014 Chantal Keller, Microsoft Research and Inria

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


(*************************************************************)
(*** A simple CPS function: adding the elements of a list. ***)
(*************************************************************)

(** Standard implementation **)
module SimpleCPS
open List

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (fun (r:int) -> k (hd + r))

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)



(** Second implementation with λ-lifting **)
module SimpleCPSLambdaLifting
open List

val add_cps_intern : (int -> Tot 'a) -> int -> int -> Tot 'a
let add_cps_intern k x y = k (x + y)

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (add_cps_intern k hd)

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)



(** It is easy to defunctionalize it **)
module SimpleCPSDefun
open List

type cont =
  | C0 : cont
  | C1 : cont -> int -> cont

val apply : cont -> int -> Tot int
let rec apply k r = match k with
  | C0 -> r
  | C1 k hd -> apply k (hd + r)

val add_cps : list int -> cont -> Tot int
let rec add_cps l k = match l with
  | [] -> apply k 0
  | hd::tl -> add_cps tl (C1 k hd)

val add : list int -> Tot int
let add l = add_cps l C0



(*******************************************************************)
(*** A more complex CPS function: adding the elements of a tree. ***)
(*******************************************************************)

(** Standard implementation **)
module DoubleCPS

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr

val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a
let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (fun r1 -> eval_cps e2 (fun r2 -> k (r1 + r2)))



(** With λ-lifting **)
module DoubleCPSLambdaLifting

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps : e:expr -> (int -> Tot 'a) -> Tot 'a (decreases %[e;0])
val eval_cps2 : e:expr -> (int -> Tot 'a) -> int -> Tot 'a (decreases %[e;1])

let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 e2 k)

and eval_cps2 e2 k r1 = eval_cps e2 (eval_cps1 k r1)


(** With greadier λ-lifting that removes mutual recursion **)
module DoubleCPSLambdaLifting2

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps2 : (int -> Tot 'a) -> ((int -> Tot 'a) -> Tot 'a) -> int -> Tot 'a
let eval_cps2 k eval_cps r1 = eval_cps (eval_cps1 k r1)

val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a
let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 k (eval_cps e2))

val eval : expr -> Tot int
let eval e = eval_cps e (fun x -> x)


(** We have to be careful when λ-lifting not to delay the strictly decreasing recursive call **)
(* module DoubleCPSLambdaLifting3 *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a *)
(* let eval_cps1 k r1 r2 = k (r1 + r2) *)

(* val eval_cps2 : (int -> Tot 'a) -> expr -> (expr -> (int -> Tot 'a) -> Tot 'a) -> int -> Tot 'a *)
(* let eval_cps2 k e2 eval_cps r1 = eval_cps e2 (eval_cps1 k r1) *)

(* val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a *)
(* let rec eval_cps e k = *)
(*   match e with *)
(*     | Const n -> k n *)
(*     | Plus e1 e2 -> eval_cps e1 (eval_cps2 k e2 eval_cps) *)

(* val eval : expr -> Tot int *)
(* let eval e = eval_cps e (fun x -> x) *)



(*******************************************************************************)
(*** Proving termination of its defunctionalized version is known to be hard ***)
(*******************************************************************************)

(** First standard try: to prove termination, I augment << with an
    ordering on call stacks **)
module DoubleCPSDefun

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr

type cont =
  | C0 : cont
  | C1 : cont -> int -> cont
  | C2 : cont -> expr -> cont

val stack : cont -> Tot (list expr)
let rec stack = function
  | C0 -> []
  | C1 k _ -> stack k
  | C2 k e -> e::(stack k)

(* Order on call stacks *)
assume Rstack0: forall (e:expr) (l:list expr). l << (e::l)
assume Rstack1: forall (e1:expr) (e:expr) (l:list expr).
    e1 << e ==> (e1::l) << (e::l)
assume Rstack2: forall (e1:expr) (e2:expr) (e:expr) (l:list expr).
    e1 << e ==> e2 << e ==> (e1::e2::l) << (e::l)

val apply : e:expr -> k:cont -> int -> Tot int (decreases %[e::(stack k);k;0])
val eval_cps : e:expr -> k:cont -> Tot int (decreases %[e::(stack k);k;1])

let rec apply e k r = match k with
    | C0 -> r
    | C1 k r1 -> apply e k (r1 + r)
    | C2 k e2 -> eval_cps e2 (C1 k r)

and eval_cps e k =
  match e with
    | Const n -> apply e k n
    | Plus e1 e2 -> eval_cps e1 (C2 k e2)

val eval : expr -> Tot int
let eval e = eval_cps e C0


(** Second try with λ-lifting: I would not expect F* to be able to infer termination anyway, but actually I get another strange error message **)
(* module DoubleCPSDefunLambdaLifting *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* type cont = *)
(*   | C0 : cont *)
(*   | C1 : cont -> int -> cont *)
(*   | C2 : cont -> expr -> cont *)

(* val apply : cont -> int -> (expr -> cont -> Tot int) -> Tot int *)
(* let rec apply k r eval_cps = match k with *)
(*     | C0 -> r *)
(*     | C1 k r1 -> apply k (r1 + r) eval_cps *)
(*     | C2 k e2 -> eval_cps e2 (C1 k r) *)

(* val eval_cps : expr -> cont -> Tot int *)
(* let rec eval_cps e k = *)
(*   match e with *)
(*     | Const n -> apply k n eval_cps *)
(*     | Plus e1 e2 -> eval_cps e1 (C2 k e2) *)
(* (\* *)
(*  Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error. *)
(* Bound term variable not found: _ *)
(* *\) *)
