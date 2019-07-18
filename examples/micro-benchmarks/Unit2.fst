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
module Unit2

(* Proving alpha equivalence in the solver *)
let test1 _ = assert ((fun (x:int) -> x) == (fun y -> y))
assume type vector : Type0 -> nat -> Type0
let test2 _ = assert ((a:Type -> x:nat -> Tot (vector a x)) ==
                      (b:Type -> y:nat -> Tot (vector b y)))
let test3 _ = assert (nat == y:int{y>=0})

type zat = x:int{x >= 0}
type geq (z:int) = x:int{x >= z}
(* let test4 _ = assert (nat == geq 0) *)

let test5 _ = assert (nat == zat)

//SMT encoding does not encode delta equivalence
//It used to work accidentally for types that are equivalent
//for the unfolding of nullary constants
//But, not anymore, since the fix to bug #1750
//Instead of SMT, this fact can be proven by normalization
[@(expect_failure [19])]
let test6 _ = assert ((a:Type -> x:nat -> Tot (vector a x)) ==
                      (b:Type -> y:zat -> Tot (vector b y)))

let test7 _ = assert_norm ((a:Type -> x:nat -> Tot (vector a x)) ==
                          (b:Type -> y:zat -> Tot (vector b y)))

(* let test7 _ = assert ((a:Type -> x:nat -> Tot (vector a x)) == *)
(*                       (b:Type -> y:int{y>=0} -> Tot (vector b y))) *)


(* GADTs *)
type t : Type -> Type =
  | Int : i:int -> t int
  | Bool : b:bool -> t bool

let f (a:Type) (x:t a) : a =
  match x with
  | Int i -> i + 1
  | Bool b -> not b


(* Strategies: *)

(*   0. --rel1, the current default of F* *)
(*      Bidirectional type inference/checking *)
(*      Given a subtyping constraints ?u <: t, or t <: ?u, it solves this as ?u=t, eagerly! *)


(*   1. --rel2, as currently implemented in F* *)

(*      Infers subtyping constraints t <:n t', where n=0 for each *)
(*      constraint produced directly from the program *)

(*      As constraints decompose, e.g, t1 -> t1' <:n t2 -> t2',  *)
(*      produces t2 <:n+1 t1 and and t1' <:n+t t2' *)

(*      It delays the solving of ?u <:n t and t <:n ?u *)

(*      Then, solves ?u <:0 x:t{phi} as  ?u = t  /\ fun x -> phi *)
(*      for ?u <:n+1 t, solves it as ?u=t *)

(*   2. Slack variable idea *)

(*      Infers subtyping constraints t < t' *)
(*      It delays the solving of ?u < t and t <: ?u *)

(*      Then, solves ?u <: x:t{phi} as  ?u = x:t{phi /\ ?slack x} *)
(*                   x:t{phi} <: ?u as  ?u = x:t{phi \/ ?slack x} *)

(*   3. Flow-sensitive idea   (ideal) *)

(*      Infers subtyping constraints Psi |- t <: t', where Psi is the  *)
(*      It delays the solving of ?u < t and t <: ?u *)

(*      Then, solves ?u <: x:t{phi} as  ?u = x:t{phi /\ ?slack x} *)
(*                   x:t{phi} <: ?u as  ?u = x:t{phi \/ ?slack x} *)


(* Some simple tests that require --rel2 to succeed; to be expanded *)
let f1 (l:list nat) = 0::l    //succeeds with both 1 and 2
let f2 (x:nat) (y:int) = x=y
let f3 : list nat =
  let y = [0;1] in
  y

assume val f4 : nat -> Tot bool
let eta_f4 x = f4 x //fails under 1; succeeds under 2

assume val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let eta_f4' = map (fun n -> f4 n) [2] //needs n:nat under strategy 1; works as is under 2

(*
   under strategy 1, infers x:int -> Tot bool
   under strategy 2, infers x:nat -> Tot bool
 *)
let test x = if x >= 0 then f4 x else false
(* let test2 (x:int) = test x //succeeds only using 1 (and 3), not 2. *)

(* type pos = x:int{x>0} *)
(* let f5 g (l:list pos) (m:list nat) = let _ = map g l in map g m *)


(* assume val f: (int -> ML (int -> int)) -> int *)
(* assume val g: (int -> int -> int) -> int *)
(* let brittle_1 x = f x + g x //this program checks under rel1 *)
(* let brittle_2 x = g x + f x //but this program fails under rel1 *)
