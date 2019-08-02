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
(* *****************************************************************************)
(* * Proving termination of its defunctionalized version is known to be hard ***)
(* *****************************************************************************)

(*  First standard try: to prove termination, I augment << with an
    ordering on call stacks **)
module CPS.DoubleDefun

open CPS.Expr

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
assume Rstack0: forall (e:expr) (l:list expr).{:pattern (Prims.precedes l (Cons e l))} l << e::l
assume Rstack1: forall (e1:expr) (e:expr) (l:list expr).{:pattern (Prims.precedes (Cons e1 l) (Cons e l))}
    e1 << e ==> (e1::l) << (e::l)
assume Rstack2: forall (e1:expr) (e2:expr) (e:expr) (l:list expr).{:pattern (Prims.precedes (Cons e1 (Cons e2 l)) (Cons e l))}
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

