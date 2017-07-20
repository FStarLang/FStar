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


(* ***********************************************************)
(* * A simple CPS function: adding the elements of a list. ***)
(* ***********************************************************)

(*  Standard implementation **)
module CPS.Simple
open FStar.List.Tot

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (fun (r:int) -> k (hd + r))

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)





(*  We have to be careful when λ-lifting not to delay the strictly decreasing recursive call **)
(* module DoubleCPSLambdaLifting3 *)

(* open Expr *)

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




(*  Second try with λ-lifting: I would not expect F* to be able to infer termination anyway, but actually I get another strange error message **)
(* module DoubleCPSDefunLambdaLifting *)

(* open Expr *)

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




(*  Trying to go further by putting the ghost expression into the environment: F* raises two strange errors **)
(* module DoubleCPSCCEnv *)

(* open Expr *)

(* type closure = *)
(*   | Clos : env:Type -> env -> (env -> int -> Tot int) -> closure *)

(* val apply : closure -> int -> Tot int *)
(* let apply c n = *)
(*   match c with *)
(*     | Clos e k -> k e n *)

(* val clos2 : (closure * int) -> int -> Tot int *)
(* let clos2 (k,n) m = apply k (n + m) *)

(* val eval : e:expr -> closure -> Tot int (decreases %[e;1]) *)
(* val clos1 : p:((|e:expr * (a:expr{a << e})|) * closure) -> int -> Tot int (decreases %[dfst (fst p);0]) *)
(* let rec eval e k = *)
(*   match e with *)
(*     | Const n -> apply k n *)
(*     | Plus t u -> eval t (Clos #((|e:expr * (a:expr{a << e})|) * closure) ((|e,u|),k) clos1) *)

(* and clos1 ((|e,u|),k) n = eval u (Clos #(closure * int) (k,n) clos2) *)
