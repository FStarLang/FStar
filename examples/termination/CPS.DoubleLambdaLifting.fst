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
(** With λ-lifting **)
module CPS.DoubleLambdaLifting
open CPS.Expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps : e:expr -> (int -> Tot 'a) -> Tot 'a (decreases %[e;0])
val eval_cps2 : e:expr -> (int -> Tot 'a) -> int -> Tot 'a (decreases %[e;1])

let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 e2 k)

and eval_cps2 e2 k r1 = eval_cps e2 (eval_cps1 k r1)
