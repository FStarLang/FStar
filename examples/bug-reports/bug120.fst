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
module Bug120

type var = nat

type exp =
  | EVar : var -> exp
  | EAbs : exp -> exp

type sub = var -> Tot exp

(* CH: How on earth can F* show this terminating with this decreases clause? *)
val subst : e:exp -> sub -> Tot exp (decreases e)
let rec subst e s =
  match e with
  | EVar x -> s x
  | EAbs e1 -> EAbs (subst e1 (fun y -> if y = 0 then EVar y
                                 else subst (s (y-1)) (fun y' -> EVar (y'+1))))
