(*
   Copyright 2008-2015 Catalin Hritcu, Nikhil Swamy, Microsoft Research and Inria

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

module LambdaOmega

(* Chapter 29 of TAPL: "Type Operators and Kinding" *)

type var = nat

type knd =
  | KTyp
  | KArr : knd -> knd

type typ =
  | TVar : var -> typ
  | TLam : knd -> typ -> typ 
  | TApp : typ -> typ
  | TArr : typ -> typ -> typ

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : typ -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_EAbs

(* Substitution *)

type sub =
  | ESub : var -> Tot exp
  | TSub : var -> Tot typ

val subst_in_exp : e:exp -> s:sub -> Tot exp (decreases e)
val subst_eabs : s:sub -> Tot sub
let rec subst_in_exp e s =
  match e with
  | EVar x -> s x
  | EAbs t e1 -> EAbs t (subst_in_exp e1 (subst_eabs s))
  | EApp e1 e2 -> EApp (subst_in_exp e1 s) (subst_in_exp e2 s)
and subst_eabs s =
  fun y -> if y = 0 then EVar y
           else subst_in_exp (s (y-1)) sub_inc
