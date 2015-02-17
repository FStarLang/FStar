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
  | TApp : typ -> typ -> typ
  | TArr : typ -> typ -> typ

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : typ -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_ELam

(* Substitution on expressions and types;
   they don't really interact in this calculus *)

type esub = var -> Tot exp

val esub_inc : var -> Tot exp
let esub_inc y = EVar (y+1)

val esubst : e:exp -> s:esub -> Tot exp
val esubst_lam : s:esub -> Tot esub
let rec esubst e s =
  match e with
  | EVar x -> s x
  | ELam t e1 -> ELam t (esubst e1 (esubst_lam s))
  | EApp e1 e2 -> EApp (esubst e1 s) (esubst e2 s)
and esubst_lam s =
  fun y -> if y = 0 then EVar y
           else esubst (s (y-1)) esub_inc

(* Substitution on types is very much analogous *)

type tsub = var -> Tot typ

val tsub_inc : var -> Tot typ
let tsub_inc y = TVar (y+1)

val tsubst : t:typ -> s:tsub -> Tot typ
val tsubst_lam : s:tsub -> Tot tsub
let rec tsubst t s =
  match t with
  | TVar x -> s x
  | TLam t t1 -> TLam t (tsubst t1 (tsubst_lam s))
  | TApp t1 t2 -> TApp (tsubst t1 s) (tsubst t2 s)
  | TArr t1 t2 -> TArr (tsubst t1 s) (tsubst t2 s)
and tsubst_lam s =
  fun y -> if y = 0 then TVar y
           else tsubst (s (y-1)) tsub_inc
