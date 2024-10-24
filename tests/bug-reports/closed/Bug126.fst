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
module Bug126

type typ  = | TUnit : typ | TArr: arg:typ -> res:typ -> typ
type var = nat
type exp =
  | EUnit  : exp
  | EVar   : x:var -> exp
  | EApp   : e1:exp -> e2:exp -> exp
  | ELam   : t:typ -> body:exp -> exp

type env = var -> Tot (option typ)
val extend: env -> typ -> Tot env
let extend g t y = if y=0 then Some t else g (y - 1)
noeq type typing : env -> exp -> typ -> Type =
  | TyUn  : #g:env -> typing g EUnit TUnit

  | TyVar : #g:env -> x:var{Some? (g x)} ->
            typing g (EVar x) (Some?.v (g x))
  | TyLam : #g:env -> t:typ -> #e1:exp -> #t':typ ->
            typing (extend g t) e1 t' ->
            typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env -> #e1:exp -> #e2:exp -> #t11:typ -> #t12:typ ->
            typing g e1 (TArr t11 t12) ->
            typing g e2 t11 ->
            typing g (EApp e1 e2) t12

let emp x = None
let value = function ELam _ _ | EVar _ | EUnit -> true | _ -> false
val invert_lam: e:exp{value e} -> t:typ{TArr? t} -> d:typing emp e t
             -> Tot (typing (extend emp (TArr?.arg t)) (ELam?.body e) (TArr?.res t))
let invert_lam e t (TyLam _ premise) = premise
