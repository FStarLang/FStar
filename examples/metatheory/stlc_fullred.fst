(*
   Copyright 2008-2014 Catalin Hritcu, Nikhil Swamy, Microsoft Research and Inria

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

module StlcFullRed

open StlcConstrDeBruijnParallelSub

type rstep : exp -> exp -> Type =
  | SBeta : t:ty ->
            e1:exp ->
            e2:exp ->
            rstep (EApp (EAbs t e1) e2) (subst_beta e2 e1)
  | SApp1 : #e1:exp ->
            e2:exp ->
            #e1':exp ->
            rstep e1 e1' ->
            rstep (EApp e1 e2) (EApp e1' e2)
  | SApp2 : e1:exp ->
            #e2:exp ->
            #e2':exp ->
            rstep e2 e2' ->
            rstep (EApp e1 e2) (EApp e1 e2')

(* Defining my own constructive existential *)
type ex : #a:Type -> (a -> Type) -> Type =
  | ExIntro : #a:Type -> #p:(a -> Type) -> x:a -> p x -> ex p

val progress : #e:exp{not (is_value e)} -> #t:ty -> h:rtyping empty e t ->
               Tot (ex (fun e' -> rstep e e')) (decreases h)
let rec progress _ _ h =
  match h with
  | TyApp #g #e1 #e2 #t11 #t12 h1 h2 ->
     match e1 with
     | EAbs t e1' -> ExIntro (subst_beta e2 e1') (SBeta t e1' e2)
     | _          -> (match progress h1 with
                      | ExIntro e1' h1' -> ExIntro (EApp e1' e2) (SApp1 e2 h1'))
