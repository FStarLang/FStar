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
module Bug184b

type exp =
  | EVar   : int -> exp
  | EApp   : exp -> exp -> exp
  | ELam   : exp -> exp

type step : exp -> exp -> Type =
  | SApp1 : #e1:exp ->
            e2:exp ->
            #e1':exp ->
            step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)
  | SApp2 : e1:exp ->
            #e2:exp ->
            #e2':exp ->
            step e2 e2' ->
            step (EApp e1 e2) (EApp e1 e2')


type relation (a:Type) = a -> a -> Type
type multi (a:Type) (r:relation a) : a -> a -> Type =
  | Multi_refl : x:a -> multi a r x x
  | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z
type steps : exp -> exp -> Type = multi exp step

val steps_preserves_red2 : e:exp -> e':exp -> b: steps e e' -> Tot unit
let rec steps_preserves_red2 e e' st_e_e' =
  match st_e_e' with
  | Multi_refl _ -> ()
  | Multi_step _ _ _ _ _ -> ()
