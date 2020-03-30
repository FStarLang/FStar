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
module Bug175

type exp =
  | EApp : exp  -> exp -> exp

type heap = int -> Tot int

type config = heap * exp

noeq type step : config -> Type =
  | SApp1 : h:heap ->
            e1:exp ->
            e2:exp ->
            step (h, EApp e1 e2)
  | SApp2 : h:heap ->
            e1:exp ->
            e2:exp ->
            step (h, e2) ->
            step (h, EApp e1 e2)
