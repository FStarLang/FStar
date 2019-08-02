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
module Bug116

type env = int -> Tot bool

assume val extend : env -> int -> Tot env

noeq type rtyping : env -> int -> Type =
  | TyAbs : #g:env ->
            x:int ->
            #e1:int ->
            rtyping (extend g x) e1 ->
            rtyping g 42

val free_in_context : e:int -> g:env -> h:rtyping g e -> Tot unit
let rec free_in_context _ _ h =
  match h with
  | TyAbs _ h1 -> ()
