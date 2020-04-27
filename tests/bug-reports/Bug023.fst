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
module Bug023

type ty = a:Type{hasEq a}
type env = int -> Tot (option ty)
val extend : env -> int -> ty -> Tot env
let extend g x t = fun x' -> if x = x' then Some t else g x'

val extend_eq : g:env -> x:int -> a:ty -> Lemma
      (ensures ((extend g x a) x) = Some a)
let extend_eq g x a = ()
