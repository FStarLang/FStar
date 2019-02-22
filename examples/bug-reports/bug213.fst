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
module Bug213

type intPair =
  | IP : f:int -> intPair

noeq type cexists (a:Type) (p:a -> Type) : Type =
  | ExIntro : x:a -> p x -> cexists a p

val foo : cexists intPair (fun (p:intPair) -> unit) -> Tot unit
let foo h =
  let ExIntro (IP p) hp = h in
  ()


noeq type cexists' : (a:Type) -> (p:a -> Type) -> Type =
  | ExIntro' : #a:Type -> #p:(a -> Type) -> x:a -> p x -> cexists' a p
val foo' : cexists' intPair (fun (p:intPair) -> unit) -> Tot unit
[@expect_failure 114]
let foo' h =
  let ExIntro' (IP p) hp = h in
  ()
