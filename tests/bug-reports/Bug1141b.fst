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
module Bug1141b

effect MyTot (a:Type) = PURE a (fun p -> forall x. p x)

[@expect_failure]
noeq
type np (a : Type) = | Mk : (np a -> MyTot a) -> np a

(* This is how to prove false out of that type, were it to succeed *)
(*
let self #a (v : np a) : a =
    match v with
    | Mk f -> f v

let loop #a (f : a -> a) : a =
    self (Mk (fun x -> f (self x)))

val falso : squash False
let falso = loop (fun x -> x)
*)
