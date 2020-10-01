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
module NTP

assume val foo : x : int{x > 0} -> Tot bool

val u : x:int{x>0}
let u =
  match 42 with
  | x when foo x -> 45

(*
Term has an unexpected non-trivial pre-condition:
[Before:((fun a:Type wp:(_:(_:a => Type) => Type) => (wp (fun x:a => True))) bool (fun p:(_:bool => Type) => (l_and (Meta (labeled "This term may not terminate (non-trivial-precondition.fst(8,15-8,16))") (l_and (Meta (labeled "Subtyping check failed; expected type [Before:x:int{(b2t (op_GreaterThan x 0))}][After:x:int{(b2t (op_GreaterThan x 0))}]; got type [Before:int][After:int] (non-trivial-precondition.fst(8,15-8,16))") (b2t (op_GreaterThan x 0))) True)) (Forall #bool (fun x:bool => (p x))))))]
[After:(b2t (op_GreaterThan x 0)) /\ True /\ (forall x:bool. True)]
*)
