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
module PositiveRelaxed

type nat =
  | O : nat
  | S : pre:nat -> nat

(* First, this inductive shouldn't be accepted by the _current_ check *)
(* Second, this inductive shouldn't be accepted by _any_ check *)
type p : nat -> Type =
  | PSO : f:(p O -> Tot (p (S O))) -> p (S O)
  | POd : h:(p (S O)) -> p O

val bad : p (S O) -> Tot (p (S O))
let bad h = (PSO.f h) (POd h)

val loop : p (S O)
let loop = bad (PSO (fun h -> bad (POd.h h)))

(* looooop ....

   bad (PSO (bad (POd.h h))) ->                               (unfold+project)
   (fun h -> POd.h h) (POd (PSO (fun h -> POd.h h))) ->       (beta+project)
   bad (PSO (bad (POd.h h)))

 *)
