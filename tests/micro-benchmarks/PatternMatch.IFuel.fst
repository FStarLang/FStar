(*
   Copyright 2008-2020 Microsoft Research

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
module PatternMatch.IFuel

assume val n : int

type proof (m:int) =
  | Proof    : squash (m == n) -> proof m

type m_and_proof =
  | C : m:int -> p:proof m -> m_and_proof

(*
 * The following proof fails with ifuel 0
 *
 * The VC that is generated for it is:
 *   forall (x:m_and_proof). x == C m (Proof ()) ==> m == n
 *
 * Without any ifuel, Z3 cannot do a type inversion on (C m (Proof ()):m_and_proof) to proceed
 *)
#push-options "--ifuel 0"
[@@ expect_failure [19]]
let test1 (x:m_and_proof) =
  match x with
  | C m (Proof ()) -> assert (m == n)
#pop-options


(*
 * It needs two units of ifuel, one for inverting C and the other for inverting Proof
 *)
#push-options "--ifuel 2"
let test2 (x:m_and_proof) =
  match x with
  | C m (Proof ()) -> assert (m == n)
#pop-options

#restart-solver

(*
 * On the other hand, if we bind the pattern variables,
 *   the proof works with ifuel 1
 *
 * Since now the query becomes,
 *   forall (x:_) (m:int) (p:proof m).
            (x == C m p /\ p == Proof ()) ==> m == n
 *
 * With ifuel 1, Z3 can invert (Proof ():proof m), and done
 *)

#push-options "--ifuel 1"
let test3 (x:m_and_proof) =
  match x with
  | C m p ->
    match p with
    | Proof () -> assert (m == n)
#pop-options
