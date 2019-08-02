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
module Gcd
open FStar.List
open FStar.Constructive
open FStar.Mul

//TODO: THESE ARE DODGY; consider using FStar.Squash instead
assume val intuitionistic_of_smt : #a:Type0 -> u:unit{a} -> Tot a
assume val smt_of_intuitionistic : #a:Type0 -> a -> Lemma a

type divides (a:pos) (b:pos) = cexists (fun (c:pos) -> a * c == b)

type is_gcd (a:pos) (b:pos) (gcd:pos) =
    (forall (d:pos). divides d a /\ divides d b ==> divides d gcd) 
    /\ divides gcd a 
    /\ divides gcd b

val times_one : a:pos -> Lemma (a * 1 = a)
let times_one a = ()

val a_divides_a' : a:pos -> Tot (divides a a)
//#set-options "--debug Gcd --debug_level Extreme --debug_level Rel --debug_level RelCheck"
let a_divides_a' a = ExIntro 1 (intuitionistic_of_smt (times_one a))

val a_divides_a : a:pos -> Lemma (divides a a)
let a_divides_a a = smt_of_intuitionistic (a_divides_a' a) //don't see why it doesn't work to unfold the definition of a_divides_a'

val gcd_triv : a:pos -> Lemma (is_gcd a a a)
let gcd_triv a = a_divides_a a
