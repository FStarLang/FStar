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
module Problem02While

(*We were not able to make F* prove simple properties about GCD, so we were stuck …*)
type divides (a:pos) (b:pos) = (exists (c:pos). a*c = b)
type is_pgcd (a:pos) (b:pos) (pgcd:pos) =
((forall (d:pos). (divides d a /\ divides d b) 
==> divides d pgcd) /\ divides pgcd a /\ divides pgcd b)

val pgcd_triv : a:pos -> Lemma (is_pgcd a a a)
let pgcd_triv a = ()
assume val pgcd_non_triv : a:pos -> b : pos{a>b} -> x : pos -> Lemma(is_pgcd (a-b) b x ==> is_pgcd a b x) 
(*let pgcd_non_triv a b x = ()*)
val algo_pgcd : n:nat 
             -> choose : (nat -> Tot bool) 
             -> a:pos 
             -> b:pos 
             -> Tot (option pos)
let rec algo_pgcd n choose a b =
if n = 0 then None
else (if (a <> b) then  
(if choose n then (if a > b then let a = a-b in algo_pgcd (n-1) choose a b else algo_pgcd (n-1) choose a b)
else (if b > a then let b = b - a in algo_pgcd (n-1) choose a b else algo_pgcd (n-1) choose a b))
else Some a) 
(*Missing property about gcd …*)
val algo_pgcd_propr : n:nat -> choose : (nat -> Tot bool) -> a:pos -> b:pos -> x:pos -> Lemma (algo_pgcd n choose a b = Some x <==> is_pgcd a b x) (decreases n)
let rec algo_pgcd_propr n choose a b x =
admit()
(*
if n = 0 then ()
else (if (a <> b) then  
(if choose n then (if a > b then let a' = a-b in (algo_pgcd_propr (n-1) choose a' b x; pgcd_non_triv a b x) else algo_pgcd_propr (n-1) choose a b x)
else (if b > a then let b' = b - a in (algo_pgcd_propr (n-1) choose a b' x; pgcd_non_triv b a x) else algo_pgcd_propr (n-1) choose a b x))
else pgcd_triv a) 
*)
