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
module ElGamal

open FStar.DM4F.Heap.Random
open FStar.DM4F.Random


type group = int

//assume type group : eqtype

assume val g: group

assume val (^): group -> int -> group

assume val ( * ): group -> group -> group

assume val log: group -> elem

assume val pow_log: a:group -> Lemma (g^(log a) == a)

assume val mul_pow: x:elem -> y:elem -> Lemma ((g^x) * (g^y) == g^((x + y) % q))


assume val mod_plus_minus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a + b) % q - b) % q == a))
  [SMTPat (((a + b) % q - b) % q)]

assume val mod_minus_plus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a - b) % q + b) % q == a))
  [SMTPat (((a - b) % q + b) % q)]

let bij' (m:group) =
  let f    = fun h -> upd h (to_id 0) ((sel h (to_id 0) - log m) % q) in
  let finv = fun h -> upd h (to_id 0) ((sel h (to_id 0) + log m) % q) in
  Bijection f finv


reifiable val elgamal: m:group -> Rand group
let elgamal (m:group)  =
  let z = sample () in
  g^z

reifiable val elgamal': m:group -> Rand group
let elgamal' (m:group) =
  let z = sample () in
  (g^z) * m


val elgamal_prop: m:group -> z:elem -> Lemma
  (requires True)
  (ensures (g^((z - log m) %q)) * m == g^z)
  [SMTPat ((g^(z - log m) % q) * m) ]
let elgamal_prop m z =
  pow_log m;
  mul_pow ((z - log m) % q) (log m);
  mod_minus_plus z (log m)

(*
g^((z - log m) % q) * m
== [pow_log m]
g^((z - log m) % q) * g^(log m)
== [mul_pow ((z - log m) % q) (log m)]
g^(((z - log m) % q + log m) % Q)
== [mod_minus_plus z (log m)]
g^z
*)


val elgamal_equiv: m:group -> c:group -> Lemma
  (let f1 h = reify (elgamal m) h in
   let f2 h = reify (elgamal' m) h in
   mass f1 (point c) == mass f2 (point c))
let elgamal_equiv m c =
  let f1 h = reify (elgamal  m) h in
  let f2 h = reify (elgamal' m) h in
  pr_eq f1 f2 (point c) (point c) (bij' m)
