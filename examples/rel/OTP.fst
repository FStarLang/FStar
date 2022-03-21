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
module OTP

open FStar.DM4F.OTP.Heap
open FStar.DM4F.OTP.Random
open FStar.BitVector

let ( ^^ ) #n = logxor_vec #n

let xor_idempotent (x y:elem)
  : Lemma
    (ensures  ((x ^^ y) ^^ y == x))
    [SMTPat ((x ^^ y) ^^ y)]
  = Seq.lemma_eq_intro ((x ^^ y) ^^ y) x

let bij (n:elem) =
  let f    = fun h -> upd h (to_id 0) ((sel h (to_id 0) ^^ n)) in
  let finv = fun h -> upd h (to_id 0) ((sel h (to_id 0) ^^ n)) in
  Bijection f finv

let otp (n:elem) : Rand elem =
  let m = sample () in
  n ^^ m

let xor_prop (n1 n2 m:elem)
  : Lemma
    (ensures (n1 ^^ m == (n2 ^^ (m ^^ (n1 ^^ n2)))))
    [SMTPat (n2 ^^ (m ^^ (n1 ^^ n2)))]
  = Seq.lemma_eq_intro (n1 ^^ m) (n2 ^^ (m ^^ (n1 ^^ n2)))

(** The output of (otp n) is independent of n, i.e.
    forall n1 n2. Pr[otp n1 = z] == Pr[otp n2 = z] *)
let otp_secure (n1 n2 z:elem)
  : Lemma
    (ensures
      (let f1 h = reify (otp n1) h in
       let f2 h = reify (otp n2) h in
       mass f1 (point z) == mass f2 (point z)))
  = let f1 h = reify (otp n1) h in
    let f2 h = reify (otp n2) h in
    pr_eq f1 f2 (point z) (point z) (bij ((n1 ^^ n2)))
