module OTP

open FStar.DM4F.Heap.Random
open FStar.DM4F.Random

open FStar.Mul

assume val mod_plus_minus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a + b) % q - b) % q == a))
  [SMTPat (((a + b) % q - b) % q)]

assume val mod_minus_plus: a:elem -> b:elem -> Lemma
  (requires True)
  (ensures  (((a - b) % q + b) % q == a))
  [SMTPat (((a - b) % q + b) % q)]

let bij (n:elem) =
  let f    = fun h -> upd h (to_id 0) ((sel h (to_id 0) + n) % q) in
  let finv = fun h -> upd h (to_id 0) ((sel h (to_id 0) - n) % q) in
  Bijection f finv


reifiable val otp: elem -> Rand elem
let otp n =
  let m = sample () in
  (n + m) % q


assume val mod_prop: n1:elem -> n2:elem -> m:elem -> Lemma
  (requires True)
  (ensures ((n1 + m) % q == (n2 + (m + (n1 - n2) % q) % q) % q))
  [SMTPat (n2 + (m + (n1 - n2) % q) % q)]

(** The output of (otp n) is independent of n, i.e.
    forall n1 n2. Pr[otp n1 = z] == Pr[otp n2 = z] *)
val otp_secure: n1:elem -> n2:elem -> z:elem -> Lemma
  (let f1 h = reify (otp n1) h in
   let f2 h = reify (otp n2) h in
   mass f1 (point z) == mass f2 (point z))
let otp_secure n1 n2 z =
  let f1 h = reify (otp n1) h in
  let f2 h = reify (otp n2) h in
  pr_eq f1 f2 (point z) (point z) (bij ((n1 - n2) % q))
