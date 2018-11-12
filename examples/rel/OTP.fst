module OTP

open FStar.DM4F.OTP.Heap
open FStar.DM4F.OTP.Random

open FStar.BitVector

let op_Hat_Hat #n = logxor_vec #n

val xor_idempotent: x:elem -> y:elem -> Lemma
  (requires True)
  (ensures  ((x ^^ y) ^^ y == x))
  [SMTPat ((x ^^ y) ^^ y)]
let xor_idempotent x y =
  Seq.lemma_eq_intro ((x ^^ y) ^^ y) x

let bij (n:elem) =
  let f    = fun h -> upd h (to_id 0) ((sel h (to_id 0) ^^ n)) in
  let finv = fun h -> upd h (to_id 0) ((sel h (to_id 0) ^^ n)) in
  Bijection f finv

reifiable val otp: elem -> Rand elem
let otp n =
  let m = sample () in
  n ^^ m

val xor_prop: n1:elem -> n2:elem -> m:elem -> Lemma
  (requires True)
  (ensures (n1 ^^ m == (n2 ^^ (m ^^ (n1 ^^ n2)))))
  [SMTPat (n2 ^^ (m ^^ (n1 ^^ n2)))]
let xor_prop n1 n2 m =
  Seq.lemma_eq_intro (n1 ^^ m) (n2 ^^ (m ^^ (n1 ^^ n2)))

(** The output of (otp n) is independent of n, i.e.
    forall n1 n2. Pr[otp n1 = z] == Pr[otp n2 = z] *)
val otp_secure: n1:elem -> n2:elem -> z:elem -> Lemma
  (let f1 h = reify (otp n1) h in
   let f2 h = reify (otp n2) h in
   mass f1 (point z) == mass f2 (point z))
let otp_secure n1 n2 z =
  let f1 h = reify (otp n1) h in
  let f2 h = reify (otp n2) h in
  pr_eq f1 f2 (point z) (point z) (bij ((n1 ^^ n2)))

let one_time_pad () : Rand ((elem -> elem) * (elem -> elem)) =
  let key = sample () in
  let encrypt (msg:elem) = msg ^^ key in
  let decrypt (cipher:elem) = cipher ^^ key in
  encrypt, decrypt

(*
 * AR: 03/07/18: this relies on abstraction leaks in FStar.DM4F.OTP.Heap
 *               admitting, see the changes in that file alongside this commit
 *)		 
// let one_time_pad_ok x0 x1 t0 t1 : Lemma
//   (requires (t1 == (bij (x1 ^^ x0)).f t0))
//   (ensures (let (Some (enc0, dec0),_) = reify (one_time_pad ()) (to_id 0, t0) in
//             let (Some (enc1, dec1),_) = reify (one_time_pad ()) (to_id 0, t1) in
//             dec0 (enc0 x0) == x0 /\
//             dec1 (enc1 x1) == x1 /\
//             enc0 x0 == enc1 x1))
//    = let (Some (enc0, dec0),_) = reify (one_time_pad ()) (to_id 0, t0) in
//      let (Some (enc1, dec1),_) = reify (one_time_pad ()) (to_id 0, t1) in
//      assert (enc0 x0 == x0 ^^ (index t0 (to_id 0)));
//      assert (enc1 x1 == x1 ^^ (index t1 (to_id 0)))
