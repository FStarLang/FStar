module Bug4558

open FStar.UInt

(* A lemma whose body ends in [assert p] is checked by relating
   [squash p <: squash post].  The attempt to unify the two propositions
   used to fully normalize [logand ...] and [dec (enc p)] to compare them,
   which unfolds [to_vec]/[from_vec] on a symbolic 64-bit argument and takes
   time exponential in the width. *)

type pair = p: (uint_t 64 & uint_t 64) { let (a, b) = p in a < 16 /\ b < 16 }

let enc (p: pair) : uint_t 64 =
  let (a, b) = p in
  logor a (shift_left b 4)

let dec (op: uint_t 64) : uint_t 64 & uint_t 64 =
  (logand op (to_uint_t 64 0xF), logand (shift_right op 4) (to_uint_t 64 0xF))

let roundtrip_ok (p: pair) : Lemma (ensures dec (enc p) == p) =
  let (a, b) = p in
  admit ();
  assert (logand (shift_right (enc p) 4) (to_uint_t 64 0xF) == b);
  ()

let roundtrip_final_assert (p: pair) : Lemma (ensures dec (enc p) == p) =
  let (a, b) = p in
  admit ();
  assert (logand (shift_right (enc p) 4) (to_uint_t 64 0xF) == b)
