module BVExtend

open FStar.UInt
open FStar.BV
open FStar.Math.Lemmas

(* This proof about bitvector extension was very difficult on Z3 4.8.5,
   but works very reliably in 4.13.3. *)

// Needed due to #3903
let _ : bv_t 32 = bv_zero
let _ : bv_t 64 = bv_zero
let _ : bv_t 128 = bv_zero

(* This should go to FStar.UInt, maybe? *)
let upcast (x : nat) (w1 w2 : nat{w2 >= w1})
: Lemma (requires fits x w1)
        (ensures  fits x w2)
        [SMTPat (fits x w1); SMTPat (fits x w2)]
  = pow2_le_compat w2 w1;
    ()

let int2bv_uext_32_64 (x : nat)
: Lemma  (requires FStar.UInt.fits x 32)
         (ensures bv_uext #32 #32 (int2bv #32 x) == int2bv #64 x)
=
  ()

let int2bv_uext_64_128 (x : nat)
: Lemma  (requires FStar.UInt.fits x 64)
         (ensures bv_uext #64 #64 (int2bv #64 x) == int2bv #128 x)
=
  ()

// Try it also under the very specific Z3 config that HACL*/Vale use
#push-options "--z3cliopt smt.arith.nl=false --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true --max_ifuel 1 --max_fuel 1 --initial_ifuel 0"

let int2bv_uext_64_128_again (x : nat)
: Lemma  (requires FStar.UInt.fits x 64)
         (ensures bv_uext #64 #64 (int2bv #64 x) == int2bv #128 x)
=
  ()

#pop-options
