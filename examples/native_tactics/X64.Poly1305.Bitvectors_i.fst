module X64.Poly1305.Bitvectors_i
open FStar.BV
open FStar.Tactics
open FStar.Tactics.Derived
open BV
open FStar.Mul
open FStar.UInt

// tweak options?
#reset-options "--smtencoding.elim_box true"

let lemma_shr2 x =
   assert_by_tactic (shift_right #64 x 2 == udiv #64 x 4) bv_tac

let lemma_shr4 x =
  assert_by_tactic (shift_right #64 x 4 == udiv #64 x 16) bv_tac

let lemma_and_mod_n x =
  assert_by_tactic (logand #64 x 3 == mod #64 x 4 /\ logand #64 x 15 == mod #64 x 16)
                   (fun () -> seq split bv_tac)

let lemma_clear_lower_2 x =
  assert_by_tactic
  (logand #8 x 0xfc == mul_mod #8 (udiv #8 x 4) 4)
  bv_tac

let lemma_and_constants x =
  assert_by_tactic
  (logand #64 x 0 == (0 <: uint_t 64) /\
   logand #64 x 0xffffffffffffffff == x)
  (fun () -> seq split bv_tac)

let lemma_poly_constants x =
 assert_by_tactic
   (logand #64 x 0x0ffffffc0fffffff < (0x1000000000000000 <: uint_t 64) /\
    logand #64 x 0x0ffffffc0ffffffc < (0x1000000000000000 <: uint_t 64) /\
    mod #64 (logand #64 x 0x0ffffffc0ffffffc) 4 == (0 <: uint_t 64))
   (fun () -> split ();
              split ();
              bv_tac_lt 64;
              bv_tac_lt 64;
              bv_tac ())

let lemma_and_commutes x y =
  assert_by_tactic
    (logand #64 x y == logand #64 y x)
    bv_tac

let lemma_bv128_64_64_and_helper x x0 x1 y y0 y1 z z0 z1 =
// TODO
  admit()

let bv128_64_64 x1 x0 = bvor (bvshl (bv_uext #64 #64 x1) 64) (bv_uext #64 #64 x0)

let lemma_bv128_64_64_and x x0 x1 y y0 y1 z z0 z1 =
// TODO
  admit()

#reset-options "--smtencoding.elim_box true --z3cliopt smt.case_split=3"
let lemma_bytes_shift_constants0 x =
  assert_by_tactic (shift_left #64 0 3 == (0 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 0 == (0x1 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants1 x =
  assert_by_tactic (shift_left #64 1 3 == (8 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 8 == (0x100 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants2 x =
  assert_by_tactic (shift_left #64 2 3 == (16 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 16 == (0x10000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants3 x =
  assert_by_tactic (shift_left #64 3 3 == (24 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 24 == (0x1000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants4 x =
  assert_by_tactic (shift_left #64 4 3 == (32 <: uint_t 64)) bv_tac;
    assert_by_tactic (shift_left #64 1 32 == (0x100000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants5 x =
  assert_by_tactic (shift_left #64 5 3 == (40 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 40 == (0x10000000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants6 x =
  assert_by_tactic (shift_left #64 6 3 == (48 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 48 == (0x1000000000000 <: uint_t 64)) bv_tac
let lemma_bytes_shift_constants7 x =
  assert_by_tactic (shift_left #64 7 3 == (56 <: uint_t 64)) bv_tac;
  assert_by_tactic (shift_left #64 1 56 == (0x100000000000000 <: uint_t 64)) bv_tac

let lemma_bytes_and_mod0 x =
  assert_by_tactic (logand #64 x (0x1 - 1) == mod #64 x 0x1) bv_tac

let lemma_bytes_and_mod1 x =
  assert_by_tactic (logand #64 x (0x100 - 1) == mod #64 x 0x100) bv_tac

let lemma_bytes_and_mod2 x =
  assert_by_tactic (logand #64 x (0x10000 - 1) == mod #64 x 0x10000) bv_tac
let lemma_bytes_and_mod3 x =
  assert_by_tactic (logand #64 x (0x1000000 - 1) == mod #64 x 0x1000000) bv_tac

let lemma_bytes_and_mod4 x =
  assert_by_tactic (logand #64 x (0x100000000 - 1) == mod #64 x 0x100000000) bv_tac

let lemma_bytes_and_mod5 x =
  assert_by_tactic (logand #64 x (0x10000000000 - 1) == mod #64 x 0x10000000000) bv_tac

let lemma_bytes_and_mod6 x =
  assert_by_tactic (logand #64 x (0x1000000000000 - 1) == mod #64 x 0x1000000000000) bv_tac

let lemma_bytes_and_mod7 x =
  assert_by_tactic (logand #64 x (0x100000000000000 - 1) == mod #64 x 0x100000000000000) bv_tac

let lemma_bytes_and_mod x y =
  match y with
  | 0 ->
      lemma_bytes_shift_constants0 ();
      lemma_bytes_and_mod0 x
  | 1 ->
    lemma_bytes_shift_constants1 ();
    lemma_bytes_and_mod1 x
  | 2 ->
    lemma_bytes_shift_constants2 ();
    lemma_bytes_and_mod2 x
  | 3 ->
    lemma_bytes_shift_constants3 ();
    lemma_bytes_and_mod3 x
  | 4 ->
     lemma_bytes_shift_constants4 ();
     lemma_bytes_and_mod4 x
  | 5 ->
    lemma_bytes_shift_constants5 ();
    lemma_bytes_and_mod5 x
  | 6 ->
    lemma_bytes_shift_constants6 ();
    lemma_bytes_and_mod6 x
  | 7 ->
    lemma_bytes_shift_constants7 ();
    lemma_bytes_and_mod7 x

let lemma_bytes_power2 () =
  assert_norm (pow2 0 == 0x1);
  assert_norm (pow2 8 == 0x100);
  assert_norm (pow2 16 == 0x10000);
  assert_norm (pow2 24 == 0x1000000);
  assert_norm (pow2 32 == 0x100000000);
  assert_norm (pow2 40 == 0x10000000000);
  assert_norm (pow2 48 == 0x1000000000000);
  assert_norm (pow2 56 == 0x100000000000000);
  ()

let lemma_bytes_shift_power2 y =
  (match y with
  | 0 ->
    lemma_bytes_shift_constants0 ()
  | 1 ->
    lemma_bytes_shift_constants1 ()
  | 2 ->
    lemma_bytes_shift_constants2 ()
  | 3 ->
    lemma_bytes_shift_constants3 ()
  | 4 ->
    lemma_bytes_shift_constants4 ()
  | 5 ->
    lemma_bytes_shift_constants5 ()
  | 6 ->
    lemma_bytes_shift_constants6 ()
  | 7 ->
    lemma_bytes_shift_constants7 ()
  | _ -> ());
  lemma_bytes_power2 ()


// val lowerUpper128: l:uint_t 64 -> u:uint_t 64 -> Tot (uint_t 128)
// let lowerUpper128 l u = l + (0x10000000000000000 * u)

// val lemma_lowerUpper128_and: x:uint_t 128 -> x0:uint_t 64 -> x1:uint_t 64 ->
//   y:uint_t 128 -> y0:uint_t 64 -> y1:uint_t 64 ->
//   z:uint_t 128 -> z0:uint_t 64 -> z1:uint_t 64 ->
//   Lemma (requires (z0 == logand #64 x0 y0 /\
//                 z1 == logand #64 x1 y1 /\
//                 x == lowerUpper128 x1 x0 /\
//                 y == lowerUpper128 y1 y0 /\
//                 z == lowerUpper128 z1 z0))
//      (ensures (z == logand #128 x y))
// let lemma_lowerUpper128_and x x0 x1 y y0 y1 z z0 z1 = ()
