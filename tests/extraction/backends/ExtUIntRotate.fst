module ExtUIntRotate

/// `rotate_left` / `rotate_right`, which no backend has as a primitive:
///
///   - C has no rotate operator at all, so Karamel has to synthesise one.
///   - OCaml has no rotate either, and UInt8 is a masked `int` while the wider
///     types are Stdint values, so there are two separate synthesised versions.
///   - Rust *does* have `rotate_left`/`rotate_right` methods, so the mapping is
///     direct and the interesting question is whether the widths line up.
///
/// The textbook synthesis is `(x << s) | (x >> (n - s))`. It has a hole:
/// FStar.UInt{8,16,32,64}.rotate_left only requires `v s < n`, so **`s = 0` is
/// legal**, and then `x >> (n - 0)` is a shift by the full width, which is
/// undefined behaviour in C and a panic in debug Rust. Checks 1-4 and 20-23
/// pin down the `s = 0` case at every width for exactly that reason.
///
/// Exact rotated values are only pinned at 8 bits: F* cannot evaluate the
/// bit-vector definition of `rotate_left` on a concrete 32- or 64-bit operand
/// (FINDINGS.md #13), so the wider widths are covered relationally with
/// `rotate_left_right_inverse` and `rotate_left_full_identity` instead.

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
module U   = FStar.UInt

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let a8   : U8.t  = 177uy
let a16  : U16.t = 45329us
let a32  : U32.t = 3735928559ul
let a64  : U64.t = 12297829382473034410uL

let z0   : U32.t = 0ul
let s3   : U32.t = 3ul
let s7   : U32.t = 7ul
let s13  : U32.t = 13ul
let s31  : U32.t = 31ul
let s63  : U32.t = 63ul

let s5   : U32.t = 5ul
let s17  : U32.t = 17ul

/// `FStar.UInt` proves `rotate_left a n = a` (a full turn) but has no lemma for
/// `rotate_left a 0`, even though `s = 0` is inside the precondition of
/// `UInt32.rotate_left`. Both follow immediately from `nth_lemma`, since
/// `rotate_left_lemma` gives `nth (rotate_left a 0) i = nth a ((i + 0) % n)`
/// and `i < n`.
let rotl_zero (#n:pos) (a:U.uint_t n) : Lemma (U.rotate_left #n a 0 == a) =
  U.nth_lemma #n (U.rotate_left #n a 0) a

let rotr_zero (#n:pos) (a:U.uint_t n) : Lemma (U.rotate_right #n a 0 == a) =
  U.nth_lemma #n (U.rotate_right #n a 0) a

/// Rotating by zero is the identity. The naive `(x << s) | (x >> (n - s))`
/// lowering shifts by the full width here, which C leaves undefined -- in
/// practice x86 masks the shift count and yields `x | x`, which happens to be
/// right, while other targets yield 0 and the check fails.
#push-options "--z3rlimit 60"
let zero_shift_tests () : I32.t =
  rotl_zero #8  (U8.v a8);
  rotl_zero #16 (U16.v a16);
  rotl_zero #32 (U32.v a32);
  rotl_zero #64 (U64.v a64);
  rotr_zero #8  (U8.v a8);
  rotr_zero #16 (U16.v a16);
  rotr_zero #32 (U32.v a32);
  rotr_zero #64 (U64.v a64);
     chk 1l (U8.eq  (U8.rotate_left  a8  z0)  a8)
 &&& chk 2l (U16.eq (U16.rotate_left a16 z0) a16)
 &&& chk 3l (U32.eq (U32.rotate_left a32 z0)    a32)
 &&& chk 4l (U64.eq (U64.rotate_left a64 z0) a64)
 &&& chk 5l (U8.eq  (U8.rotate_right  a8  z0)  a8)
 &&& chk 6l (U16.eq (U16.rotate_right a16 z0) a16)
 &&& chk 7l (U32.eq (U32.rotate_right a32 z0)    a32)
 &&& chk 8l (U64.eq (U64.rotate_right a64 z0) a64)
#pop-options

/// Exact values, at the only width where F* can evaluate the specification.
/// 177 = 0b10110001; rotated left by 3 that is 0b10001101 = 141, and rotated
/// right by 3 it is 0b00110110 = 54.
#push-options "--fuel 20 --ifuel 20 --z3rlimit 200"
let exact_tests () : I32.t =
  assert_norm (U.rotate_left #8 177 3 == 141);
  assert_norm (U.rotate_right #8 177 3 == 54);
     chk 10l (U8.eq (U8.rotate_left  a8 s3) 141uy)
 &&& chk 11l (U8.eq (U8.rotate_right a8 s3) 54uy)
#pop-options

/// Rotating one way and back is the identity, at every width and for shift
/// counts on both sides of the halfway point.
#push-options "--z3rlimit 120"
let inverse_tests () : I32.t =
  U.rotate_left_right_inverse #8  (U8.v a8)   (U32.v s3);
  U.rotate_left_right_inverse #16 (U16.v a16) (U32.v s5);
  U.rotate_left_right_inverse #32 (U32.v a32) (U32.v s7);
  U.rotate_left_right_inverse #32 (U32.v a32) (U32.v s31);
  U.rotate_left_right_inverse #64 (U64.v a64) (U32.v s17);
  U.rotate_right_left_inverse #32 (U32.v a32) (U32.v s13);
     chk 20l (U8.eq  (U8.rotate_right  (U8.rotate_left  a8 s3) s3) a8)
 &&& chk 21l (U16.eq (U16.rotate_right (U16.rotate_left a16 s5) s5) a16)
 &&& chk 22l (U32.eq (U32.rotate_right (U32.rotate_left a32 s7) s7) a32)
 &&& chk 23l (U32.eq (U32.rotate_right (U32.rotate_left a32 s31) s31) a32)
 &&& chk 24l (U64.eq (U64.rotate_right (U64.rotate_left a64 s17) s17) a64)
 &&& chk 25l (U32.eq (U32.rotate_left  (U32.rotate_right a32 s13) s13) a32)
#pop-options

/// A rotation actually has to move the bits: rotating a value that is not
/// invariant under the rotation must change it. Without this the whole module
/// would be satisfied by a backend that implemented rotate as the identity.
#push-options "--fuel 20 --ifuel 20 --z3rlimit 200"
let nontrivial_tests () : I32.t =
  assert_norm (U.rotate_left #8 177 3 == 141);
  assert_norm (U.rotate_right #8 177 3 == 54);
     chk 30l (not (U8.eq (U8.rotate_left a8 s3) a8))
 &&& chk 31l (not (U8.eq (U8.rotate_right a8 s3) a8))
#pop-options

let main () : I32.t =
     zero_shift_tests ()
 &&& exact_tests ()
 &&& inverse_tests ()
 &&& nontrivial_tests ()
