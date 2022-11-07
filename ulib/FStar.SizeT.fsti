module FStar.SizeT

open FStar.Mul

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

val t : eqtype

val fits (x: nat) : Tot prop

[@@noextract_to "krml"]
val v (x: t) : Pure nat
  (requires True)
  (ensures (fun y -> fits y))

val size_v_inj (x1 x2: t) : Lemma
  (v x1 == v x2 ==> x1 == x2)
  [SMTPat (v x1); SMTPat (v x2)]

/// According to the C standard, "the bit width of t is not less than 16 since c99"
/// (https://en.cppreference.com/w/c/types/t)
/// We therefore offer two functions to create a t value.
/// Any value that fits in a uint_16 can be cast directly to t
/// Any value that might not fit in a uint_16 needs to satisfy the `fits_u32`
/// or `fits_u64` predicates. These predicates can only be introduced through a
/// stateful function (currently in Steel.ST.HigherArray), which will be extracted
/// to a static_assert by krml
val uint_to_t (x: nat) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))

val fits_u32 : prop
val fits_u64 : prop

noextract inline_for_extraction
val mk_u32 (x: U32.t) : Pure t
  (requires fits_u32)
  (ensures (fun y -> v y == U32.v x))

noextract inline_for_extraction
val mk_u64 (x: U64.t) : Pure t
  (requires fits_u64)
  (ensures (fun y -> v y == U64.v x))

val fits_lte (x y: nat) : Lemma
  (requires (x <= y /\ fits y))
  (ensures (fits x))
  [SMTPat (fits x); SMTPat (fits y)]

(** Non-overflowing arithmetic operations *)

val add (x y: t) : Pure t
  (requires (fits (v x + v y)))
  (ensures (fun z -> v z == v x + v y))

val sub (x y: t) : Pure t
  (requires (v x >= v y))
  (ensures (fun z -> v z == v x - v y))

val mul (x y: t) : Pure t
  (requires (fits (v x * v y)))
  (ensures (fun z -> v z == v x * v y))

(** Greater than *)
val gt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x > v y)))

(** Greater than or equal *)
val gte (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x >= v y)))

(** Less than *)
val lt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x < v y)))

(** Less than or equal *)
val lte (x y: t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x <= v y)))

(** Infix notations *)

unfold let op_Plus_Hat = add
unfold let op_Subtraction_Hat = sub
unfold let op_Star_Hat = mul
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t
    = uint_to_t x
#reset-options
