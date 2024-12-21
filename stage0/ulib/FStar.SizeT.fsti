module FStar.SizeT

open FStar.Mul

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

new
val t : eqtype

val fits (x: nat) : Tot prop

/// According to the C standard, "the bit width of t is not less than 16 since c99"
/// (https://en.cppreference.com/w/c/types/size_t)

val fits_at_least_16 (x:nat)
  : Lemma
    (requires x < pow2 16)
    (ensures fits x)
    [SMTPat (fits x)]

[@@noextract_to "krml"]
val v (x: t) : Pure nat
  (requires True)
  (ensures (fun y -> fits y))

/// We therefore offer two functions to create a t value.
/// Any value that fits in a uint_16 can be cast directly to t
/// Any value that might not fit in a uint_16 needs to satisfy the `fits_u32`
/// or `fits_u64` predicates. These predicates can only be introduced through a
/// stateful function (currently in Steel.ST.HigherArray), which will be extracted
/// to a static_assert by krml
val uint_to_t (x: nat) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))

/// v and uint_to_t are inverses
val size_v_inj (x: t)
  : Lemma
    (ensures uint_to_t (v x) == x)
    [SMTPat (v x)]

val size_uint_to_t_inj (x: nat)
  : Lemma
    (requires fits x)
    (ensures v (uint_to_t x) == x)
    [SMTPat (uint_to_t x)]

val fits_u32 : prop
val fits_u64 : prop

val fits_u64_implies_fits_32 (_:unit)
  : Lemma
    (requires fits_u64)
    (ensures fits_u32)

val fits_u32_implies_fits (x:nat)
  : Lemma
    (requires fits_u32 /\ x < pow2 32)
    (ensures fits x)

val fits_u64_implies_fits (x:nat)
  : Lemma
    (requires fits_u64 /\ x < pow2 64)
    (ensures fits x)

/// Creates a size_t when given a uint32 literal. Note, this will not
/// extract if [x] is not a literal (e.g., 12ul). If you want to do a
/// cast, see `uint32_to_sizet` below
noextract inline_for_extraction
val of_u32 (x: U32.t) : Pure t
  (requires fits_u32)
  (ensures (fun y -> v y == U32.v x))

/// Creates a size_t when given a uint64 literal. Note, this will not
/// extract if [x] is not a literal (e.g., 12uL). If you want to do a
/// cast, see `uint64_to_sizet` below
noextract inline_for_extraction
val of_u64 (x: U64.t) : Pure t
  (requires fits_u64)
  (ensures (fun y -> v y == U64.v x))

val uint16_to_sizet (x:U16.t) : Pure t
  (requires True)
  (ensures fun y -> v y == U16.v x)

val uint32_to_sizet (x:U32.t) : Pure t
  (requires fits_u32)
  (ensures fun y -> v y == U32.v x)

val uint64_to_sizet (x:U64.t) : Pure t
  (requires fits_u64)
  (ensures fun y -> v y == U64.v x)

val sizet_to_uint32 (x:t) : Pure U32.t
  (requires True)
  (ensures fun y -> U32.v y == v x % pow2 32)

val sizet_to_uint64 (x:t) : Pure U64.t
  (requires True)
  (ensures fun y -> U64.v y == v x % pow2 64)

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

(** Euclidean division of [a] and [b], with [b] non-zero *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))

(** Modulo specification, similar to FStar.UInt.mod *)

let mod_spec (a:nat{fits a}) (b:nat{fits b /\ b <> 0}) : GTot (n:nat{fits n}) =
  let open FStar.Mul in
  let res = a - ((a/b) * b) in
  fits_lte res a;
  res

(** Euclidean remainder

    The result is the modulus of [a] with respect to a non-zero [b] *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> mod_spec (v a) (v b) = v c))

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

unfold let ( +^ ) = add
unfold let ( -^ ) = sub
unfold let ( *^ ) = mul
unfold let ( %^ ) = rem
unfold let ( >^ ) = gt
unfold let ( >=^ ) = gte
unfold let ( <^ ) = lt
unfold let ( <=^ ) = lte

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
    = assume (x >= 0 /\ fits x); uint_to_t x
