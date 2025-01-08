module FStar.Endianness

/// A library of lemmas for reasoning about sequences of machine integers and
/// their (little|big)-endian representation as a sequence of bytes.
///
/// The functions in this module aim to be as generic as possible, in order to
/// facilitate compatibility with:
/// - Vale's model of machine integers (nat64 et al.), which does not rely on
///   FStar's machine integers
/// - HACL*'s Lib.IntTypes module, which exposes a universal indexed integer
///   type but uses F* machine integers under the hood.
///
/// To achieve maximum compatibility, we try to state most lemmas using nat
/// rather than UIntX.
///
/// To limit context pollution, the definitions of the recursive functions are
/// abstract; please add lemmas as you see fit. In extreme cases, ``friend``'ing
/// might be de rigueur.
///
/// .. note::
///
///    This module supersedes the poorly-named ``FStar.Krml.Endianness``.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S = FStar.Seq

[@@ noextract_to "krml"]
type bytes = S.seq U8.t

open FStar.Mul


/// Definition of little and big-endianness
/// ---------------------------------------
///
/// This is our spec, to be audited. From bytes to nat.

/// lt_to_n interprets a byte sequence as a little-endian natural number
val le_to_n : b:bytes -> Tot nat

/// be_to_n interprets a byte sequence as a big-endian natural number
val be_to_n : b:bytes -> Tot nat

/// Induction for le_to_n and be_to_n

val reveal_le_to_n (b:bytes)
  : Lemma
    (le_to_n b ==
     (match Seq.length b with
      | 0 -> 0
      | _ -> U8.v (S.head b) + pow2 8 * le_to_n (S.tail b)))

val reveal_be_to_n (b:bytes)
  : Lemma
    (be_to_n b ==
     (match Seq.length b with
      | 0 -> 0
      | _ -> U8.v (S.last b) + pow2 8 * be_to_n (S.slice b 0 (S.length b - 1))))

val lemma_le_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (le_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))

val lemma_be_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (be_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))


/// Inverse operations
/// ------------------
///
/// From nat to bytes, and their functional correctness.

/// n_to_le encodes a number as a little-endian byte sequence of a fixed,
/// sufficiently large length.
val n_to_le : len:nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:bytes{S.length b == len /\ n == le_to_n b})
  (decreases len)

/// n_to_be encodes a numbers as a big-endian byte sequence of a fixed,
/// sufficiently large length
val n_to_be:
  len:nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:bytes{S.length b == len /\ n == be_to_n b})
  (decreases len)

/// Injectivity
/// -----------

val n_to_le_inj (len: nat) (n1 n2: (n:nat{n < pow2 (8 * len)})):
  Lemma (requires (n_to_le len n1 == n_to_le len n2))
        (ensures (n1 == n2))

val n_to_be_inj (len: nat) (n1 n2: (n:nat{n < pow2 (8 * len)})) :
  Lemma (requires (n_to_be len n1 == n_to_be len n2))
        (ensures (n1 == n2))

val be_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ be_to_n b1 == be_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))

val le_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ le_to_n b1 == le_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))

/// Roundtripping
/// -------------

val n_to_be_be_to_n (len: nat) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == len))
  (ensures (
    be_to_n s < pow2 (8 * len) /\
    n_to_be len (be_to_n s) == s
  ))
  [SMTPat (n_to_be len (be_to_n s))]

val n_to_le_le_to_n (len: nat) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == len))
  (ensures (
    le_to_n s < pow2 (8 * len) /\
    n_to_le len (le_to_n s) == s
  ))
  [SMTPat (n_to_le len (le_to_n s))]


/// Specializations for F* machine integers
/// ---------------------------------------
///
/// These are useful because they take care of calling the right ``*_is_bounded`` lemmas.

let uint32_of_le (b: bytes { S.length b = 4 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt32.uint_to_t n

let le_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_le 4 (UInt32.v x)

let uint32_of_be (b: bytes { S.length b = 4 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt32.uint_to_t n

let be_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_be 4 (UInt32.v x)

let uint64_of_le (b: bytes { S.length b = 8 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt64.uint_to_t n

let le_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_le 8 (UInt64.v x)

let uint64_of_be (b: bytes { S.length b = 8 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt64.uint_to_t n

let be_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_be 8 (UInt64.v x)


/// Lifting {le,be}_to_n / n_to_{le,be} to sequences
/// ------------------------------------------------
///
/// TODO: 16-bit (but is it really needed?)
/// TODO: should these be specializations of generic functions that chop on
///       N-byte boundaries, and operate on bounded nats instead of uints?

val seq_uint32_of_le (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }

val le_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))

val seq_uint32_of_be (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }

val be_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))

val seq_uint64_of_le (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }

val le_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))

val seq_uint64_of_be (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }

val be_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))


/// Complete specification of the combinators above, relating them to {le,be}_to_ / n_to_{le,be}
/// --------------------------------------------------------------------------------------------

val offset_uint32_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_be n b) i == uint32_of_be (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_be n b) i) ]

val offset_uint32_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_le n b) i == uint32_of_le (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_le n b) i) ]

val offset_uint64_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_be n b) i == uint64_of_be (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_be n b) i) ]

val offset_uint64_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_le n b) i == uint64_of_le (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_le n b) i) ]


/// Reasoning about appending such sequences
/// ----------------------------------------
///
/// TODO: this is fairly incomplete
/// TODO: the *_base cases seem ad-hoc and derivable trivially from offset above; why have them?

val be_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    be_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint32 s1)))
  [ SMTPat (be_to_n s2); SMTPat (U32.v (S.index s1 0)) ]

val le_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    le_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (le_of_seq_uint32 s1)))
  [ SMTPat (le_to_n s2); SMTPat (U32.v (S.index s1 0)) ]

val be_of_seq_uint64_base (s1: S.seq U64.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 8 /\
    be_to_n s2 = U64.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint64 s1)))
  [ SMTPat (be_to_n s2); SMTPat (U64.v (S.index s1 0)) ]

val be_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint32 (S.append s1 s2))
      (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2)) ]

val le_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (le_of_seq_uint32 (S.append s1 s2))
      (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2)) ]

val be_of_seq_uint64_append (s1 s2: S.seq U64.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint64 (S.append s1 s2))
      (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2)) ]

/// Roundtripping
/// -------------
///
/// TODO: also incomplete

val seq_uint32_of_be_be_of_seq_uint32 (n: nat) (s: S.seq U32.t) : Lemma
  (requires (n == S.length s))
  (ensures (seq_uint32_of_be n (be_of_seq_uint32 s) `S.equal` s))
  (decreases n)
  [SMTPat (seq_uint32_of_be n (be_of_seq_uint32 s))]

val be_of_seq_uint32_seq_uint32_of_be (n: nat) (s: S.seq U8.t) : Lemma
  (requires (4 * n == S.length s))
  (ensures (be_of_seq_uint32 (seq_uint32_of_be n s) `S.equal` s))
  (decreases n)
  [SMTPat (be_of_seq_uint32 (seq_uint32_of_be n s))]

/// Reasoning about slicing such sequences
/// --------------------------------------
///
/// (Needs SMTPats above for roundtripping in their proof, hence why they're at the end.)

val slice_seq_uint32_of_be (n: nat) (s: S.seq U8.t) (lo: nat) (hi: nat) : Lemma
  (requires (4 * n == S.length s /\ lo <= hi /\ hi <= n))
  (ensures (S.slice (seq_uint32_of_be n s) lo hi) `S.equal` seq_uint32_of_be (hi - lo) (S.slice s (4 * lo) (4 * hi)))

val be_of_seq_uint32_slice (s: S.seq U32.t) (lo: nat) (hi: nat) : Lemma
  (requires (lo <= hi /\ hi <= S.length s))
  (ensures (be_of_seq_uint32 (S.slice s lo hi) `S.equal` S.slice (be_of_seq_uint32 s) (4 * lo) (4 * hi)))


/// Some reasoning about zero bytes

let rec le_to_n_zeros (s:bytes)
  : Lemma
    (requires
      forall (i:nat). i < Seq.length s ==> Seq.index s i == 0uy)
    (ensures le_to_n s == 0)
    (decreases (Seq.length s))
  = reveal_le_to_n s;
    if Seq.length s = 0 then ()
    else le_to_n_zeros (Seq.tail s)

let rec be_to_n_zeros (s:bytes)
  : Lemma
    (requires
      forall (i:nat). i < Seq.length s ==> Seq.index s i == 0uy)
    (ensures be_to_n s == 0)
    (decreases (Seq.length s))
  = reveal_be_to_n s;
    if Seq.length s = 0 then ()
    else be_to_n_zeros (Seq.slice s 0 (Seq.length s - 1))
