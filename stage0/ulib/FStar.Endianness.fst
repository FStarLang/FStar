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
/// .. note::
///
///    This module supersedes the poorly-named ``FStar.Krml.Endianness``.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S = FStar.Seq

open FStar.Mul

/// Definition of little and big-endianness
/// ---------------------------------------

let rec le_to_n b
  : Tot nat (decreases (S.length b))
  = if S.length b = 0 then 0
    else U8.v (S.head b) + pow2 8 * le_to_n (S.tail b)

let rec be_to_n b
  : Tot nat (decreases (S.length b))
  = if S.length b = 0 then 0
    else U8.v (S.last b) + pow2 8 * be_to_n (S.slice b 0 (S.length b - 1))

let reveal_le_to_n _ = ()

let reveal_be_to_n _ = ()

/// Inverse operations
/// ------------------

/// TODO: move to FStar.Math.Lemmas?
private val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

/// TODO: move to FStar.Math.Lemmas? US spelling?
private val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

let rec lemma_le_to_n_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_le_to_n_is_bounded s;
    assert(UInt8.v (Seq.index b 0) < pow2 8);
    assert(le_to_n s < pow2 (8 * Seq.length s));
    assert(le_to_n b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.index b 0)) (le_to_n s) (pow2 8);
    assert(le_to_n b <= pow2 8 * (le_to_n s + 1));
    assert(le_to_n b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

let rec lemma_be_to_n_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 0 (Seq.length b - 1) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_be_to_n_is_bounded s;
    assert(UInt8.v (Seq.last b) < pow2 8);
    assert(be_to_n s < pow2 (8 * Seq.length s));
    assert(be_to_n b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.last b)) (be_to_n s) (pow2 8);
    assert(be_to_n b <= pow2 8 * (be_to_n s + 1));
    assert(be_to_n b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

let rec n_to_le len n =
  if len = 0 then
    S.empty
  else
    let len = len - 1 in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * len);
    assert(n' < pow2 (8 * len ));
    let b' = n_to_le len n' in
    let b = S.cons byte b' in
    S.lemma_eq_intro b' (S.tail b);
    b

let rec n_to_be len n =
  if len = 0 then
    S.empty
  else
    let len = len - 1 in
    let byte = U8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.pow2_plus 8 (8 * len);
    let b' = n_to_be len n' in
    let b'' = S.create 1 byte in
    let b = S.append b' b'' in
    S.lemma_eq_intro b' (S.slice b 0 len);
    b

/// Injectivity
/// -----------

// this lemma easily follows from le_to_n . (n_to_le len) == id, the inversion
// proof in the spec for n_to_le
let n_to_le_inj len n1 n2 = ()

let n_to_be_inj len n1 n2 = ()

let rec be_to_n_inj b1 b2 =
  if Seq.length b1 = 0
  then ()
  else begin
    be_to_n_inj (Seq.slice b1 0 (Seq.length b1 - 1)) (Seq.slice b2 0 (Seq.length b2 - 1));
    Seq.lemma_split b1 (Seq.length b1 - 1);
    Seq.lemma_split b2 (Seq.length b2 - 1)
  end

let rec le_to_n_inj b1 b2 =
  if Seq.length b1 = 0
  then ()
  else begin
    le_to_n_inj (Seq.slice b1 1 (Seq.length b1)) (Seq.slice b2 1 (Seq.length b2));
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1
  end

/// Roundtripping
/// -------------

let n_to_be_be_to_n len s =
  lemma_be_to_n_is_bounded s;
  be_to_n_inj s (n_to_be len (be_to_n s))

let n_to_le_le_to_n len s =
  lemma_le_to_n_is_bounded s;
  le_to_n_inj s (n_to_le len (le_to_n s))


/// Reasoning over sequences of integers
/// ------------------------------------
///
/// TODO: should these be sequences of nats instead? then re-use these lemmas to
/// export a variant (which we need for, say, hashes) specialized to F* machine
/// integers?

let rec seq_uint32_of_le l b =
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_le hd) (seq_uint32_of_le (l - 1) tl)

let rec le_of_seq_uint32 s =
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint32 (S.head s)) (le_of_seq_uint32 (S.tail s))

let rec seq_uint32_of_be l b =
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 4 in
    S.cons (uint32_of_be hd) (seq_uint32_of_be (l - 1) tl)

let rec be_of_seq_uint32 s =
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint32 (S.head s)) (be_of_seq_uint32 (S.tail s))

let rec seq_uint64_of_le l b =
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_le hd) (seq_uint64_of_le (l - 1) tl)

let rec le_of_seq_uint64 s =
  if S.length s = 0 then
    S.empty
  else
    S.append (le_of_uint64 (S.head s)) (le_of_seq_uint64 (S.tail s))

let rec seq_uint64_of_be l b =
  if S.length b = 0 then
    S.empty
  else
    let hd, tl = Seq.split b 8 in
    S.cons (uint64_of_be hd) (seq_uint64_of_be (l - 1) tl)

let rec be_of_seq_uint64 s =
  if S.length s = 0 then
    S.empty
  else
    S.append (be_of_uint64 (S.head s)) (be_of_seq_uint64 (S.tail s))

/// Pure indexing & update over sequences
/// -------------------------------------

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 50"

let rec offset_uint32_be (b: bytes) (n: nat) (i: nat) =
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 4 in
    if i = 0 then
      ()
    else
      offset_uint32_be tl (n - 1) (i - 1)

let rec offset_uint32_le (b: bytes) (n: nat) (i: nat) =
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 4 in
    if i = 0 then
      ()
    else
      offset_uint32_le tl (n - 1) (i - 1)

let rec offset_uint64_be (b: bytes) (n: nat) (i: nat) =
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 8 in
    if i = 0 then
      ()
    else
      offset_uint64_be tl (n - 1) (i - 1)

let rec offset_uint64_le (b: bytes) (n: nat) (i: nat) =
  if S.length b = 0 then
    false_elim ()
  else
    let hd, tl = Seq.split b 8 in
    if i = 0 then
      ()
    else
      offset_uint64_le tl (n - 1) (i - 1)


/// Appending and slicing sequences of integers
/// -------------------------------------------

#set-options "--max_fuel 1 --z3rlimit 20"

(* TODO: move to FStar.Seq.Properties, with the pattern *)
let tail_cons (#a: Type) (hd: a) (tl: S.seq a): Lemma
  (ensures (S.equal (S.tail (S.cons hd tl)) tl))
//  [ SMTPat (S.tail (S.cons hd tl)) ]
=
  ()

let be_of_seq_uint32_base s1 s2 = ()

let le_of_seq_uint32_base s1 s2 = ()

let be_of_seq_uint64_base s1 s2 = ()

let rec be_of_seq_uint32_append s1 s2 =
  if S.length s1 = 0 then begin
    assert (S.equal (be_of_seq_uint32 s1) S.empty);
    assert (S.equal s1 S.empty);
    S.append_empty_l s2;
    S.append_empty_l (be_of_seq_uint32 s2);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    calc S.equal {
      be_of_seq_uint32 (S.append s1 s2);
      S.equal { () }
      be_of_seq_uint32 (S.append (S.cons (S.head s1) (S.tail s1)) s2);
      S.equal { S.append_cons (S.head s1) (S.tail s1) s2 }
      be_of_seq_uint32 (S.cons (S.head s1) (S.append (S.tail s1) s2));
      S.equal { () }
      be_of_seq_uint32 (S.cons (S.head s1) (S.append (S.tail s1) s2));
      S.equal { S.head_cons (S.head s1) (S.append (S.tail s1) s2);
                tail_cons (S.head s1) (S.append (S.tail s1) s2) }
      S.append (be_of_uint32 (S.head s1))
               (be_of_seq_uint32 (S.append (S.tail s1) s2));
      S.equal { be_of_seq_uint32_append (S.tail s1) s2 }
      S.append (be_of_uint32 (S.head s1))
               (S.append (be_of_seq_uint32 (S.tail s1)) (be_of_seq_uint32 s2));
    }
  end

let rec le_of_seq_uint32_append s1 s2 =
  Classical.forall_intro_2 (tail_cons #U32.t); // TODO: this is a local pattern, remove once tail_cons lands in FStar.Seq.Properties
  if S.length s1 = 0 then begin
    assert (S.equal (le_of_seq_uint32 s1) S.empty);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    assert (S.equal (S.append s1 s2) (S.cons (S.head s1) (S.append (S.tail s1) s2)));
    assert (S.equal (le_of_seq_uint32 (S.append s1 s2))
      (S.append (le_of_uint32 (S.head s1)) (le_of_seq_uint32 (S.append (S.tail s1) s2))));
    le_of_seq_uint32_append (S.tail s1) s2
  end

let rec be_of_seq_uint64_append s1 s2 =
  Classical.forall_intro_2 (tail_cons #U64.t); // TODO: this is a local pattern, remove once tail_cons lands in FStar.Seq.Properties
  if S.length s1 = 0 then begin
    assert (S.equal (be_of_seq_uint64 s1) S.empty);
    assert (S.equal (S.append s1 s2) s2);
    ()
  end else begin
    assert (S.equal (S.append s1 s2) (S.cons (S.head s1) (S.append (S.tail s1) s2)));
    assert (S.equal (be_of_seq_uint64 (S.append s1 s2))
      (S.append (be_of_uint64 (S.head s1)) (be_of_seq_uint64 (S.append (S.tail s1) s2))));
    be_of_seq_uint64_append (S.tail s1) s2
  end

let rec seq_uint32_of_be_be_of_seq_uint32 n s =
  if n = 0
  then ()
  else begin
    assert (s `S.equal` S.cons (S.head s) (S.tail s));
    seq_uint32_of_be_be_of_seq_uint32 (n - 1) (S.tail s);
    let s' = be_of_seq_uint32 s in
    S.lemma_split s' 4;
    S.lemma_append_inj (S.slice s' 0 4) (S.slice s' 4 (S.length s')) (be_of_uint32 (S.head s)) (be_of_seq_uint32 (S.tail s))
  end

let rec be_of_seq_uint32_seq_uint32_of_be n s =
  if n = 0
  then ()
  else begin
    S.lemma_split s 4;
    be_of_seq_uint32_seq_uint32_of_be (n - 1) (S.slice s 4 (S.length s));
    let s' = seq_uint32_of_be n s in
    let hd, tl = S.split s 4 in
    assert (S.head s' == uint32_of_be hd);
    tail_cons (uint32_of_be hd) (seq_uint32_of_be (n - 1) tl);
    assert (S.tail s' == seq_uint32_of_be (n - 1) tl);
    let s'' = be_of_seq_uint32 s' in
    S.lemma_split s'' 4;
    S.lemma_append_inj (S.slice s'' 0 4) (S.slice s'' 4 (S.length s'')) (be_of_uint32 (S.head s')) (be_of_seq_uint32 (S.tail s'));
    n_to_be_be_to_n 4 hd
  end

let slice_seq_uint32_of_be n s lo hi = ()

let be_of_seq_uint32_slice s lo hi =
  slice_seq_uint32_of_be (S.length s) (be_of_seq_uint32 s) lo hi
