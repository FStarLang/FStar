(* Model implementation of FStar.Bytes: verified, but never extracted (the real implementation is native).
   Bytes are modeled as lists of bytes. String conversions are not modeled
   (they return empty results). *)
module FStar.Bytes

module S = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot
module E = FStar.Endianness

let bytes : t:Type0{hasEq t} = l:list u8{L.length l < pow2 32}

let len b = U32.uint_to_t (L.length b)

let reveal b = S.seq_of_list b

let length_reveal _ = ()

let mk (s:S.seq byte{S.length s < pow2 32}) : bytes = S.seq_to_list s

let hide s = mk s
let hide_reveal _ = ()
let reveal_hide _ = ()

let reveal_inj (b1 b2:bytes)
  : Lemma (requires S.equal (reveal b1) (reveal b2)) (ensures b1 == b2)
  = S.lemma_seq_to_seq_of_list b1;
    S.lemma_seq_to_seq_of_list b2

let empty_bytes = []
let empty_unique _ = ()

let get b pos = S.index (S.seq_of_list b) (U32.v pos)

let extensionality b1 b2 =
  let aux (j:nat{j < length b1}) : Lemma (S.index (reveal b1) j == S.index (reveal b2) j) =
    let i = U32.uint_to_t j in
    assert (b1.[i] == b2.[i])
  in
  FStar.Classical.forall_intro aux;
  reveal_inj b1 b2

let create len v = mk (S.create (U32.v len) v)
let init len f = mk (S.init (U32.v len) (fun i -> f (U32.uint_to_t i)))

let abyte b = mk (S.create 1 b)
let twobytes (b1, b2) = mk (S.append (S.create 1 b1) (S.create 1 b2))

let append b1 b2 = mk (S.append (S.seq_of_list b1) (S.seq_of_list b2))
let slice b s e = mk (S.slice (S.seq_of_list b) (U32.v s) (U32.v e))
let sub b s l = mk (S.slice (S.seq_of_list b) (U32.v s) (U32.v s + U32.v l))
let split b k = (slice b 0ul k, slice b k (len b))

let rec repr_bytes n : Tot (k:pos{fits_in_k_bytes n k}) (decreases n) =
  if n < 256 then (assert_norm (pow2 8 == 256); 1)
  else begin
    let k = repr_bytes (n / 256) in
    assert_norm (pow2 8 == 256);
    FStar.Math.Lemmas.pow2_plus 8 (8 * k);
    k + 1
  end

let rec lemma_repr_bytes_values n =
  if n < 256 then () else lemma_repr_bytes_values (n / 256)

let rec repr_bytes_size k n =
  assert_norm (pow2 8 == 256);
  if n < 256 then ()
  else begin
    if k = 1 then ()
    else begin
      FStar.Math.Lemmas.pow2_plus 8 (8 * (k - 1));
      repr_bytes_size (k - 1) (n / 256)
    end
  end

let int_of_bytes b =
  E.lemma_be_to_n_is_bounded (S.seq_of_list b);
  E.be_to_n (S.seq_of_list b)

let bytes_of_int k n =
  FStar.Math.Lemmas.pow2_le_compat (8 * k) (8 * repr_bytes n);
  mk (E.n_to_be k n)

let int_of_bytes_of_int #k n = repr_bytes_size k n

let bytes_of_int_of_bytes b =
  E.n_to_be_be_to_n (length b) (reveal b);
  S.lemma_seq_to_seq_of_list b

let int32_of_bytes b =
  FStar.Math.Lemmas.pow2_le_compat 32 (8 * length b);
  U32.uint_to_t (int_of_bytes b)

let int16_of_bytes b =
  FStar.Math.Lemmas.pow2_le_compat 16 (8 * length b);
  U16.uint_to_t (int_of_bytes b)

let int8_of_bytes b =
  U8.uint_to_t (int_of_bytes b)

let bytes_of_int32 n = repr_bytes_size 4 (U32.v n); bytes_of_int 4 (U32.v n)
let bytes_of_int16 n = repr_bytes_size 2 (U16.v n); bytes_of_int 2 (U16.v n)
let bytes_of_int8 n = repr_bytes_size 1 (U8.v n); bytes_of_int 1 (U8.v n)

let xor_seq (n:nat) (s1:S.seq byte{S.length s1 >= n}) (s2:S.seq byte{S.length s2 >= n})
  : (s:S.seq byte{S.length s == n})
  = S.init n (fun i -> U8.logxor (S.index s1 i) (S.index s2 i))

let xor n b1 b2 = mk (xor_seq (U32.v n) (S.seq_of_list b1) (S.seq_of_list b2))

let logxor_comm (a b:byte) : Lemma (U8.logxor a b == U8.logxor b a) =
  FStar.UInt.logxor_commutative (U8.v a) (U8.v b);
  U8.v_inj (U8.logxor a b) (U8.logxor b a)

let logxor_cancel (a b:byte) : Lemma (U8.logxor (U8.logxor a b) b == a) =
  FStar.UInt.logxor_associative (U8.v a) (U8.v b) (U8.v b);
  FStar.UInt.logxor_self (U8.v b);
  FStar.UInt.logxor_lemma_1 (U8.v a);
  U8.v_inj (U8.logxor (U8.logxor a b) b) a

let xor_commutative n b1 b2 =
  let s1 = reveal b1 in
  let s2 = reveal b2 in
  let aux (i:nat{i < U32.v n}) : Lemma (U8.logxor (S.index s1 i) (S.index s2 i) ==
                                        U8.logxor (S.index s2 i) (S.index s1 i)) =
    logxor_comm (S.index s1 i) (S.index s2 i)
  in
  FStar.Classical.forall_intro aux;
  assert (S.equal (xor_seq (U32.v n) s1 s2) (xor_seq (U32.v n) s2 s1))

let xor_append b1 b2 x1 x2 =
  let lhs = xor U32.(len b1 + len b2) (b1 @| b2) (x1 @| x2) in
  let rhs = xor (len b1) b1 x1 @| xor (len b2) b2 x2 in
  assert (S.equal (reveal lhs) (reveal rhs));
  reveal_inj lhs rhs

let xor_idempotent n b1 b2 =
  let x = xor n b1 b2 in
  let r = xor n x b2 in
  let aux (i:nat{i < U32.v n}) : Lemma (S.index (reveal r) i == S.index (reveal b1) i) =
    logxor_cancel (S.index (reveal b1) i) (S.index (reveal b2) i)
  in
  FStar.Classical.forall_intro aux;
  assert (S.equal (reveal r) (reveal b1));
  reveal_inj r b1

let utf8_encode _ = empty_bytes
let iutf8_opt _ = None

let string_of_hex _ = ""
let bytes_of_hex _ = empty_bytes
let hex_of_string _ = ""
let hex_of_bytes _ = ""
let print_bytes _ = ""
let bytes_of_string _ = empty_bytes
