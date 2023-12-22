module Bug3130d

(* Taken from Comparse *)

open FStar.Mul

type nat_lbytes (sz:nat) = n:nat{n < normalize_term (pow2 (8*sz))}

assume
val nat_lbytes_helper: sz:nat -> Lemma (normalize_term (pow2 (8*sz)) == pow2 (8*sz))
[SMTPat (nat_lbytes sz)]

/// Minimal interface to manipulate symbolic bytes.
/// Here are the explanations for a few design decisions:
/// - We don't require that only `empty` has length zero, e.g. we may have `concat empty empty <> empty`.
/// - We implement `split` and not `slice`, because `slice` causes trouble in the symbolic case:
///   with `slice`, how do you get the left and right part of `concat empty (concat empty empty)`?
/// - `split` returns an option, hence can fail if the indices are not on the correct bounds.
///   * We require `split` to succeed on the bound of a `concat` (see `split_concat_...`).
///   * This is useful to state the `concat_split` lemma in a way which would be correct on symbolic bytes.
/// - To compensate the first fact, and the fact that we don't require decidable equality,
///   we need a function that recognize the `empty` bytes.
/// - The `to_nat` function can fail, if the bytes are not public for example

class bytes_like (bytes:Type0) = {
  length: bytes -> nat;

  empty: bytes;
  empty_length: unit -> Lemma (length empty == 0);
  recognize_empty: b:bytes -> res:bool{res <==> b == empty};

  concat: bytes -> bytes -> bytes;
  concat_length: b1:bytes -> b2:bytes -> Lemma (length (concat b1 b2) == (length b1) + (length b2));

  split: b:bytes -> i:nat -> option (bytes & bytes);
  split_length: b:bytes -> i:nat -> Lemma (
    match split b i with
    | Some (b1, b2) -> length b1 == i /\ i+length b2 == length b
    | None -> True
  );

  split_concat: b1:bytes -> b2:bytes -> Lemma (split (concat b1 b2) (length b1) == Some (b1, b2));

  concat_split: b:bytes -> i:nat -> Lemma (
    match split b i with
    | Some (lhs, rhs) -> concat lhs rhs == b
    | _ -> True
  );

  to_nat: b:bytes -> option (nat_lbytes (length b));
  from_nat: sz:nat -> nat_lbytes sz -> b:bytes{length b == sz};

  from_to_nat: sz:nat -> n:nat_lbytes sz -> Lemma
    (to_nat (from_nat sz n) == Some n);

  to_from_nat: b:bytes -> Lemma (
    match to_nat b with
    | Some n -> b == from_nat (length b) n
    | None -> True
  );
}

/// This type defines a predicate on `bytes` that is compatible with its structure.
/// It is meant to be used for labeling predicates, which are typically compatible with the `bytes` structure.

let bytes_pre_is_compatible (#bytes:Type0) {|bytes_like bytes|} (pre:bytes -> prop) =
    (pre empty) /\
    (forall b1 b2. pre b1 /\ pre b2 ==> pre (concat b1 b2)) /\
    (forall b i. pre b /\ Some? (split b i) ==> pre (fst (Some?.v (split b i))) /\ pre (snd (Some?.v (split b i)))) /\
    (forall sz n. pre (from_nat sz n))

let bytes_pre_is_compatible_intro
  (#bytes:Type0) {|bytes_like bytes|} (pre:bytes -> prop)
  (empty_proof:squash(pre empty))
  (concat_proof:(b1:bytes{pre b1} -> b2:bytes{pre b2} -> Lemma (pre (concat b1 b2))))
  (split_proof:(b:bytes{pre b} -> i:nat{Some? (split #bytes b i)} -> Lemma (pre (fst (Some?.v (split b i))) /\ pre (snd (Some?.v (split b i))))))
  (from_nat_proof:(sz:nat -> n:nat_lbytes sz -> Lemma (pre (from_nat sz n))))
  : squash (bytes_pre_is_compatible pre)
  =
  FStar.Classical.forall_intro_2 concat_proof;
  FStar.Classical.forall_intro_2 split_proof;
  FStar.Classical.forall_intro_2 from_nat_proof

type bytes_compatible_pre (bytes:Type0) {|bytes_like bytes|} =
  pre:(bytes -> prop){bytes_pre_is_compatible pre}

let seq_u8_bytes_like: bytes_like (Seq.seq UInt8.t) = {
  length = Seq.length;

  empty = (Seq.empty);
  empty_length = (fun () -> ());
  recognize_empty = (fun b ->
    assert(Seq.length b = 0 ==> b `Seq.eq` Seq.empty);
    Seq.length b = 0
  );

  concat = (fun b1 b2 -> Seq.append b1 b2);
  concat_length = (fun b1 b2 -> ());

  split = (fun b i ->
    if i <= Seq.length b then
      Some (Seq.slice b 0 i, Seq.slice b i (Seq.length b))
    else
      None
  );

  split_length = (fun b i -> ());
  split_concat = (fun b1 b2 ->
    assert(b1 `Seq.eq` (Seq.slice (Seq.append b1 b2) 0 (Seq.length b1)));
    assert(b2 `Seq.eq` (Seq.slice (Seq.append b1 b2) (Seq.length b1) (Seq.length (Seq.append b1 b2))))
  );
  concat_split = (fun b i ->
    if i <= Seq.length b then
      assert(b `Seq.eq` Seq.append (Seq.slice b 0 i) (Seq.slice b i (Seq.length b)))
    else ()
  );

  to_nat = (fun b ->
    FStar.Endianness.lemma_be_to_n_is_bounded b;
    Some (FStar.Endianness.be_to_n b)
  );
  from_nat = (fun sz n ->
    FStar.Endianness.n_to_be sz n
  );

  from_to_nat = (fun sz n -> ());
  to_from_nat = (fun b -> ());
}

let refine_bytes_like (bytes:Type0) {|bytes_like bytes|} (pre:bytes_compatible_pre bytes): bytes_like (b:bytes{pre b}) = {
  length = (fun (b:bytes{pre b}) -> length #bytes b);

  empty = empty #bytes;
  empty_length = (fun () -> empty_length #bytes ());
  recognize_empty = (fun b -> recognize_empty #bytes b);

  concat = (fun b1 b2 -> concat #bytes b1 b2);
  concat_length = (fun b1 b2 -> concat_length #bytes b1 b2);

  split = (fun b i ->
    match split #bytes b i with
    | None -> None
    | Some (b1, b2) -> Some (b1, b2)
  );
  split_length = (fun b i -> split_length #bytes b i);

  split_concat = (fun b1 b2 -> split_concat #bytes b1 b2);
  concat_split = (fun b i -> concat_split #bytes b i);

  to_nat = (fun b -> to_nat #bytes b);
  from_nat = (fun sz n -> from_nat #bytes sz n);

  from_to_nat = (fun sz n -> from_to_nat #bytes sz n);
  to_from_nat = (fun b -> to_from_nat #bytes b);
}
