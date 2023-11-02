module CBOR.Spec
include CBOR.Spec.Type

module U8 = FStar.UInt8

(* Data format specification *)

val serialize_cbor
  (c: raw_data_item)
: GTot (Seq.seq U8.t)

val serialize_cbor_inj
  (c1 c2: raw_data_item)
  (s1 s2: Seq.seq U8.t)
: Lemma
  (requires (serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2))
  (ensures (c1 == c2 /\ s1 == s2))

let serialize_cbor_inj'
  (c1: raw_data_item)
  (s1: Seq.seq U8.t)
: Lemma
  (forall c2 s2 . serialize_cbor c1 `Seq.append` s1 == serialize_cbor c2 `Seq.append` s2 ==> (c1 == c2 /\ s1 == s2))
= Classical.forall_intro_2 (fun c2 s2 ->
    Classical.move_requires (serialize_cbor_inj c1 c2 s1) s2
  )

let serialize_cbor_with_test_correct
  (c: raw_data_item)
  (suff: Seq.seq U8.t)
  (p: (raw_data_item -> Seq.seq U8.t -> prop))
: Lemma
  (requires (
    ~ (p c suff)
  ))
  (ensures (
    forall (c': raw_data_item) (suff': Seq.seq U8.t) .
    serialize_cbor c `Seq.append` suff == serialize_cbor c' `Seq.append` suff' ==> ~ (p c' suff'))
  )
= Classical.forall_intro_2 (fun c' suff' ->
    Classical.move_requires (serialize_cbor_inj c c' suff) suff'
  )

val serialize_cbor_nonempty
  (c: raw_data_item)
: Lemma
  (Seq.length (serialize_cbor c) > 0)

(* 4.2.1 Deterministically encoded CBOR: The keys in every map MUST be sorted in the bytewise lexicographic order of their deterministic encodings. *)

val deterministically_encoded_cbor_map_key_order : Ghost.erased (raw_data_item -> raw_data_item -> bool)

val deterministically_encoded_cbor_map_key_order_irrefl
  (x: raw_data_item)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order x x == false)
  [SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order x x)]

val deterministically_encoded_cbor_map_key_order_trans
  (x y z: raw_data_item)
: Lemma
  (requires (Ghost.reveal deterministically_encoded_cbor_map_key_order x y == true /\ Ghost.reveal deterministically_encoded_cbor_map_key_order y z == true))
  (ensures (Ghost.reveal deterministically_encoded_cbor_map_key_order x z == true))
  [SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order x y); SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order y z)]

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

val deterministically_encoded_cbor_map_key_order_assoc_ext :
  (m1: list (raw_data_item & raw_data_item)) ->
  (m2: list (raw_data_item & raw_data_item)) ->
  (ext: (
    (k: raw_data_item) ->
    Lemma
    (list_ghost_assoc k m1 == list_ghost_assoc k m2)
  )) ->
  Lemma
  (requires (List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m1 /\ List.Tot.sorted (map_entry_order deterministically_encoded_cbor_map_key_order _) m2))
  (ensures (m1 == m2))

module U64 = FStar.UInt64

val deterministically_encoded_cbor_map_key_order_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    U8.v (get_major_type v1) < U8.v (get_major_type v2)
  ))
  (ensures (
    Ghost.reveal deterministically_encoded_cbor_map_key_order v1 v2 == true
  ))

val deterministically_encoded_cbor_map_key_order_int64
  (ty: major_type_uint64_or_neg_int64)
  (v1 v2: U64.t)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2) == U64.lt v1 v2)
  [SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2))]
