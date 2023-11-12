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

(* Comparisons with unserialized values *)

module U64 = FStar.UInt64

noextract [@@noextract_to "krml"]
let int_compare (x1 x2: int) : Tot int =
  if x1 < x2
  then -1
  else if x1 = x2
  then 0
  else 1

noextract [@@noextract_to "krml"]
let rec bytes_lex_compare
  (s1 s2: Seq.seq U8.t)
: Tot int
  (decreases (Seq.length s1))
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then int_compare (Seq.length s1) (Seq.length s2)
  else
    let c = int_compare (U8.v (Seq.index s1 0)) (U8.v (Seq.index s2 0)) in
    if c = 0
    then bytes_lex_compare (Seq.tail s1) (Seq.tail s2)
    else c

let rec bytes_lex_compare_values
  (s1 s2: Seq.seq U8.t)
: Lemma
  (ensures (let c = bytes_lex_compare s1 s2 in
    c == -1 \/ c == 0 \/ c == 1))
  (decreases (Seq.length s1))
  [SMTPat (bytes_lex_compare s1 s2)]
= if Seq.length s1 = 0 || Seq.length s2 = 0
  then ()
  else bytes_lex_compare_values (Seq.tail s1) (Seq.tail s2)

val bytes_lex_compare_equal
  (s1 s2: Seq.seq U8.t)
: Lemma
  (bytes_lex_compare s1 s2 == 0 <==> s1 == s2)

val deterministically_encoded_cbor_map_key_order_spec
  (x1 x2: raw_data_item)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order x1 x2 == (bytes_lex_compare (serialize_cbor x1) (serialize_cbor x2) < 0))

noextract [@@noextract_to "krml"]
let rec cbor_compare
  (x1 x2: raw_data_item)
: Tot int
  (decreases x1)
= let ty1 = get_major_type x1 in
  let ty2 = get_major_type x2 in
  let c = int_compare (U8.v ty1) (U8.v ty2) in
  if c <> 0
  then c
  else if ty1 = major_type_uint64 || ty1 = major_type_neg_int64
  then int_compare (U64.v (Int64?.v x1)) (U64.v (Int64?.v x2))
  else if ty1 = major_type_simple_value
  then int_compare (U8.v (Simple?.v x1)) (U8.v (Simple?.v x2))
  else if ty1 = major_type_byte_string || ty1 = major_type_text_string
  then
    let c = int_compare (Seq.length (String?.v x1)) (Seq.length (String?.v x2)) in
    if c <> 0
    then c
    else bytes_lex_compare (String?.v x1) (String?.v x2)
  else if ty1 = major_type_tagged
  then
    let c = int_compare (U64.v (Tagged?.tag x1)) (U64.v (Tagged?.tag x2)) in
    if c <> 0
    then c
    else cbor_compare (Tagged?.v x1) (Tagged?.v x2)
  else if ty1 = major_type_array
  then
    let c = int_compare (List.Tot.length (Array?.v x1)) (List.Tot.length (Array?.v x2)) in
    if c <> 0
    then c
    else cbor_compare_array (Array?.v x1) (Array?.v x2)
  else if ty1 = major_type_map
  then
    let c = int_compare (List.Tot.length (Map?.v x1)) (List.Tot.length (Map?.v x2)) in
    if c <> 0
    then c
    else cbor_compare_map (Map?.v x1) (Map?.v x2)
  else false_elim ()

and cbor_compare_array
  (x1 x2: list raw_data_item)
: Pure int
    (requires (List.Tot.length x1 == List.Tot.length x2))
    (ensures (fun _ -> True))
    (decreases x1)
= match x1, x2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare a1 a2 in
    if c <> 0
    then c
    else cbor_compare_array q1 q2

and cbor_compare_map
  (x1 x2: list (raw_data_item & raw_data_item))
: Pure int
    (requires (List.Tot.length x1 == List.Tot.length x2))
    (ensures (fun _ -> True))
    (decreases x1)
= match x1, x2 with
  | [], [] -> 0
  | a1 :: q1, a2 :: q2 ->
    let c = cbor_compare (fst a1) (fst a2) in
    if c <> 0
    then c
    else
      let c = cbor_compare (snd a1) (snd a2) in
      if c <> 0
      then c
      else cbor_compare_map q1 q2

val cbor_compare_correct
  (x1 x2: raw_data_item)
: Lemma
  (ensures (cbor_compare x1 x2 == bytes_lex_compare (serialize_cbor x1) (serialize_cbor x2)))

let cbor_compare_equal
  (x1 x2: raw_data_item)
: Lemma
  (cbor_compare x1 x2 == 0 <==> x1 == x2)
= cbor_compare_correct x1 x2;
  bytes_lex_compare_equal (serialize_cbor x1) (serialize_cbor x2);
  Seq.append_empty_r (serialize_cbor x1);
  Seq.append_empty_r (serialize_cbor x2);
  Classical.move_requires (serialize_cbor_inj x1 x2 Seq.empty) Seq.empty

let deterministically_encoded_cbor_map_key_order_major_type_intro
  (v1 v2: raw_data_item)
: Lemma
  (requires (
    U8.v (get_major_type v1) < U8.v (get_major_type v2)
  ))
  (ensures (
    Ghost.reveal deterministically_encoded_cbor_map_key_order v1 v2 == true
  ))
= deterministically_encoded_cbor_map_key_order_spec v1 v2;
  cbor_compare_correct v1 v2

let deterministically_encoded_cbor_map_key_order_int64
  (ty: major_type_uint64_or_neg_int64)
  (v1 v2: U64.t)
: Lemma
  (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2) == U64.lt v1 v2)
  [SMTPat (Ghost.reveal deterministically_encoded_cbor_map_key_order (Int64 ty v1) (Int64 ty v2))]
= deterministically_encoded_cbor_map_key_order_spec (Int64 ty v1) (Int64 ty v2);
  cbor_compare_correct (Int64 ty v1) (Int64 ty v2)
