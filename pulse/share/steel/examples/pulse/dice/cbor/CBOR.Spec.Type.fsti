module CBOR.Spec.Type
include CBOR.Spec.Constants

module U8 = FStar.UInt8
module U64 = FStar.UInt64

(* Simple values *)

[@@CMacro]
let min_simple_value_long_argument = 32uy

[@@CMacro]
let max_simple_value_additional_info = 23uy

inline_for_extraction
noextract
let simple_value_wf
  (x: U8.t)
: Tot bool
= x `U8.lte` max_simple_value_additional_info || min_simple_value_long_argument `U8.lte` x

inline_for_extraction
noextract
let simple_value : eqtype =
  (x: U8.t { simple_value_wf x == true } )

(* Raw data items, disregarding ordering of map entries *)

noextract
noeq
type raw_data_item
= | Simple: (v: simple_value) -> raw_data_item
  | Int64: (typ: major_type_uint64_or_neg_int64) -> (v: U64.t) -> raw_data_item
  | String: (typ: major_type_byte_string_or_text_string) -> (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n }) -> raw_data_item // Section 3.1: "a string containing an invalid UTF-8 sequence is well-formed but invalid", so we don't care about UTF-8 specifics here.
  | Array: (v: list raw_data_item { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
  | Map: (v: list (raw_data_item & raw_data_item) { FStar.UInt.fits (List.Tot.length v) U64.n }) -> raw_data_item
  | Tagged: (tag: U64.t) -> (v: raw_data_item) -> raw_data_item
//  | Float: (v: Float.float) -> raw_data_item // TODO

noextract
let get_major_type
  (d: raw_data_item)
: Tot major_type_t
= match d with
  | Simple _ -> major_type_simple_value
  | Int64 m _ -> m
  | String m _ -> m
  | Array _ -> major_type_array
  | Map _ -> major_type_map
  | Tagged _ _ -> major_type_tagged

noextract
val holds_on_raw_data_item
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool

noextract
let holds_on_pair
  (#t: Type)
  (pred: (t -> bool))
  (x: (t & t))
: Tot bool
= let (x1, x2) = x in
  pred x1 && pred x2

noextract
let holds_on_raw_data_item'
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Tot bool
= p x &&
  begin match x with
  | Array l -> List.Tot.for_all (holds_on_raw_data_item p) l
  | Map l ->
    List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) l
  | Tagged _ v -> holds_on_raw_data_item p v
  | _ -> true
  end

val holds_on_raw_data_item_eq
  (p: (raw_data_item -> bool))
  (x: raw_data_item)
: Lemma
  (holds_on_raw_data_item p x == holds_on_raw_data_item' p x)

let holds_on_raw_data_item_eq_simple
  (p: (raw_data_item -> bool))
  (v: simple_value)
: Lemma
  (holds_on_raw_data_item p (Simple v) == p (Simple v))
  [SMTPat (holds_on_raw_data_item p (Simple v))]
= holds_on_raw_data_item_eq p (Simple v)

let holds_on_raw_data_item_eq_int64
  (p: (raw_data_item -> bool))
  (typ: major_type_uint64_or_neg_int64)
  (v: U64.t)
: Lemma
  (holds_on_raw_data_item p (Int64 typ v) == p (Int64 typ v))
  [SMTPat (holds_on_raw_data_item p (Int64 typ v))]
= holds_on_raw_data_item_eq p (Int64 typ v)

let holds_on_raw_data_item_eq_string
  (p: (raw_data_item -> bool))
  (typ: major_type_byte_string_or_text_string)
  (v: Seq.seq U8.t { FStar.UInt.fits (Seq.length v) U64.n })
: Lemma
  (holds_on_raw_data_item p (String typ v) == p (String typ v))
  [SMTPat (holds_on_raw_data_item p (String typ v))]
= holds_on_raw_data_item_eq p (String typ v)

let holds_on_raw_data_item_eq_array
  (p: (raw_data_item -> bool))
  (v: list raw_data_item { FStar.UInt.fits (List.Tot.length v) U64.n })
: Lemma
  (holds_on_raw_data_item p (Array v) == (p (Array v) && List.Tot.for_all (holds_on_raw_data_item p) v))
  [SMTPat (holds_on_raw_data_item p (Array v))]
= holds_on_raw_data_item_eq p (Array v)

let holds_on_raw_data_item_eq_map
  (p: (raw_data_item -> bool))
  (v: list (raw_data_item & raw_data_item) { FStar.UInt.fits (List.Tot.length v) U64.n })
: Lemma
  (holds_on_raw_data_item p (Map v) == (p (Map v) && List.Tot.for_all (holds_on_pair (holds_on_raw_data_item p)) v))
  [SMTPat (holds_on_raw_data_item p (Map v))]
= holds_on_raw_data_item_eq p (Map v)

let holds_on_raw_data_item_eq_tagged
  (p: (raw_data_item -> bool))
  (tag: U64.t)
  (v: raw_data_item)
: Lemma
  (holds_on_raw_data_item p (Tagged tag v) <==> (p (Tagged tag v) && holds_on_raw_data_item p v))
  [SMTPat (holds_on_raw_data_item p (Tagged tag v))]
= holds_on_raw_data_item_eq p (Tagged tag v)

noextract
let map_entry_order
  (#key: Type)
  (key_order: (key -> key -> bool))
  (value: Type)
  (m1: (key & value))
  (m2: (key & value))
: Tot bool
= key_order (fst m1) (fst m2)

noextract
let data_item_wf_head (order: (raw_data_item -> raw_data_item -> bool)) (x: raw_data_item) : Tot bool
= match x with
  | Map l ->
      FStar.List.Tot.sorted (map_entry_order order _) l
  | _ -> true

noextract
let data_item_wf (order: (raw_data_item -> raw_data_item -> bool)) : Tot (raw_data_item -> bool)
= holds_on_raw_data_item (data_item_wf_head order)

let data_item (order: (raw_data_item -> raw_data_item -> bool)) =
  (x: raw_data_item { data_item_wf order x == true })
