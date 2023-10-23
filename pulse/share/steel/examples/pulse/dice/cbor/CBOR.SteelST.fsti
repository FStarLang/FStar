module CBOR.SteelST
open Steel.ST.Util

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Steel.ST.Reference
module A = Steel.ST.Array
module SM = Steel.ST.SeqMatch

(* The C datatype for CBOR objects *)

noeq
type cbor_int = {
  cbor_int_type: Cbor.major_type_uint64_or_neg_int64;
  cbor_int_value: U64.t;
}

noeq
type cbor_string = {
  cbor_string_type: Cbor.major_type_byte_string_or_text_string;
  cbor_string_length: U64.t;
  cbor_string_payload: A.array U8.t;
  permission: perm; // ghost
}

inline_for_extraction
noextract
val cbor_serialized_payload_t: Type0 // extracted as uint8_t*

[@@erasable]
val cbor_serialized_footprint_t: Type0

noeq
type cbor_serialized = {
  cbor_serialized_size: SZ.t;
  cbor_serialized_payload: cbor_serialized_payload_t;
  footprint: cbor_serialized_footprint_t; // ghost
}

noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: R.ref cbor;
  footprint: Ghost.erased cbor; // ghost
}

and cbor_array = {
  cbor_array_length: U64.t;
  cbor_array_payload: A.array cbor;
  footprint: Ghost.erased (Seq.seq cbor); // ghost
}

and cbor_map_entry = {
  cbor_map_entry_key: cbor;
  cbor_map_entry_value: cbor;
}

and cbor_map = {
  cbor_map_length: U64.t;
  cbor_map_payload: A.array cbor_map_entry;
  footprint: Ghost.erased (Seq.seq cbor_map_entry); // ghost
}

and cbor =
| CBOR_Case_Int64 of cbor_int
| CBOR_Case_String of cbor_string
| CBOR_Case_Tagged of cbor_tagged
| CBOR_Case_Array of cbor_array
| CBOR_Case_Map of cbor_map
| CBOR_Case_Simple_value of Cbor.simple_value
| CBOR_Case_Serialized of cbor_serialized

inline_for_extraction
noextract
let dummy_cbor : cbor = CBOR_Case_Simple_value 0uy

(* Relating a CBOR C object with a CBOR high-level value *)

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

[@@__reduce__]
let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match c1.cbor_map_entry_key (fstp v1) `star`
  raw_data_item_match c1.cbor_map_entry_value (sndp v1)

val raw_data_item_match
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop

let raw_data_item_array_match
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
  (decreases v)
= SM.seq_list_match c v raw_data_item_match

[@@__reduce__]
let raw_data_item_map_entry_match
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 raw_data_item_match

let raw_data_item_map_match
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= SM.seq_list_match c v raw_data_item_map_entry_match

val raw_data_item_match_get_case
  (#opened: _)
  (#v: Cbor.raw_data_item)
  (c: cbor)
: STGhost unit opened
    (raw_data_item_match c v)
    (fun _ -> raw_data_item_match c v)
    True
    (fun _ -> match c, v with
    | CBOR_Case_Serialized _, _
    | CBOR_Case_Array _, Cbor.Array _
    | CBOR_Case_Int64 _, Cbor.Int64 _ _
    | CBOR_Case_Map _, Cbor.Map _
    | CBOR_Case_Simple_value _, Cbor.Simple _
    | CBOR_Case_String _, Cbor.String _ _
    | CBOR_Case_Tagged _, Cbor.Tagged _ _
      -> True
    | _ -> False
    )

(* Parsing *)

noeq
type read_cbor_success_t = {
  read_cbor_payload: cbor;
  read_cbor_remainder: A.array U8.t;
  read_cbor_remainder_length: SZ.t;
}

noeq
type read_cbor_t =
| ParseError
| ParseSuccess of read_cbor_success_t

noextract
let read_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= SZ.v c.read_cbor_remainder_length == Seq.length rem /\
  va `Seq.equal` (Cbor.serialize_cbor v `Seq.append` rem)

[@@__reduce__]
let read_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match c.read_cbor_payload v `star`
    A.pts_to c.read_cbor_remainder p rem `star`
    ((raw_data_item_match c.read_cbor_payload v `star` A.pts_to c.read_cbor_remainder p rem) `implies_`
      A.pts_to a p va) `star`
    pure (read_cbor_success_postcond va c v rem)
  ))

noextract
let read_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v . ~ (Cbor.serialize_cbor v == Seq.slice va 0 (min (Seq.length (Cbor.serialize_cbor v)) (Seq.length va)))

[@@__reduce__]
let read_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a p va `star` pure (read_cbor_error_postcond va)

let read_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_cbor_error_post a p va
  | ParseSuccess c -> read_cbor_success_post a p va c

val read_cbor
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (a: A.array U8.t)
  (sz: SZ.t)
: ST read_cbor_t
    (A.pts_to a p va)
    (fun res -> read_cbor_post a p va res)
    (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    (fun _ -> True)

(* Destructors and constructors *)

val destr_cbor_int64
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST cbor_int
    (raw_data_item_match c (Ghost.reveal va))
    (fun _ -> raw_data_item_match c (Ghost.reveal va))
    (Cbor.Int64? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Int64 c'.cbor_int_type c'.cbor_int_value /\
      (CBOR_Case_Int64? c ==> c == CBOR_Case_Int64 c')
    )

val constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Int64 ty value))
    True
    (fun c -> c == CBOR_Case_Int64 ({ cbor_int_type = ty; cbor_int_value = value }))

val destr_cbor_simple_value
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
: ST Cbor.simple_value
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' ->
      raw_data_item_match c (Ghost.reveal va)
    )
    (Cbor.Simple? (Ghost.reveal va))
    (fun c' ->
      Ghost.reveal va == Cbor.Simple c' /\
      (CBOR_Case_Simple_value? c ==> c == CBOR_Case_Simple_value c')
    )

val constr_cbor_simple_value
  (value: Cbor.simple_value)
: ST cbor
    emp
    (fun c -> raw_data_item_match c (Cbor.Simple value))
    True
    (fun c -> c == CBOR_Case_Simple_value value)

val destr_cbor_string
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor {Cbor.String? va})
: STT cbor_string
    (raw_data_item_match c (Ghost.reveal va))
    (fun c' -> exists_ (fun vc' ->
      A.pts_to c'.cbor_string_payload c'.permission vc' `star`
      (A.pts_to c'.cbor_string_payload c'.permission vc' `implies_` raw_data_item_match c (Ghost.reveal va)) `star`
      pure (
        U64.v c'.cbor_string_length == Seq.length vc' /\
        c'.cbor_string_type == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    )))

val constr_cbor_string
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t {
    U64.v len == Seq.length va
  })
: ST cbor
    (A.pts_to a p va)
    (fun c' ->
      raw_data_item_match c' (Cbor.String typ va) `star`
      (raw_data_item_match c' (Cbor.String typ va) `implies_`
        A.pts_to a p va
      )
    )
    True
    (fun c' -> c' == CBOR_Case_String ({
      cbor_string_type = typ;
      cbor_string_length = len;
      cbor_string_payload = a;
      permission = p;
    }))

val constr_cbor_array
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
  (a: A.array cbor)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: ST cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_array_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Array v') `star`
      (raw_data_item_match res (Cbor.Array v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_array_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Array ({
        cbor_array_payload = a;
        cbor_array_length = len;
        footprint = c';
      })
    )

[@@__reduce__]
let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

val destr_cbor_array
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_array
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.cbor_array_payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.cbor_array_payload full_perm res.footprint `star`
        raw_data_item_array_match res.footprint (maybe_cbor_array v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Array? a)
    (fun res ->
      a == CBOR_Case_Array res /\
      Cbor.Array? v /\
      U64.v res.cbor_array_length == List.Tot.length (Cbor.Array?.v v)
    )

val cbor_array_length
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST U64.t
    (raw_data_item_match a v)
    (fun _ -> raw_data_item_match a v)
    (Cbor.Array? v)
    (fun res ->
      Cbor.Array? v /\
      U64.v res == List.Tot.length (Cbor.Array?.v v)
    )

val cbor_array_index
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (i: SZ.t {
    Cbor.Array? v /\
    SZ.v i < List.Tot.length (Cbor.Array?.v v)
  })
: STT cbor
    (raw_data_item_match a v)
    (fun a' ->
      raw_data_item_match a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `star`
      (raw_data_item_match a' (List.Tot.index (Cbor.Array?.v v) (SZ.v i)) `implies_`
        raw_data_item_match a v)
    )

noeq
type cbor_array_iterator_payload_t =
| CBOR_Array_Iterator_Payload_Array:
    payload: A.array cbor ->
    footprint: Ghost.erased (Seq.seq cbor) ->
    cbor_array_iterator_payload_t
| CBOR_Array_Iterator_Payload_Serialized:
    payload: cbor_serialized_payload_t ->
    footprint: cbor_serialized_footprint_t ->
    cbor_array_iterator_payload_t

// NOTE: this type could be made abstract (with val and
// CAbstractStruct, and then hiding cbor_array_iterator_payload_t
// altogether), but then, users couldn't allocate on stack
noeq
type cbor_array_iterator_t = {
  cbor_array_iterator_length: U64.t;
  cbor_array_iterator_payload: cbor_array_iterator_payload_t;
}

val dummy_cbor_array_iterator: cbor_array_iterator_t

val cbor_array_iterator_match
  (i: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop

val cbor_array_iterator_init
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor { Cbor.Array? v })
: STT cbor_array_iterator_t
    (raw_data_item_match a v)
    (fun i ->
      cbor_array_iterator_match i (Cbor.Array?.v v) `star`
      (cbor_array_iterator_match i (Cbor.Array?.v v) `implies_`
        raw_data_item_match a v)
    )

val cbor_array_iterator_is_done
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (i: cbor_array_iterator_t)
: ST bool
    (cbor_array_iterator_match i l)
    (fun _ -> cbor_array_iterator_match i l)
    True
    (fun res -> res == Nil? l)

val cbor_array_iterator_next
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i: Ghost.erased cbor_array_iterator_t)
  (pi: R.ref cbor_array_iterator_t { Cons? l })
: STT cbor
    (R.pts_to pi full_perm i `star` cbor_array_iterator_match i l)
    (fun c -> exists_ (fun i' ->
      R.pts_to pi full_perm i' `star`
      raw_data_item_match c (List.Tot.hd l) `star`
      cbor_array_iterator_match i' (List.Tot.tl l) `star`
      ((raw_data_item_match c (List.Tot.hd l) `star`
        cbor_array_iterator_match i' (List.Tot.tl l)) `implies_`
        cbor_array_iterator_match i l
      )
    ))

val read_cbor_array
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (#vdest: Ghost.erased (Seq.seq cbor))
  (dest: A.array cbor) // it is the user's responsibility to allocate the array properly
  (len: U64.t)
: ST cbor_array
    (raw_data_item_match a v `star`
      A.pts_to dest full_perm vdest
    )
    (fun res ->
      A.pts_to res.cbor_array_payload full_perm res.footprint `star`
      raw_data_item_array_match res.footprint (maybe_cbor_array v) `star`
      ((A.pts_to res.cbor_array_payload full_perm res.footprint `star`
        raw_data_item_array_match res.footprint (maybe_cbor_array v)) `implies_` (
        raw_data_item_match a v `star`
        (exists_ (A.pts_to dest full_perm))
      ))
    )
    (Cbor.Array? v /\
      (U64.v len == A.length dest \/ U64.v len == Seq.length vdest) /\
      U64.v len == List.Tot.length (Cbor.Array?.v v)
    )
    (fun res ->
      Cbor.Array? v /\
      res.cbor_array_length == len /\
      U64.v len == A.length dest /\
      U64.v len == A.length res.cbor_array_payload /\
      U64.v len == Seq.length res.footprint /\
      (if CBOR_Case_Array? a
      then a == CBOR_Case_Array res
      else res.cbor_array_payload == dest
      )
    )

[@@__reduce__]
let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

let dummy_raw_data_item : Ghost.erased Cbor.raw_data_item =
  Cbor.Int64 Cbor.major_type_uint64 0uL

[@@__reduce__]
let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> dummy_raw_data_item

val destr_cbor_tagged
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_tagged
    (raw_data_item_match a v)
    (fun res ->
      R.pts_to res.cbor_tagged_payload full_perm res.footprint `star`
      raw_data_item_match res.footprint (maybe_cbor_tagged_payload v) `star`
      ((R.pts_to res.cbor_tagged_payload full_perm res.footprint `star`
        raw_data_item_match res.footprint (maybe_cbor_tagged_payload v)) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Tagged? a)
    (fun res ->
      a == CBOR_Case_Tagged res /\
      Cbor.Tagged? v /\
      res.cbor_tagged_tag == Cbor.Tagged?.tag v
    )

val constr_cbor_tagged
  (#c': Ghost.erased (cbor))
  (#v': Ghost.erased (Cbor.raw_data_item))
  (tag: U64.t)
  (a: R.ref cbor)
: ST cbor
    (R.pts_to a full_perm c' `star`
      raw_data_item_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Tagged tag v') `star`
      (raw_data_item_match res (Cbor.Tagged tag v') `implies_`
        (R.pts_to a full_perm c' `star`
          raw_data_item_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Tagged ({
        cbor_tagged_tag = tag;
        cbor_tagged_payload = a;
        footprint = c';
      })
    )

val read_cbor_tagged
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
  (#vdest: Ghost.erased (cbor))
  (dest: R.ref cbor) // it is the user's responsibility to allocate the reference properly (maybe on the stack)
: ST cbor_tagged
    (raw_data_item_match a v `star`
      R.pts_to dest full_perm vdest
    )
    (fun res ->
      R.pts_to res.cbor_tagged_payload full_perm res.footprint `star`
      raw_data_item_match res.footprint (maybe_cbor_tagged_payload v) `star`
      ((R.pts_to res.cbor_tagged_payload full_perm res.footprint `star`
        raw_data_item_match res.footprint (maybe_cbor_tagged_payload v)) `implies_` (
        raw_data_item_match a v `star`
        (exists_ (R.pts_to dest full_perm))
      ))
    )
    (Cbor.Tagged? v)
    (fun res ->
      Cbor.Tagged? v /\
      Cbor.Tagged?.tag v == res.cbor_tagged_tag /\
      (if CBOR_Case_Tagged? a
      then a == CBOR_Case_Tagged res
      else res.cbor_tagged_payload == dest
      )
    )

[@@__reduce__]
let maybe_cbor_map
  (v: Cbor.raw_data_item)
: GTot (list (Cbor.raw_data_item & Cbor.raw_data_item))
= match v with
  | Cbor.Map l -> l
  | _ -> []

val destr_cbor_map
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST cbor_map
    (raw_data_item_match a v)
    (fun res ->
      A.pts_to res.cbor_map_payload full_perm res.footprint `star`
      SM.seq_list_match res.footprint (maybe_cbor_map v) raw_data_item_map_entry_match `star`
      ((A.pts_to res.cbor_map_payload full_perm res.footprint `star`
        SM.seq_list_match res.footprint (maybe_cbor_map v) raw_data_item_map_entry_match) `implies_`
        raw_data_item_match a v
      )
    )
    (CBOR_Case_Map? a)
    (fun res ->
      a == CBOR_Case_Map res /\
      Cbor.Map? v /\
      U64.v res.cbor_map_length == List.Tot.length (Cbor.Map?.v v)
    )

val constr_cbor_map
  (#c': Ghost.erased (Seq.seq cbor_map_entry))
  (#v': Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
  (a: A.array cbor_map_entry)
  (len: U64.t {
    U64.v len == List.Tot.length v'
  })
: ST cbor
    (A.pts_to a full_perm c' `star`
      raw_data_item_map_match c' v')
    (fun res ->
      raw_data_item_match res (Cbor.Map v') `star`
      (raw_data_item_match res (Cbor.Map v') `implies_`
        (A.pts_to a full_perm c' `star`
          raw_data_item_map_match c' v')
      )
    )
    True
    (fun res ->
      res == CBOR_Case_Map ({
        cbor_map_payload = a;
        cbor_map_length = len;
        footprint = c';
      })
    )

val cbor_get_major_type
  (#v: Ghost.erased Cbor.raw_data_item)
  (a: cbor)
: ST Cbor.major_type_t
    (raw_data_item_match a v)
    (fun _ -> raw_data_item_match a v)
    True
    (fun res -> res == Cbor.get_major_type v)

val cbor_is_equal
  (#v1: Ghost.erased Cbor.raw_data_item)
  (a1: cbor)
  (#v2: Ghost.erased Cbor.raw_data_item)
  (a2: cbor)
: ST bool
    (raw_data_item_match a1 v1 `star` raw_data_item_match a2 v2)
    (fun _ -> raw_data_item_match a1 v1 `star` raw_data_item_match a2 v2)
    True
    (fun res -> (~ (Cbor.Tagged? v1 \/ Cbor.Array? v1 \/ Cbor.Map? v1)) ==> (res == true <==> v1 == v2)) // TODO: underspecified for tagged, arrays and maps, complete those missing cases

noeq
type cbor_map_get_t =
| Found of cbor
| NotFound

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

[@@__reduce__]
let cbor_map_get_post_not_found
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item { Cbor.Map? vmap })
  (map: cbor)
: Tot vprop
= raw_data_item_match map vmap `star` pure (list_ghost_assoc vkey (Cbor.Map?.v vmap) == None)

[@@__reduce__]
let cbor_map_get_post_found
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item { Cbor.Map? vmap })
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists_ (fun vvalue ->
    raw_data_item_match value vvalue `star`
    (raw_data_item_match value vvalue `implies_` raw_data_item_match map vmap) `star`
    pure (list_ghost_assoc vkey (Cbor.Map?.v vmap) == Some vvalue)
  )

let cbor_map_get_post
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_post_not_found vkey vmap map
  | Found value -> cbor_map_get_post_found vkey vmap map value

val cbor_map_get
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (key: cbor)
  (#vmap: Ghost.erased Cbor.raw_data_item)
  (map: cbor { Cbor.Map? vmap })
: ST cbor_map_get_t
    (raw_data_item_match key vkey `star` raw_data_item_match map vmap)
    (fun res -> raw_data_item_match key vkey `star` cbor_map_get_post vkey vmap map res)
    (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey))
    (fun res -> Found? res == Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap)))

(* Serialization *)

noextract
let write_cbor_postcond
  (va: Cbor.raw_data_item)
  (out: A.array U8.t)
  (vout': Seq.seq U8.t)
  (res: SZ.t)
: Tot prop
= let s = Cbor.serialize_cbor va in
  Seq.length vout' == A.length out /\
  (res = 0sz <==> Seq.length s > Seq.length vout') /\
  (res <> 0sz ==> (
    SZ.v res == Seq.length s /\
    Seq.slice vout' 0 (Seq.length s) `Seq.equal` s
  ))

[@@__reduce__]
let write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (res: SZ.t)
  (vout': Seq.seq U8.t)
: Tot vprop
= 
  A.pts_to out full_perm vout' `star`
  pure (write_cbor_postcond va out vout' res)

val write_cbor
  (#va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (#vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (sz: SZ.t)
: ST SZ.t
    (raw_data_item_match c (Ghost.reveal va) `star`
      A.pts_to out full_perm vout
    )
    (fun res -> 
      raw_data_item_match c (Ghost.reveal va) `star`
      exists_ (write_cbor_post va c vout out res)
    )
    (SZ.v sz == A.length out)
    (fun _ -> True)
