module CBOR.Pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module SM = Pulse.Lib.SeqMatch

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
}


val cbor_map_entry: Type0

val cbor: Type0

inline_for_extraction
noextract
val dummy_cbor : cbor

inline_for_extraction
noextract
val cbor_map_entry_key: cbor_map_entry -> cbor

inline_for_extraction
noextract
val cbor_map_entry_value: cbor_map_entry -> cbor

val cbor_map_entry_key_value_inj
  (m1 m2: cbor_map_entry)
: Lemma
  (requires (
    cbor_map_entry_key m1 == cbor_map_entry_key m2 /\
    cbor_map_entry_value m1 == cbor_map_entry_value m2
  ))
  (ensures (m1 == m2))
  [SMTPatOr [
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_key m1); SMTPat (cbor_map_entry_value m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_key m2)];
    [SMTPat (cbor_map_entry_value m1); SMTPat (cbor_map_entry_value m2)];
  ]]

inline_for_extraction
noextract
val mk_cbor_map_entry
  (key: cbor)
  (value: cbor)
: Pure cbor_map_entry
  (requires True)
  (ensures (fun res ->
    cbor_map_entry_key res == key /\
    cbor_map_entry_value res == value
  ))

(* Relating a CBOR C object with a CBOR high-level value *)

noextract
let fstp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a1 = fst x

noextract
let sndp (#a1 #a2: Type) (x: (a1 & a2)) : Tot a2 = snd x

let raw_data_item_map_entry_match1
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
  (raw_data_item_match: (cbor -> (v': Cbor.raw_data_item { v' << v1 }) -> vprop))
: Tot vprop
= raw_data_item_match (cbor_map_entry_key c1) (fstp v1) **
  raw_data_item_match (cbor_map_entry_value c1) (sndp v1)

val raw_data_item_match
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot vprop

let raw_data_item_array_match
  (p: perm)
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot vprop
= SM.seq_list_match c v (raw_data_item_match p)

let raw_data_item_map_entry_match
  (p: perm)
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
= raw_data_item_map_entry_match1 c1 v1 (raw_data_item_match p)

let raw_data_item_map_match
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot vprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_map_entry_match p)

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

let read_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v **
    A.pts_to c.read_cbor_remainder #p rem **
    ((raw_data_item_match full_perm c.read_cbor_payload v ** A.pts_to c.read_cbor_remainder #p rem) @==>
      A.pts_to a #p va) **
    pure (read_cbor_success_postcond va c v rem)
  ))

noextract
let read_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . ~ (Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff)

let read_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a #p va ** pure (read_cbor_error_postcond va)

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
  (a: A.array U8.t)
  (sz: SZ.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt read_cbor_t
    (A.pts_to a #p va ** pure (
      (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    ))
    (fun res -> read_cbor_post a p va res)

noextract
let read_deterministically_encoded_cbor_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= read_cbor_success_postcond va c v rem /\
  Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == true

let read_deterministically_encoded_cbor_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: read_cbor_success_t)
: Tot vprop
= exists_ (fun v -> exists_ (fun rem ->
    raw_data_item_match full_perm c.read_cbor_payload v **
    A.pts_to c.read_cbor_remainder #p rem **
    ((raw_data_item_match full_perm c.read_cbor_payload v ** A.pts_to c.read_cbor_remainder #p rem) @==>
      A.pts_to a #p va) **
    pure (read_deterministically_encoded_cbor_success_postcond va c v rem)
  ))

noextract
let read_deterministically_encoded_cbor_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff ==> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == false

let read_deterministically_encoded_cbor_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot vprop
= A.pts_to a #p va ** pure (read_deterministically_encoded_cbor_error_postcond va)

let read_deterministically_encoded_cbor_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: read_cbor_t)
: Tot vprop
= match res with
  | ParseError -> read_deterministically_encoded_cbor_error_post a p va
  | ParseSuccess c -> read_deterministically_encoded_cbor_success_post a p va c

val read_deterministically_encoded_cbor
  (a: A.array U8.t)
  (sz: SZ.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt read_cbor_t
    (A.pts_to a #p va ** pure (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a))
    (fun res -> read_deterministically_encoded_cbor_post a p va res)

(* Destructors and constructors *)

val destr_cbor_int64
  (c: cbor)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
: stt cbor_int
    (raw_data_item_match p c (Ghost.reveal va) ** pure (
      (Cbor.Int64? (Ghost.reveal va))
    ))
    (fun c' -> raw_data_item_match p c (Ghost.reveal va) ** pure (
      Ghost.reveal va == Cbor.Int64 c'.cbor_int_type c'.cbor_int_value
    ))

val constr_cbor_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: stt cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Int64 ty value))

val destr_cbor_simple_value
  (c: cbor)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
: stt Cbor.simple_value
    (raw_data_item_match p c (Ghost.reveal va) ** pure (
      (Cbor.Simple? (Ghost.reveal va))
    ))
    (fun c' ->
      raw_data_item_match p c (Ghost.reveal va) ** pure (
      Ghost.reveal va == Cbor.Simple c'
    ))

val constr_cbor_simple_value
  (value: Cbor.simple_value)
: stt cbor
    emp
    (fun c -> raw_data_item_match full_perm c (Cbor.Simple value))

val destr_cbor_string
  (c: cbor)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
: stt cbor_string
    (raw_data_item_match p c (Ghost.reveal va) ** pure (
      Cbor.String? va
    ))
    (fun c' -> exists_ (fun vc' -> exists_ (fun p'->
      A.pts_to c'.cbor_string_payload #p' vc' **
      (A.pts_to c'.cbor_string_payload #p' vc' @==> raw_data_item_match p c (Ghost.reveal va)) **
      pure (
        Cbor.String? va /\
        U64.v c'.cbor_string_length == Seq.length vc' /\
        c'.cbor_string_type == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va
    ))))

val constr_cbor_string
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt cbor
    (A.pts_to a #p va ** pure (
      U64.v len == Seq.length va
    ))
    (fun c' -> exists_ (fun vc' ->
      raw_data_item_match full_perm c' vc' **
      (raw_data_item_match full_perm c' vc' @==>
        A.pts_to a #p va
      ) ** pure (
      U64.v len == Seq.length va /\
      vc' == Cbor.String typ va
    )))

val constr_cbor_array
  (a: A.array cbor)
  (len: U64.t)
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
: stt cbor
    (A.pts_to a c' **
      raw_data_item_array_match full_perm c' v' **
      pure (
        U64.v len == List.Tot.length v'
    ))
    (fun res -> exists_ (fun vres ->
      raw_data_item_match full_perm res vres **
      (raw_data_item_match full_perm res vres @==>
        (A.pts_to a c' **
          raw_data_item_array_match full_perm c' v')
      ) ** pure (
      U64.v len == List.Tot.length v' /\
      vres == Cbor.Array v'
    )))

let maybe_cbor_array
  (v: Cbor.raw_data_item)
: GTot (list Cbor.raw_data_item)
= match v with
  | Cbor.Array l -> l
  | _ -> []

val cbor_array_length
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt U64.t
    (raw_data_item_match p a v ** pure (
      (Cbor.Array? v)
    ))
    (fun res -> raw_data_item_match p a v ** pure (
      Cbor.Array? v /\
      U64.v res == List.Tot.length (Cbor.Array?.v v)
    ))

val cbor_array_index
  (a: cbor)
  (i: SZ.t)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt cbor
    (raw_data_item_match p a v ** pure (
      Cbor.Array? v /\
      SZ.v i < List.Tot.length (Cbor.Array?.v v)
    ))
    (fun a' -> exists_ (fun va' ->
      raw_data_item_match p a' va' **
      (raw_data_item_match p a' va' @==>
        raw_data_item_match p a v) **
      pure (
        Cbor.Array? v /\
        SZ.v i < List.Tot.length (Cbor.Array?.v v) /\
        va' == List.Tot.index (Cbor.Array?.v v) (SZ.v i)
    )))

val cbor_array_iterator_t: Type0

val dummy_cbor_array_iterator: cbor_array_iterator_t

val cbor_array_iterator_match
  (p: perm)
  (i: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot vprop

val cbor_array_iterator_init
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i -> exists_ (fun vi ->
      cbor_array_iterator_match p i vi **
      (cbor_array_iterator_match p i vi @==>
        raw_data_item_match p a v) **
      pure (
        Cbor.Array? v /\
        vi == Cbor.Array?.v v
    )))

val cbor_array_iterator_is_done
  (i: cbor_array_iterator_t)
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
: stt bool
    (cbor_array_iterator_match p i l)
    (fun res -> cbor_array_iterator_match p i l ** pure (
      res == Nil? l
    ))

val cbor_array_iterator_next
  (pi: R.ref cbor_array_iterator_t)
  (#p: perm)
  (#l: Ghost.erased (list Cbor.raw_data_item))
  (#i: Ghost.erased cbor_array_iterator_t)
: stt cbor
    (R.pts_to pi i ** cbor_array_iterator_match p i l **
      pure (Cons? l)
    )
    (fun c -> exists_ (fun i' -> exists_ (fun vc -> exists_ (fun vi' ->
      R.pts_to pi i' **
      raw_data_item_match p c vc **
      cbor_array_iterator_match p i' vi' **
      ((raw_data_item_match p c vc **
        cbor_array_iterator_match p i' vi') @==>
        cbor_array_iterator_match p i l
      ) ** pure (
      Ghost.reveal l == vc :: vi'
    )))))

val read_cbor_array
  (a: cbor)
  (dest: A.array cbor) // it is the user's responsibility to allocate the array properly
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (#vdest: Ghost.erased (Seq.seq cbor))
: stt (A.array cbor)
    (raw_data_item_match p a v **
      A.pts_to dest vdest **
      pure (
        (Cbor.Array? v /\
          (U64.v len == A.length dest \/ U64.v len == Seq.length vdest) /\
          U64.v len == List.Tot.length (Cbor.Array?.v v)
        )
    ))
    (fun res -> exists_ (fun vres ->
      A.pts_to res vres **
      raw_data_item_array_match p vres (maybe_cbor_array v) **
      ((A.pts_to res vres **
        raw_data_item_array_match p vres (maybe_cbor_array v)) @==> (
        raw_data_item_match p a v **
        (exists_ (A.pts_to dest #full_perm))
      )) ** pure (
      Cbor.Array? v /\
      U64.v len == A.length dest /\
      U64.v len == A.length res
    )))

let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

let dummy_raw_data_item : Ghost.erased Cbor.raw_data_item =
  Cbor.Int64 Cbor.major_type_uint64 0uL

let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> dummy_raw_data_item

noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: cbor;
}

val destr_cbor_tagged
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt cbor_tagged
    (raw_data_item_match p a v ** pure (
      (Cbor.Tagged? v)
    ))
    (fun res ->
      raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v) **
      ((raw_data_item_match p res.cbor_tagged_payload (maybe_cbor_tagged_payload v)) @==>
        raw_data_item_match p a v
      ) ** pure (
      Cbor.Tagged? v /\
      res.cbor_tagged_tag == Cbor.Tagged?.tag v
    ))

val constr_cbor_tagged
  (tag: U64.t)
  (a: R.ref cbor)
  (#c': Ghost.erased (cbor))
  (#v': Ghost.erased (Cbor.raw_data_item))
: stt cbor
    (R.pts_to a c' **
      raw_data_item_match full_perm c' v')
    (fun res ->
      raw_data_item_match full_perm res (Cbor.Tagged tag v') **
      (raw_data_item_match full_perm res (Cbor.Tagged tag v') @==>
        (R.pts_to a c' **
          raw_data_item_match full_perm c' v')
      )
    )

val constr_cbor_map
  (a: A.array cbor_map_entry)
  (len: U64.t)
  (#c': Ghost.erased (Seq.seq cbor_map_entry))
  (#v': Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
: stt cbor
    (A.pts_to a c' **
      raw_data_item_map_match full_perm c' v' **
      pure (
        U64.v len == List.Tot.length v'
    ))
    (fun res -> exists_ (fun vres ->
      raw_data_item_match full_perm res vres **
      (raw_data_item_match full_perm res vres @==>
        (A.pts_to a c' **
          raw_data_item_map_match full_perm c' v')
      ) ** pure (
      U64.v len == List.Tot.length v' /\
      vres == Cbor.Map v'
    )))

val cbor_get_major_type
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt Cbor.major_type_t
    (raw_data_item_match p a v)
    (fun res -> raw_data_item_match p a v ** pure (
      res == Cbor.get_major_type v
    ))

val cbor_is_equal
  (a1: cbor)
  (a2: cbor)
  (#p1: perm)
  (#p2: perm)
  (#v1: Ghost.erased Cbor.raw_data_item)
  (#v2: Ghost.erased Cbor.raw_data_item)
: stt bool
    (raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2)
    (fun res -> raw_data_item_match p1 a1 v1 ** raw_data_item_match p2 a2 v2 ** pure (
      (~ (Cbor.Tagged? v1 \/ Cbor.Array? v1 \/ Cbor.Map? v1)) ==> (res == true <==> v1 == v2) // TODO: underspecified for tagged, arrays and maps, complete those missing cases
    ))

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

let cbor_map_get_post_not_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
: Tot vprop
= raw_data_item_match p map vmap ** pure (
    Cbor.Map? vmap /\
    list_ghost_assoc vkey (Cbor.Map?.v vmap) == None
  )

let cbor_map_get_post_found
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (value: cbor)
: Tot vprop
= exists_ (fun vvalue ->
    raw_data_item_match p value vvalue **
    (raw_data_item_match p value vvalue @==> raw_data_item_match p map vmap) **
    pure (
      Cbor.Map? vmap /\
      list_ghost_assoc vkey (Cbor.Map?.v vmap) == Some vvalue
  ))

let cbor_map_get_post
  (p: perm)
  (vkey: Cbor.raw_data_item)
  (vmap: Cbor.raw_data_item)
  (map: cbor)
  (res: cbor_map_get_t)
: Tot vprop
= match res with
  | NotFound -> cbor_map_get_post_not_found p vkey vmap map
  | Found value -> cbor_map_get_post_found p vkey vmap map value

val cbor_map_get
  (key: cbor)
  (map: cbor)
  (#pkey: perm)
  (#pmap: perm)
  (#vkey: Ghost.erased Cbor.raw_data_item)
  (#vmap: Ghost.erased Cbor.raw_data_item)
: stt cbor_map_get_t
    (raw_data_item_match pkey key vkey ** raw_data_item_match pmap map vmap ** pure (
      Cbor.Map? vmap /\
      (~ (Cbor.Tagged? vkey \/ Cbor.Array? vkey \/ Cbor.Map? vkey))
    ))
    (fun res -> raw_data_item_match pkey key vkey ** cbor_map_get_post pmap vkey vmap map res ** pure (
      Cbor.Map? vmap /\
      Found? res == Some? (list_ghost_assoc (Ghost.reveal vkey) (Cbor.Map?.v vmap))
    ))

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

let write_cbor_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (res: SZ.t)
  (vout': Seq.seq U8.t)
: Tot vprop
= 
  A.pts_to out vout' **
  pure (write_cbor_postcond va out vout' res)

val write_cbor
  (c: cbor)
  (out: A.array U8.t)
  (sz: SZ.t)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (#vout: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (raw_data_item_match p c (Ghost.reveal va) **
      A.pts_to out vout **
      pure (
        (SZ.v sz == A.length out)
    ))
    (fun res -> 
      raw_data_item_match p c (Ghost.reveal va) **
      exists_ (write_cbor_post va c vout out res)
    )

val cbor_gather
  (c: cbor)
  (v1 v2: Cbor.raw_data_item)
  (p1 p2: perm)
: stt_ghost unit emp_inames
    (raw_data_item_match p1 c v1 ** raw_data_item_match p2 c v2)
    (fun _ -> raw_data_item_match (p1 `sum_perm` p2) c v1 ** pure (v1 == v2))

val cbor_share
  (c: cbor)
  (v1: Cbor.raw_data_item)
  (p p1 p2: perm)
: stt_ghost unit emp_inames
    (raw_data_item_match p c v1 ** pure (p == p1 `sum_perm` p2))
    (fun _ -> raw_data_item_match p1 c v1 ** raw_data_item_match p2 c v1)
