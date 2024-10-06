(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module CBOR.Pulse.Extern
include CBOR.Pulse.Type
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module SM = Pulse.Lib.SeqMatch

val cbor_dummy : cbor

val cbor_map_entry_key: cbor_map_entry -> cbor

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

val cbor_mk_map_entry
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

val raw_data_item_match
  (p: perm)
  (c: cbor)
  (v: Cbor.raw_data_item)
: Tot slprop

let raw_data_item_array_match
  (p: perm)
  (c: Seq.seq cbor)
  (v: list Cbor.raw_data_item)
: Tot slprop
= SM.seq_list_match c v (raw_data_item_match p)

let raw_data_item_map_entry_match
  (p: perm)
  (c1: cbor_map_entry)
  (v1: (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot slprop
= raw_data_item_match p (cbor_map_entry_key c1) (fstp v1) **
  raw_data_item_match p (cbor_map_entry_value c1) (sndp v1)

let raw_data_item_map_match
  (p: perm)
  (c: Seq.seq cbor_map_entry)
  (v: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot slprop
  (decreases v)
= SM.seq_list_match c v (raw_data_item_map_entry_match p)

(* Parsing *)

[@@no_auto_projectors]
noeq
type cbor_read_t = {
  cbor_read_is_success: bool;
  cbor_read_payload: cbor;
  cbor_read_remainder: A.array U8.t;
  cbor_read_remainder_length: SZ.t;
}

noextract
let cbor_read_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= SZ.v c.cbor_read_remainder_length == Seq.length rem /\
  va `Seq.equal` (Cbor.serialize_cbor v `Seq.append` rem)

let cbor_read_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
: Tot slprop
= exists* v rem.
    raw_data_item_match 1.0R c.cbor_read_payload v **
    pts_to c.cbor_read_remainder #p rem **
    ((raw_data_item_match 1.0R c.cbor_read_payload v ** pts_to c.cbor_read_remainder #p rem) @==>
      pts_to a #p va) **
    pure (cbor_read_success_postcond va c v rem)


noextract
let cbor_read_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . ~ (Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff)

let cbor_read_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot slprop
= pts_to a #p va ** pure (cbor_read_error_postcond va)

let cbor_read_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: cbor_read_t)
: Tot slprop
= if res.cbor_read_is_success
  then cbor_read_success_post a p va res
  else cbor_read_error_post a p va

val cbor_read
  (a: A.array U8.t)
  (sz: SZ.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt cbor_read_t
    (pts_to a #p va ** pure (
      (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a)
    ))
    (fun res -> cbor_read_post a p va res)

noextract
let cbor_read_deterministically_encoded_success_postcond
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
  (v: Cbor.raw_data_item)
  (rem: Seq.seq U8.t)
: Tot prop
= cbor_read_success_postcond va c v rem /\
  Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == true

let cbor_read_deterministically_encoded_success_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (c: cbor_read_t)
: Tot slprop
= ((exists* v rem.
    raw_data_item_match 1.0R c.cbor_read_payload v **
    pts_to c.cbor_read_remainder #p rem **
    ((raw_data_item_match 1.0R c.cbor_read_payload v ** pts_to c.cbor_read_remainder #p rem) @==>
      pts_to a #p va) **
    pure (cbor_read_deterministically_encoded_success_postcond va c v rem)
  ))

noextract
let cbor_read_deterministically_encoded_error_postcond
  (va: Ghost.erased (Seq.seq U8.t))
: Tot prop
= forall v suff . Ghost.reveal va == Cbor.serialize_cbor v `Seq.append` suff ==> Cbor.data_item_wf Cbor.deterministically_encoded_cbor_map_key_order v == false

let cbor_read_deterministically_encoded_error_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
: Tot slprop
= pts_to a #p va ** pure (cbor_read_deterministically_encoded_error_postcond va)

let cbor_read_deterministically_encoded_post
  (a: A.array U8.t)
  (p: perm)
  (va: Ghost.erased (Seq.seq U8.t))
  (res: cbor_read_t)
: Tot slprop
= if res.cbor_read_is_success
  then cbor_read_deterministically_encoded_success_post a p va res
  else cbor_read_deterministically_encoded_error_post a p va

val cbor_read_deterministically_encoded
  (a: A.array U8.t)
  (sz: SZ.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt cbor_read_t
    (pts_to a #p va ** pure (SZ.v sz == Seq.length va \/ SZ.v sz == A.length a))
    (fun res -> cbor_read_deterministically_encoded_post a p va res)

(* Destructors and constructors *)

val cbor_destr_int64
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

val cbor_constr_int64
  (ty: Cbor.major_type_uint64_or_neg_int64)
  (value: U64.t)
: stt cbor
    emp
    (fun c -> raw_data_item_match 1.0R c (Cbor.Int64 ty value))

val cbor_destr_simple_value
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

val cbor_constr_simple_value
  (value: Cbor.simple_value)
: stt cbor
    emp
    (fun c -> raw_data_item_match 1.0R c (Cbor.Simple value))

noextract
let cbor_destr_string_post
  (va: Cbor.raw_data_item)
  (c': cbor_string)
  (vc' : Seq.seq U8.t)
: Tot prop
=         Cbor.String? va /\
        U64.v c'.cbor_string_length == Seq.length vc' /\
        c'.cbor_string_type == Cbor.String?.typ va /\
        vc' == Cbor.String?.v va


val cbor_destr_string
  (c: cbor)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
: stt cbor_string
    (raw_data_item_match p c (Ghost.reveal va) ** pure (
      Cbor.String? va
    ))
    (fun c' -> exists* vc' p'.
      pts_to c'.cbor_string_payload #p' vc' **
      (pts_to c'.cbor_string_payload #p' vc' @==> raw_data_item_match p c (Ghost.reveal va)) **
      pure (cbor_destr_string_post va c'  vc'
    ))

val cbor_constr_string
  (typ: Cbor.major_type_byte_string_or_text_string)
  (a: A.array U8.t)
  (len: U64.t)
  (#va: Ghost.erased (Seq.seq U8.t))
  (#p: perm)
: stt cbor
    (pts_to a #p va ** pure (
      U64.v len == Seq.length va
    ))
    (fun c' -> exists* vc'.
      raw_data_item_match 1.0R c' vc' **
      (raw_data_item_match 1.0R c' vc' @==>
        pts_to a #p va
      ) ** pure (
      U64.v len == Seq.length va /\
      vc' == Cbor.String typ va
    ))

val cbor_constr_array
  (a: A.array cbor)
  (len: U64.t)
  (#c': Ghost.erased (Seq.seq cbor))
  (#v': Ghost.erased (list Cbor.raw_data_item))
: stt cbor
    (pts_to a c' **
      raw_data_item_array_match 1.0R c' v' **
      pure (
        U64.v len == List.Tot.length v'
    ))
    (fun res -> exists* vres.
      raw_data_item_match 1.0R res vres **
      (raw_data_item_match 1.0R res vres @==>
        (pts_to a c' **
          raw_data_item_array_match 1.0R c' v')
      ) ** pure (
      U64.v len == List.Tot.length v' /\
      vres == Cbor.Array v'
    ))

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
    (fun a' -> exists* va'.
      raw_data_item_match p a' va' **
      (raw_data_item_match p a' va' @==>
        raw_data_item_match p a v) **
      pure (
        Cbor.Array? v /\
        SZ.v i < List.Tot.length (Cbor.Array?.v v) /\
        va' == List.Tot.index (Cbor.Array?.v v) (SZ.v i)
    ))

val cbor_dummy_array_iterator: cbor_array_iterator_t

val cbor_array_iterator_match
  (p: perm)
  (i: cbor_array_iterator_t)
  (l: list Cbor.raw_data_item)
: Tot slprop

val cbor_array_iterator_init
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt cbor_array_iterator_t
    (raw_data_item_match p a v)
    (fun i -> exists* vi.
      cbor_array_iterator_match p i vi **
      (cbor_array_iterator_match p i vi @==>
        raw_data_item_match p a v) **
      pure (
        Cbor.Array? v /\
        vi == Cbor.Array?.v v
    ))

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
    (pts_to pi i ** cbor_array_iterator_match p i l **
      pure (Cons? l)
    )
    (fun c -> exists* i' vc vi'.
      pts_to pi i' **
      raw_data_item_match p c vc **
      cbor_array_iterator_match p i' vi' **
      ((raw_data_item_match p c vc **
        cbor_array_iterator_match p i' vi') @==>
        cbor_array_iterator_match p i l
      ) ** pure (
      Ghost.reveal l == vc :: vi'
    ))

val cbor_read_array
  (a: cbor)
  (dest: A.array cbor) // it is the user's responsibility to allocate the array properly
  (len: U64.t)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
  (#vdest: Ghost.erased (Seq.seq cbor))
: stt (A.array cbor)
    (raw_data_item_match p a v **
      pts_to dest vdest **
      pure (
        (Cbor.Array? v /\
          (U64.v len == A.length dest \/ U64.v len == Seq.length vdest) /\
          U64.v len == List.Tot.length (Cbor.Array?.v v)
        )
    ))
    (fun res -> exists* vres.
      pts_to res vres **
      raw_data_item_array_match p vres (maybe_cbor_array v) **
      ((pts_to res vres **
        raw_data_item_array_match p vres (maybe_cbor_array v)) @==> (
        raw_data_item_match p a v **
        (exists* _x. (pts_to dest #1.0R _x))
      )) ** pure (
      Cbor.Array? v /\
      U64.v len == A.length dest /\
      U64.v len == A.length res
    ))

let maybe_cbor_tagged_tag
  (v: Cbor.raw_data_item)
: GTot U64.t
= match v with
  | Cbor.Tagged t _ -> t
  | _ -> 0uL // dummy

let dummy_raw_data_item : Ghost.erased Cbor.raw_data_item =
  Cbor.Int64 Cbor.cbor_major_type_uint64 0uL

let maybe_cbor_tagged_payload
  (v: Cbor.raw_data_item)
: GTot Cbor.raw_data_item
= match v with
  | Cbor.Tagged _ l -> l
  | _ -> dummy_raw_data_item

[@@no_auto_projectors]
noeq
type cbor_tagged = {
  cbor_tagged_tag: U64.t;
  cbor_tagged_payload: cbor;
}

val cbor_destr_tagged
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

val cbor_constr_tagged
  (tag: U64.t)
  (a: R.ref cbor)
  (#c': Ghost.erased (cbor))
  (#v': Ghost.erased (Cbor.raw_data_item))
: stt cbor
    (pts_to a c' **
      raw_data_item_match 1.0R c' v')
    (fun res ->
      raw_data_item_match 1.0R res (Cbor.Tagged tag v') **
      (raw_data_item_match 1.0R res (Cbor.Tagged tag v') @==>
        (pts_to a c' **
          raw_data_item_match 1.0R c' v')
      )
    )

val cbor_constr_map
  (a: A.array cbor_map_entry)
  (len: U64.t)
  (#c': Ghost.erased (Seq.seq cbor_map_entry))
  (#v': Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
: stt cbor
    (pts_to a c' **
      raw_data_item_map_match 1.0R c' v' **
      pure (
        U64.v len == List.Tot.length v'
    ))
    (fun res -> exists* vres.
      raw_data_item_match 1.0R res vres **
      (raw_data_item_match 1.0R res vres @==>
        (pts_to a c' **
          raw_data_item_map_match 1.0R c' v')
      ) ** pure (
      U64.v len == List.Tot.length v' /\
      vres == Cbor.Map v'
    ))

val cbor_map_length
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt U64.t
    (raw_data_item_match p a v ** pure (
      (Cbor.Map? v)
    ))
    (fun res -> raw_data_item_match p a v ** pure (
      Cbor.Map? v /\
      U64.v res == List.Tot.length (Cbor.Map?.v v)
    ))

val cbor_dummy_map_iterator: cbor_map_iterator_t

val cbor_map_iterator_match
  (p: perm)
  (i: cbor_map_iterator_t)
  (l: list (Cbor.raw_data_item & Cbor.raw_data_item))
: Tot slprop

val cbor_map_iterator_init
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt cbor_map_iterator_t
    (raw_data_item_match p a v ** pure (Cbor.Map? v))
    (fun i -> exists* l.
      cbor_map_iterator_match p i l **
      (cbor_map_iterator_match p i l @==>
        raw_data_item_match p a v) **
      pure (
        Cbor.Map? v /\
        l == Cbor.Map?.v v
      )
    )

val cbor_map_iterator_is_done
  (i: cbor_map_iterator_t)
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)))
: stt bool
    (cbor_map_iterator_match p i l)
    (fun res -> cbor_map_iterator_match p i l ** pure (res == Nil? l))

val cbor_map_iterator_next
  (pi: R.ref cbor_map_iterator_t)
  (#p: perm)
  (#l: Ghost.erased (list (Cbor.raw_data_item & Cbor.raw_data_item)) { Cons? l})
  (#i: Ghost.erased cbor_map_iterator_t)
: stt cbor_map_entry
    (pts_to pi i ** cbor_map_iterator_match p i l ** pure (Cons? l))
    (fun c -> exists* i' vc l'.
      pts_to pi i' **
      raw_data_item_map_entry_match p c vc **
      cbor_map_iterator_match p i' l' **
      ((raw_data_item_map_entry_match p c vc **
        cbor_map_iterator_match p i' l' @==>
        cbor_map_iterator_match p i l
      ) **
      pure (Ghost.reveal l == vc :: l')
    ))

val cbor_get_major_type
  (a: cbor)
  (#p: perm)
  (#v: Ghost.erased Cbor.raw_data_item)
: stt Cbor.major_type_t
    (raw_data_item_match p a v)
    (fun res -> raw_data_item_match p a v ** pure (
      res == Cbor.get_major_type v
    ))

(* `cbor_compare_aux` is an auxiliary function intended to compare two CBOR objects
   represented by their serialized bytes. It returns an inconclusive result if one of
   the two is not such an object. The full equality test is implemented in Pulse, see
   `CBOR.Pulse.cbor_compare`
*)

noextract
let cbor_compare_aux_postcond
  (v1 v2: Cbor.raw_data_item)
  (res: FStar.Int16.t)
: Tot prop
= let nres = FStar.Int16.v res in
  (nres = -1 || nres = 0 || nres = 1) ==> nres == Cbor.cbor_compare v1 v2

val cbor_compare_aux
  (c1 c2: cbor)
  (#p1 #p2: perm)
  (#v1 #v2: Ghost.erased Cbor.raw_data_item)
: stt FStar.Int16.t
    (raw_data_item_match p1 c1 v1 ** raw_data_item_match p2 c2 v2)
    (fun res -> raw_data_item_match p1 c1 v1 ** raw_data_item_match p2 c2 v2 **
      pure (cbor_compare_aux_postcond v1 v2 res)
    )

(* Serialization *)

noextract
let cbor_write_postcond
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

let cbor_write_post
  (va: Ghost.erased Cbor.raw_data_item)
  (c: cbor)
  (vout: Ghost.erased (Seq.seq U8.t))
  (out: A.array U8.t)
  (res: SZ.t)
  (vout': Seq.seq U8.t)
: Tot slprop
= 
  pts_to out vout' **
  pure (cbor_write_postcond va out vout' res)

val cbor_write
  (c: cbor)
  (out: A.array U8.t)
  (sz: SZ.t)
  (#p: perm)
  (#va: Ghost.erased Cbor.raw_data_item)
  (#vout: Ghost.erased (Seq.seq U8.t))
: stt SZ.t
    (raw_data_item_match p c (Ghost.reveal va) **
      pts_to out vout **
      pure (
        (SZ.v sz == A.length out)
    ))
    (fun res -> 
      raw_data_item_match p c (Ghost.reveal va) **
      (exists* _x. cbor_write_post va c vout out res _x)
    )

val cbor_gather
  (c: cbor)
  (v1 v2: Cbor.raw_data_item)
  (p1 p2: perm)
: stt_ghost unit emp_inames
    (raw_data_item_match p1 c v1 ** raw_data_item_match p2 c v2)
    (fun _ -> raw_data_item_match (p1 +. p2) c v1 ** pure (v1 == v2))

val cbor_share
  (c: cbor)
  (v1: Cbor.raw_data_item)
  (p p1 p2: perm)
: stt_ghost unit emp_inames
    (raw_data_item_match p c v1 ** pure (p == p1 +. p2))
    (fun _ -> raw_data_item_match p1 c v1 ** raw_data_item_match p2 c v1)
