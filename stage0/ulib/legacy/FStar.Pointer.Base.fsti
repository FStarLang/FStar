(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Pointer.Base

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST // for := , !

(*** Definitions *)

(** Type codes *)

type base_typ =
| TUInt
| TUInt8
| TUInt16
| TUInt32
| TUInt64
| TInt
| TInt8
| TInt16
| TInt32
| TInt64
| TChar
| TBool
| TUnit

// C11, Sect. 6.2.5 al. 20: arrays must be nonempty
type array_length_t = (length: UInt32.t { UInt32.v length > 0 } )

type typ =
| TBase:
  (b: base_typ) ->
  typ
| TStruct:
  (l: struct_typ) ->
  typ
| TUnion:
  (l: union_typ) ->
  typ
| TArray:
  (length: array_length_t ) ->
  (t: typ) ->
  typ
| TPointer:
  (t: typ) ->
  typ
| TNPointer:
  (t: typ) ->
  typ
| TBuffer:
  (t: typ) ->
  typ
and struct_typ' = (l: list (string & typ) {
  Cons? l /\ // C11, 6.2.5 al. 20: structs and unions must have at least one field
  List.Tot.noRepeats (List.Tot.map fst l)
})
and struct_typ = {
  name: string;
  fields: struct_typ' ;
}
and union_typ = struct_typ

(** `struct_field l` is the type of fields of `TStruct l`
    (i.e. a refinement of `string`).
*)
let struct_field'
  (l: struct_typ')
: Tot eqtype
= (s: string { List.Tot.mem s (List.Tot.map fst l) } )

let struct_field
  (l: struct_typ)
: Tot eqtype
= struct_field' l.fields

(** `union_field l` is the type of fields of `TUnion l`
    (i.e. a refinement of `string`).
*)
let union_field = struct_field

(** `typ_of_struct_field l f` is the type of data associated with field `f` in
    `TStruct l` (i.e. a refinement of `typ`).
*)

let typ_of_struct_field'
  (l: struct_typ')
  (f: struct_field' l)
: Tot (t: typ {t << l})
= List.Tot.assoc_mem f l;
  let y = Some?.v (List.Tot.assoc f l) in
  List.Tot.assoc_precedes f l y;
  y

let typ_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Tot (t: typ {t << l})
= typ_of_struct_field' l.fields f

(** `typ_of_union_field l f` is the type of data associated with field `f` in
    `TUnion l` (i.e. a refinement of `typ`).
*)
let typ_of_union_field
  (l: union_typ)
  (f: union_field l)
: Tot (t: typ {t << l})
= typ_of_struct_field l f

let rec typ_depth
  (t: typ)
: GTot nat
= match t with
  | TArray _ t -> 1 + typ_depth t
  | TUnion l
  | TStruct l -> 1 + struct_typ_depth l.fields
  | _ -> 0
and struct_typ_depth
  (l: list (string & typ))
: GTot nat
= match l with
  | [] -> 0
  | h :: l ->
    let (_, t) = h in // matching like this prevents needing two units of ifuel
    let n1 = typ_depth t in
    let n2 = struct_typ_depth l in
    if n1 > n2 then n1 else n2

let rec typ_depth_typ_of_struct_field
  (l: struct_typ')
  (f: struct_field' l)
: Lemma
  (ensures (typ_depth (typ_of_struct_field' l f) <= struct_typ_depth l))
  (decreases l)
= let ((f', _) :: l') = l in
  if f = f'
  then ()
  else begin
    let f: string = f in
    assert (List.Tot.mem f (List.Tot.map fst l'));
    List.Tot.assoc_mem f l';
    typ_depth_typ_of_struct_field l' f
  end

(** Pointers to data of type t.

    This defines two main types:
    - `npointer (t: typ)`, a pointer that may be "NULL";
    - `pointer (t: typ)`, a pointer that cannot be "NULL"
      (defined as a refinement of `npointer`).

    `nullptr #t` (of type `npointer t`) represents the "NULL" value.
*)

val npointer (t: typ) : Tot Type0

(** The null pointer *)

val nullptr (#t: typ): Tot (npointer t)

val g_is_null (#t: typ) (p: npointer t) : GTot bool

val g_is_null_intro
  (t: typ)
: Lemma
  (g_is_null (nullptr #t) == true)
  [SMTPat (g_is_null (nullptr #t))]

// concrete, for subtyping
let pointer (t: typ) : Tot Type0 = (p: npointer t { g_is_null p == false } )

(** Buffers *)

val buffer (t: typ): Tot Type0

(** Interpretation of type codes.

   Defines functions mapping from type codes (`typ`) to their interpretation as
   FStar types. For example, `type_of_typ (TBase TUInt8)` is `FStar.UInt8.t`.
*)

(** Interpretation of base types. *)
let type_of_base_typ
  (t: base_typ)
: Tot Type0
= match t with
  | TUInt -> nat
  | TUInt8 -> FStar.UInt8.t
  | TUInt16 -> FStar.UInt16.t
  | TUInt32 -> FStar.UInt32.t
  | TUInt64 -> FStar.UInt64.t
  | TInt -> int
  | TInt8 -> FStar.Int8.t
  | TInt16 -> FStar.Int16.t
  | TInt32 -> FStar.Int32.t
  | TInt64 -> FStar.Int64.t
  | TChar -> FStar.Char.char
  | TBool -> bool
  | TUnit -> unit

(** Interpretation of arrays of elements of (interpreted) type `t`. *)
type array (length: array_length_t) (t: Type) = (s: Seq.seq t {Seq.length s == UInt32.v length})

let type_of_struct_field''
  (l: struct_typ')
  (type_of_typ: (
    (t: typ { t << l } ) ->
    Tot Type0
  ))
  (f: struct_field' l)
: Tot Type0 =
  List.Tot.assoc_mem f l;
  let y = typ_of_struct_field' l f in
  List.Tot.assoc_precedes f l y;
  type_of_typ y

[@@ unifier_hint_injective]
let type_of_struct_field'
  (l: struct_typ)
  (type_of_typ: (
    (t: typ { t << l } ) ->
    Tot Type0
  ))
  (f: struct_field l)
: Tot Type0
= type_of_struct_field'' l.fields type_of_typ f

val struct (l: struct_typ) : Tot Type0
val union (l: union_typ) : Tot Type0

(* Interprets a type code (`typ`) as a FStar type (`Type0`). *)
let rec type_of_typ
  (t: typ)
: Tot Type0
= match t with
  | TBase b -> type_of_base_typ b
  | TStruct l ->
    struct l
  | TUnion l ->
    union l
  | TArray length t ->
    array length (type_of_typ t)
  | TPointer t ->
    pointer t
  | TNPointer t ->
    npointer t
  | TBuffer t ->
    buffer t

let type_of_typ_array
  (len: array_length_t)
  (t: typ)
: Lemma
  (type_of_typ (TArray len t) == array len (type_of_typ t))
  [SMTPat (type_of_typ (TArray len t))]
= ()

let type_of_struct_field
  (l: struct_typ)
: Tot (struct_field l -> Tot Type0)
= type_of_struct_field' l (fun (x:typ{x << l}) -> type_of_typ x)

let type_of_typ_struct
  (l: struct_typ)
: Lemma
  (type_of_typ (TStruct l) == struct l)
  [SMTPat (type_of_typ (TStruct l))]
= assert_norm (type_of_typ (TStruct l) == struct l)

let type_of_typ_type_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Lemma
  (type_of_typ (typ_of_struct_field l f) == type_of_struct_field l f)
  [SMTPat (type_of_typ (typ_of_struct_field l f))]
= ()

val struct_sel (#l: struct_typ) (s: struct l) (f: struct_field l) : Tot (type_of_struct_field l f)

let dfst_struct_field
  (s: struct_typ)
  (p: (x: struct_field s & type_of_struct_field s x))
: Tot string
=
  let (| f, _ |) = p in
  f

let struct_literal (s: struct_typ) : Tot Type0 = list (x: struct_field s & type_of_struct_field s x)

let struct_literal_wf (s: struct_typ) (l: struct_literal s) : Tot bool =
  List.Tot.sortWith FStar.String.compare (List.Tot.map fst s.fields) =
  List.Tot.sortWith FStar.String.compare
    (List.Tot.map (dfst_struct_field s) l)

let fun_of_list
  (s: struct_typ)
  (l: struct_literal s)
  (f: struct_field s)
: Pure (type_of_struct_field s f)
  (requires (normalize_term (struct_literal_wf s l) == true))
  (ensures (fun _ -> True))
=
  let f' : string = f in
  let phi (p: (x: struct_field s & type_of_struct_field s x)) : Tot bool =
    dfst_struct_field s p = f'
  in
  match List.Tot.find phi l with
  | Some p -> let (| _, v |) = p in v
  | _ ->
    List.Tot.sortWith_permutation FStar.String.compare (List.Tot.map fst s.fields);
    List.Tot.sortWith_permutation FStar.String.compare (List.Tot.map (dfst_struct_field s) l);
    List.Tot.mem_memP f' (List.Tot.map fst s.fields);
    List.Tot.mem_count (List.Tot.map fst s.fields) f';
    List.Tot.mem_count (List.Tot.map (dfst_struct_field s) l) f';
    List.Tot.mem_memP f' (List.Tot.map (dfst_struct_field s) l);
    List.Tot.memP_map_elim (dfst_struct_field s) f' l;
    Classical.forall_intro (Classical.move_requires (List.Tot.find_none phi l));
    false_elim ()

val struct_create_fun (l: struct_typ) (f: ((fd: struct_field l) -> Tot (type_of_struct_field l fd))) : Tot (struct l)

let struct_create
  (s: struct_typ)
  (l: struct_literal s)
: Pure (struct s)
  (requires (normalize_term (struct_literal_wf s l) == true))
  (ensures (fun _ -> True))
= struct_create_fun s (fun_of_list s l)

val struct_sel_struct_create_fun
  (l: struct_typ)
  (f: ((fd: struct_field l) -> Tot (type_of_struct_field l fd)))
  (fd: struct_field l)
: Lemma
  (struct_sel (struct_create_fun l f) fd == f fd)
  [SMTPat (struct_sel (struct_create_fun l f) fd)]

let type_of_typ_union
  (l: union_typ)
: Lemma
  (type_of_typ (TUnion l) == union l)
  [SMTPat (type_of_typ (TUnion l))]
= assert_norm (type_of_typ (TUnion l) == union l)

val union_get_key (#l: union_typ) (v: union l) : GTot (struct_field l)

val union_get_value
  (#l: union_typ)
  (v: union l)
  (fd: struct_field l)
: Pure (type_of_struct_field l fd)
  (requires (union_get_key v == fd))
  (ensures (fun _ -> True))

val union_create
  (l: union_typ)
  (fd: struct_field l)
  (v: type_of_struct_field l fd)
: Tot (union l)

(*** Semantics of pointers *)

(** Operations on pointers *)

val equal
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> t1 == t2 /\ p1 == p2 ))

val as_addr (#t: typ) (p: pointer t): GTot (x: nat { x > 0 } )

val unused_in
  (#value: typ)
  (p: pointer value)
  (h: HS.mem)
: GTot Type0

val live
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot Type0

val nlive
  (#value: typ)
  (h: HS.mem)
  (p: npointer value)
: GTot Type0

val live_nlive
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: Lemma
  (nlive h p <==> live h p)
  [SMTPat (nlive h p)]

val g_is_null_nlive
  (#t: typ)
  (h: HS.mem)
  (p: npointer t)
: Lemma
  (requires (g_is_null p))
  (ensures (nlive h p))
  [SMTPat (g_is_null p); SMTPat (nlive h p)]

val live_not_unused_in
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: Lemma
  (ensures (live h p /\ p `unused_in` h ==> False))
  [SMTPat (live h p); SMTPat (p `unused_in` h)]

val gread
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot (type_of_typ value)

val frameOf
  (#value: typ)
  (p: pointer value)
: GTot HS.rid

val live_region_frameOf
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: Lemma
  (requires (live h p))
  (ensures (HS.live_region h (frameOf p)))
  [SMTPatOr [
    [SMTPat (HS.live_region h (frameOf p))];
    [SMTPat (live h p)]
  ]]

val disjoint_roots_intro_pointer_vs_pointer
  (#value1 value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 =!= as_addr p2))

val disjoint_roots_intro_pointer_vs_reference
  (#value1: typ)
  (#value2: Type)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: HS.reference value2)
: Lemma
  (requires (live h p1 /\ p2 `HS.unused_in` h))
  (ensures (frameOf p1 <> HS.frameOf p2 \/ as_addr p1 =!= HS.as_addr p2))

val disjoint_roots_intro_reference_vs_pointer
  (#value1: Type)
  (#value2: typ)
  (h: HS.mem)
  (p1: HS.reference value1)
  (p2: pointer value2)
: Lemma
  (requires (HS.contains h p1 /\ p2 `unused_in` h))
  (ensures (HS.frameOf p1 <> frameOf p2 \/ HS.as_addr p1 =!= as_addr p2))

val is_mm
  (#value: typ)
  (p: pointer value)
: GTot bool

(* // TODO: recover with addresses?
val recall
  (#value: Type)
  (p: pointer value {is_eternal_region (frameOf p) && not (is_mm p)})
: HST.Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ live m1 p))
*)

val gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: GTot (pointer (typ_of_struct_field l fd))

val as_addr_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (as_addr (gfield p fd) == as_addr p))
  [SMTPat (as_addr (gfield p fd))]

val unused_in_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (unused_in (gfield p fd) h <==> unused_in p h))
  [SMTPat (unused_in (gfield p fd) h)]

val live_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (live h (gfield p fd) <==> live h p))
  [SMTPat (live h (gfield p fd))]

val gread_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (gread h (gfield p fd) == struct_sel (gread h p) fd))
  [SMTPatOr [[SMTPat (gread h (gfield p fd))]; [SMTPat (struct_sel (gread h p) fd)]]]

val frameOf_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (frameOf (gfield p fd) == frameOf p))
  [SMTPat (frameOf (gfield p fd))]

val is_mm_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (is_mm (gfield p fd) <==> is_mm p))
  [SMTPat (is_mm (gfield p fd))]

val gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: GTot (pointer (typ_of_struct_field l fd))

val as_addr_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (as_addr (gufield p fd) == as_addr p))
  [SMTPat (as_addr (gufield p fd))]

val unused_in_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (unused_in (gufield p fd) h <==> unused_in p h))
  [SMTPat (unused_in (gufield p fd) h)]

val live_gufield
  (h: HS.mem)
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (live h (gufield p fd) <==> live h p))
  [SMTPat (live h (gufield p fd))]

val gread_gufield
  (h: HS.mem)
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (union_get_key (gread h p) == fd))
  (ensures (
    union_get_key (gread h p) == fd /\
    gread h (gufield p fd) == union_get_value (gread h p) fd
  ))
  [SMTPatOr [[SMTPat (gread h (gufield p fd))]; [SMTPat (union_get_value (gread h p) fd)]]]

val frameOf_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (frameOf (gufield p fd) == frameOf p))
  [SMTPat (frameOf (gufield p fd))]

val is_mm_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (is_mm (gufield p fd) <==> is_mm p))
  [SMTPat (is_mm (gufield p fd))]

val gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Ghost (pointer value)
  (requires (UInt32.v i < UInt32.v length))
  (ensures (fun _ -> True))

val as_addr_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ as_addr (gcell p i) == as_addr p))
  [SMTPat (as_addr (gcell p i))]

val unused_in_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ (unused_in (gcell p i) h <==> unused_in p h)))
  [SMTPat (unused_in (gcell p i) h)]

val live_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ (live h (gcell p i) <==> live h p)))
  [SMTPat (live h (gcell p i))]

val gread_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ gread h (gcell p i) == Seq.index (gread h p) (UInt32.v i)))
  [SMTPat (gread h (gcell p i))]

val frameOf_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ frameOf (gcell p i) == frameOf p))
  [SMTPat (frameOf (gcell p i))]

val is_mm_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ is_mm (gcell p i) == is_mm p))
  [SMTPat (is_mm (gcell p i))]

val includes
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: GTot bool

val includes_refl
  (#t: typ)
  (p: pointer t)
: Lemma
  (ensures (includes p p))
  [SMTPat (includes p p)]

val includes_trans
  (#t1 #t2 #t3: typ)
  (p1: pointer t1)
  (p2: pointer t2)
  (p3: pointer t3)
: Lemma
  (requires (includes p1 p2 /\ includes p2 p3))
  (ensures (includes p1 p3))

val includes_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (includes p (gfield p fd)))

val includes_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (includes p (gufield p fd)))

val includes_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ includes p (gcell p i)))

(** The readable permission.
    We choose to implement it only abstractly, instead of explicitly
    tracking the permission in the heap.
*)

val readable
  (#a: typ)
  (h: HS.mem)
  (b: pointer a)
: GTot Type0

val readable_live
  (#a: typ)
  (h: HS.mem)
  (b: pointer a)
: Lemma
  (requires (readable h b))
  (ensures (live h b))
  [SMTPatOr [
    [SMTPat (readable h b)];
    [SMTPat (live h b)];
  ]]

val readable_gfield
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (readable h p))
  (ensures (readable h (gfield p fd)))
  [SMTPat (readable h (gfield p fd))]

val readable_struct
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
: Lemma
  (requires (
    forall (f: struct_field l) .
    readable h (gfield p f)
  ))
  (ensures (readable h p))
//  [SMTPat (readable #(TStruct l) h p)] // TODO: dubious pattern, will probably trigger unreplayable hints

val readable_struct_forall_mem
  (#l: struct_typ)
  (p: pointer (TStruct l))
: Lemma (forall
    (h: HS.mem)
  . (
      forall (f: struct_field l) .
      readable h (gfield p f)
    ) ==>
    readable h p
  )

val readable_struct_fields
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (s: list string)
: GTot Type0

val readable_struct_fields_nil
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
: Lemma
  (readable_struct_fields h p [])
  [SMTPat (readable_struct_fields h p [])]

val readable_struct_fields_cons
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (f: string)
  (q: list string)
: Lemma
  (requires (readable_struct_fields h p q /\ (List.Tot.mem f (List.Tot.map fst l.fields) ==> (let f : struct_field l = f in readable h (gfield p f)))))
  (ensures (readable_struct_fields h p (f::q)))
  [SMTPat (readable_struct_fields h p (f::q))]

val readable_struct_fields_readable_struct
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
: Lemma
  (requires (readable_struct_fields h p (normalize_term (List.Tot.map fst l.fields))))
  (ensures (readable h p))

val readable_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length /\ readable h p))
  (ensures (UInt32.v i < UInt32.v length /\ readable h (gcell p i)))
  [SMTPat (readable h (gcell p i))]

val readable_array
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
: Lemma
  (requires (
    forall (i: UInt32.t) .
    UInt32.v i < UInt32.v length ==>
    readable h (gcell p i)
  ))
  (ensures (readable h p))
//  [SMTPat (readable #(TArray length value) h p)] // TODO: dubious pattern, will probably trigger unreplayable hints

(* TODO: improve on the following interface *)
val readable_gufield
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires True)
  (ensures (readable h (gufield p fd) <==> (readable h p /\ union_get_key (gread h p) == fd)))
  [SMTPat (readable h (gufield p fd))]

(** The active field of a union *)

val is_active_union_field
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: GTot Type0

val is_active_union_live
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (is_active_union_field h p fd))
  (ensures (live h p))
  [SMTPat (is_active_union_field h p fd)]

val is_active_union_field_live
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (is_active_union_field h p fd))
  (ensures (live h (gufield p fd)))
  [SMTPat (is_active_union_field h p fd)]

val is_active_union_field_eq
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd1 fd2: struct_field l)
: Lemma
  (requires (is_active_union_field h p fd1 /\ is_active_union_field h p fd2))
  (ensures (fd1 == fd2))
  [SMTPat (is_active_union_field h p fd1); SMTPat (is_active_union_field h p fd2)]

val is_active_union_field_get_key
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (is_active_union_field h p fd))
  (ensures (union_get_key (gread h p) == fd))
  [SMTPat (is_active_union_field h p fd)]

val is_active_union_field_readable
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (is_active_union_field h p fd /\ readable h (gufield p fd)))
  (ensures (readable h p))
  [SMTPat (is_active_union_field h p fd); SMTPat (readable h (gufield p fd))]

val is_active_union_field_includes_readable
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
  (#t': typ)
  (p' : pointer t')
: Lemma
  (requires (includes (gufield p fd) p' /\ readable h p'))
  (ensures (is_active_union_field h p fd))

(* Equality predicate on struct contents, without quantifiers *)
let equal_values #a h (b:pointer a) h' (b':pointer a) : GTot Type0 =
  (live h b ==> live h' b') /\ (
    readable h b ==> (
      readable h' b' /\
      gread h b == gread h' b'
  ))


(*** Semantics of buffers *)

(** Operations on buffers *)

val gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: GTot (buffer t)

val singleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: HST.Stack (buffer t)
  (requires (fun h -> live h p))
  (ensures (fun h b h' -> h' == h /\ b == gsingleton_buffer_of_pointer p))

val gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: GTot (buffer t)

val buffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: HST.Stack (buffer t)
  (requires (fun h -> live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))

val buffer_length
  (#t: typ)
  (b: buffer t)
: GTot UInt32.t

val buffer_length_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (buffer_length (gsingleton_buffer_of_pointer p))]

val buffer_length_gbuffer_of_array_pointer
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (buffer_length (gbuffer_of_array_pointer p) == len))
  [SMTPat (buffer_length (gbuffer_of_array_pointer p))]

val buffer_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0

val buffer_live_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (h: HS.mem)
: Lemma
  (ensures (buffer_live h (gsingleton_buffer_of_pointer p) <==> live h p ))
  [SMTPat (buffer_live h (gsingleton_buffer_of_pointer p))]

val buffer_live_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (buffer_live h (gbuffer_of_array_pointer p) <==> live h p))
  [SMTPat (buffer_live h (gbuffer_of_array_pointer p))]

val buffer_unused_in
  (#t: typ)
  (b: buffer t)
  (h: HS.mem)
: GTot Type0

val buffer_live_not_unused_in
  (#t: typ)
  (b: buffer t)
  (h: HS.mem)
: Lemma
  ((buffer_live h b /\ buffer_unused_in b h) ==> False)


val buffer_unused_in_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (h: HS.mem)
: Lemma
  (ensures (buffer_unused_in (gsingleton_buffer_of_pointer p) h <==> unused_in p h ))
  [SMTPat (buffer_unused_in (gsingleton_buffer_of_pointer p) h)]

val buffer_unused_in_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (buffer_unused_in (gbuffer_of_array_pointer p) h <==> unused_in p h))
  [SMTPat (buffer_unused_in (gbuffer_of_array_pointer p) h)]

val frameOf_buffer
  (#t: typ)
  (b: buffer t)
: GTot HS.rid

val frameOf_buffer_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (ensures (frameOf_buffer (gsingleton_buffer_of_pointer p) == frameOf p))
  [SMTPat (frameOf_buffer (gsingleton_buffer_of_pointer p))]

val frameOf_buffer_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: Lemma
  (ensures (frameOf_buffer (gbuffer_of_array_pointer p) == frameOf p))
  [SMTPat (frameOf_buffer (gbuffer_of_array_pointer p))]

val live_region_frameOf_buffer
  (#value: typ)
  (h: HS.mem)
  (p: buffer value)
: Lemma
  (requires (buffer_live h p))
  (ensures (HS.live_region h (frameOf_buffer p)))
  [SMTPatOr [
    [SMTPat (HS.live_region h (frameOf_buffer p))];
    [SMTPat (buffer_live h p)]
  ]]

val buffer_as_addr
  (#t: typ)
  (b: buffer t)
: GTot (x: nat { x > 0 } )

val buffer_as_addr_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (ensures (buffer_as_addr (gsingleton_buffer_of_pointer p) == as_addr p))
  [SMTPat (buffer_as_addr (gsingleton_buffer_of_pointer p))]

val buffer_as_addr_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: Lemma
  (ensures (buffer_as_addr (gbuffer_of_array_pointer p) == as_addr p))
  [SMTPat (buffer_as_addr (gbuffer_of_array_pointer p))]

val gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Ghost (buffer t)
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (fun _ -> True))

val frameOf_buffer_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    frameOf_buffer (gsub_buffer b i len) == frameOf_buffer b
  ))
  [SMTPat (frameOf_buffer (gsub_buffer b i len))]

val buffer_as_addr_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_as_addr (gsub_buffer b i len) == buffer_as_addr b
  ))
  [SMTPat (buffer_as_addr (gsub_buffer b i len))]

val sub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: HST.Stack (buffer t)
  (requires (fun h -> UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_live h b))
  (ensures (fun h b' h' -> UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ h' == h /\ b' == gsub_buffer b i len ))

val offset_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: HST.Stack (buffer t)
  (requires (fun h -> UInt32.v i <= UInt32.v (buffer_length b) /\ buffer_live h b))
  (ensures (fun h b' h' -> UInt32.v i <= UInt32.v (buffer_length b) /\ h' == h /\ b' == gsub_buffer b i (UInt32.sub (buffer_length b) i)))

val buffer_length_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_length (gsub_buffer b i len) == len))
  [SMTPat (buffer_length (gsub_buffer b i len))]

val buffer_live_gsub_buffer_equiv
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ (buffer_live h (gsub_buffer b i len) <==> buffer_live h b)))
  [SMTPat (buffer_live h (gsub_buffer b i len))]

val buffer_live_gsub_buffer_intro
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (buffer_live h b /\ UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_live h (gsub_buffer b i len)))
  [SMTPat (buffer_live h (gsub_buffer b i len))]

val buffer_unused_in_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ (buffer_unused_in (gsub_buffer b i len) h <==> buffer_unused_in b h)))
  [SMTPat (buffer_unused_in (gsub_buffer b i len) h)]

val gsub_buffer_gsub_buffer
  (#a: typ)
  (b: buffer a)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v len1 /\
    gsub_buffer (gsub_buffer b i1 len1) i2 len2 == gsub_buffer b FStar.UInt32.(i1 +^ i2) len2
  ))
  [SMTPat (gsub_buffer (gsub_buffer b i1 len1) i2 len2)]

val gsub_buffer_zero_buffer_length
  (#a: typ)
  (b: buffer a)
: Lemma
  (ensures (gsub_buffer b 0ul (buffer_length b) == b))
  [SMTPat (gsub_buffer b 0ul (buffer_length b))]

val buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq (type_of_typ t))

val buffer_length_buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_as_seq h b) == UInt32.v (buffer_length b)))
  [SMTPat (Seq.length (buffer_as_seq h b))]

val buffer_as_seq_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_as_seq h (gsingleton_buffer_of_pointer p) == Seq.create 1 (gread h p)))
  [SMTPat (buffer_as_seq h (gsingleton_buffer_of_pointer p))]

val buffer_as_seq_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray length t))
: Lemma
  (requires True)
  (ensures (buffer_as_seq h (gbuffer_of_array_pointer p) == gread h p))
  [SMTPat (buffer_as_seq h (gbuffer_of_array_pointer p))]

val buffer_as_seq_gsub_buffer
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_as_seq h (gsub_buffer b i len) == Seq.slice (buffer_as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len)))
  [SMTPat (buffer_as_seq h (gsub_buffer b i len))]

val gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Ghost (pointer t)
  (requires (UInt32.v i < UInt32.v (buffer_length b)))
  (ensures (fun _ -> True))

val pointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: HST.Stack (pointer t)
  (requires (fun h -> UInt32.v i < UInt32.v (buffer_length b) /\ buffer_live h b))
  (ensures (fun h p h' -> UInt32.v i < UInt32.v (buffer_length b) /\ h' == h /\ p == gpointer_of_buffer_cell b i))

val gpointer_of_buffer_cell_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v len
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v len /\
    gpointer_of_buffer_cell (gsub_buffer b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)
  ))

let gpointer_of_buffer_cell_gsub_buffer'
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v len
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v len /\
    gpointer_of_buffer_cell (gsub_buffer b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)
  ))
  [SMTPat (gpointer_of_buffer_cell (gsub_buffer b i1 len) i2)]
= gpointer_of_buffer_cell_gsub_buffer b i1 len i2

val live_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (
    UInt32.v i < UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i < UInt32.v (buffer_length b) /\
    (live h (gpointer_of_buffer_cell b i) <==> buffer_live h b)
  ))
  [SMTPat (live h (gpointer_of_buffer_cell b i))]

val gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < 1))
  (ensures (UInt32.v i < 1 /\ gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i == p))
  [SMTPat (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) i)]

val gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (p: pointer (TArray length t))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i == gcell p i))
  [SMTPat (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i)]

val frameOf_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ frameOf (gpointer_of_buffer_cell b i) == frameOf_buffer b))
  [SMTPat (frameOf (gpointer_of_buffer_cell b i))]

val as_addr_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ as_addr (gpointer_of_buffer_cell b i) == buffer_as_addr b))
  [SMTPat (as_addr (gpointer_of_buffer_cell b i))]

val gread_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ gread h (gpointer_of_buffer_cell b i) == Seq.index (buffer_as_seq h b) (UInt32.v i)))
  [SMTPat (gread h (gpointer_of_buffer_cell b i))]

val gread_gpointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ gread h (gpointer_of_buffer_cell b i) == Seq.index (buffer_as_seq h b) (UInt32.v i)))

val index_buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: nat)
: Lemma
  (requires (i < UInt32.v (buffer_length b)))
  (ensures (i < UInt32.v (buffer_length b) /\ Seq.index (buffer_as_seq h b) i == gread h (gpointer_of_buffer_cell b (UInt32.uint_to_t i))))
  [SMTPat (Seq.index (buffer_as_seq h b) i)]

val gsingleton_buffer_of_pointer_gcell
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
  (i: UInt32.t)
: Lemma
  (requires (
    UInt32.v i < UInt32.v len
  ))
  (ensures (
    UInt32.v i < UInt32.v len /\
    gsingleton_buffer_of_pointer (gcell p i) == gsub_buffer (gbuffer_of_array_pointer p) i 1ul
  ))
  [SMTPat (gsingleton_buffer_of_pointer (gcell p i))]

val gsingleton_buffer_of_pointer_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (
    UInt32.v i < UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i < UInt32.v (buffer_length b) /\
    gsingleton_buffer_of_pointer (gpointer_of_buffer_cell b i) == gsub_buffer b i 1ul
  ))
  [SMTPat (gsingleton_buffer_of_pointer (gpointer_of_buffer_cell b i))]

(* The readable permission lifted to buffers. *)

val buffer_readable
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0

val buffer_readable_buffer_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (buffer_readable h b))
  (ensures (buffer_live h b))
  [SMTPatOr [
    [SMTPat (buffer_readable h b)];
    [SMTPat (buffer_live h b)];
  ]]

val buffer_readable_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: pointer t)
: Lemma
  (ensures (buffer_readable h (gsingleton_buffer_of_pointer p) <==> readable h p))
  [SMTPat (buffer_readable h (gsingleton_buffer_of_pointer p))]

val buffer_readable_gbuffer_of_array_pointer
  (#len: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (buffer_readable h (gbuffer_of_array_pointer p) <==> readable h p))
  [SMTPat (buffer_readable h (gbuffer_of_array_pointer p))]

val buffer_readable_gsub_buffer
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_readable h b))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ buffer_readable h (gsub_buffer b i len)))
  [SMTPat (buffer_readable h (gsub_buffer b i len))]

val readable_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ buffer_readable h b))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ readable h (gpointer_of_buffer_cell b i)))
  [SMTPat (readable h (gpointer_of_buffer_cell b i))]

val buffer_readable_intro
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (
    buffer_live h b /\ (
     forall (i: UInt32.t) .
     UInt32.v i < UInt32.v (buffer_length b) ==>
     readable h (gpointer_of_buffer_cell b i)
  )))
  (ensures (buffer_readable h b))
//  [SMTPat (buffer_readable h b)] // TODO: dubious pattern, may trigger unreplayable hints

val buffer_readable_elim
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (
    buffer_readable h b
  ))
  (ensures (
    buffer_live h b /\ (
     forall (i: UInt32.t) .
     UInt32.v i < UInt32.v (buffer_length b) ==>
     readable h (gpointer_of_buffer_cell b i)
  )))


(*** The modifies clause *)

val loc : Type u#0

val loc_none: loc

val loc_union
  (s1 s2: loc)
: GTot loc

(** The following is useful to make Z3 cut matching loops with
modifies_trans and modifies_refl *)
val loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_pointer
  (#t: typ)
  (p: pointer t)
: GTot loc

val loc_buffer
  (#t: typ)
  (b: buffer t)
: GTot loc

val loc_addresses
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc

val loc_regions
  (r: Set.set HS.rid)
: GTot loc


(* Inclusion of memory locations *)

val loc_includes
  (s1 s2: loc)
: GTot Type0

val loc_includes_refl
  (s: loc)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_union_l
  (s1 s2 s: loc)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  [SMTPat (loc_includes (loc_union s1 s2) s)]

val loc_includes_none
  (s: loc)
: Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val loc_includes_pointer_pointer
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Lemma
  (requires (includes p1 p2))
  (ensures (loc_includes (loc_pointer p1) (loc_pointer p2)))
  [SMTPat (loc_includes (loc_pointer p1) (loc_pointer p2))]

val loc_includes_gsingleton_buffer_of_pointer
  (l: loc)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_includes l (loc_pointer p)))
  (ensures (loc_includes l (loc_buffer (gsingleton_buffer_of_pointer p))))
  [SMTPat (loc_includes l (loc_buffer (gsingleton_buffer_of_pointer p)))]

val loc_includes_gbuffer_of_array_pointer
  (l: loc)
  (#len: array_length_t)
  (#t: typ)
  (p: pointer (TArray len t))
: Lemma
  (requires (loc_includes l (loc_pointer p)))
  (ensures (loc_includes l (loc_buffer (gbuffer_of_array_pointer p))))
  [SMTPat (loc_includes l (loc_buffer (gbuffer_of_array_pointer p)))]

val loc_includes_gpointer_of_array_cell
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_includes l (loc_buffer b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_includes l (loc_pointer (gpointer_of_buffer_cell b i))))
  [SMTPat (loc_includes l (loc_pointer (gpointer_of_buffer_cell b i)))]

val loc_includes_gsub_buffer_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_includes l (loc_buffer b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_includes l (loc_buffer (gsub_buffer b i len))))
  [SMTPat (loc_includes l (loc_buffer (gsub_buffer b i len)))]

val loc_includes_gsub_buffer_l
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1))
  (ensures (UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\ loc_includes (loc_buffer (gsub_buffer b i1 len1)) (loc_buffer (gsub_buffer b i2 len2))))
  [SMTPat (loc_includes (loc_buffer (gsub_buffer b i1 len1)) (loc_buffer (gsub_buffer b i2 len2)))]

val loc_includes_addresses_pointer
  (#t: typ)
  (r: HS.rid)
  (s: Set.set nat)
  (p: pointer t)
: Lemma
  (requires (frameOf p == r /\ Set.mem (as_addr p) s))
  (ensures (loc_includes (loc_addresses r s) (loc_pointer p)))
  [SMTPat (loc_includes (loc_addresses r s) (loc_pointer p))]

val loc_includes_addresses_buffer
  (#t: typ)
  (r: HS.rid)
  (s: Set.set nat)
  (p: buffer t)
: Lemma
  (requires (frameOf_buffer p == r /\ Set.mem (buffer_as_addr p) s))
  (ensures (loc_includes (loc_addresses r s) (loc_buffer p)))
  [SMTPat (loc_includes (loc_addresses r s) (loc_buffer p))]

val loc_includes_region_pointer
  (#t: typ)
  (s: Set.set HS.rid)
  (p: pointer t)
: Lemma
  (requires (Set.mem (frameOf p) s))
  (ensures (loc_includes (loc_regions s) (loc_pointer p)))
  [SMTPat (loc_includes (loc_regions s) (loc_pointer p))]

val loc_includes_region_buffer
  (#t: typ)
  (s: Set.set HS.rid)
  (b: buffer t)
: Lemma
  (requires (Set.mem (frameOf_buffer b) s))
  (ensures (loc_includes (loc_regions s) (loc_buffer b)))
  [SMTPat (loc_includes (loc_regions s) (loc_buffer b))]

val loc_includes_region_addresses
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions s) (loc_addresses r a)))
  [SMTPat (loc_includes (loc_regions s) (loc_addresses r a))]

val loc_includes_region_region
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (Set.subset s2 s1))
  (ensures (loc_includes (loc_regions s1) (loc_regions s2)))
  [SMTPat (loc_includes (loc_regions s1) (loc_regions s2))]

val loc_includes_region_union_l
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2))]


(* Disjointness of two memory locations *)

val loc_disjoint
  (s1 s2: loc)
: GTot Type0

val loc_disjoint_sym
  (s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
  [SMTPat (loc_disjoint s1 s2)]

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_disjoint_root
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))
  (ensures (loc_disjoint (loc_pointer p1) (loc_pointer p2)))

val loc_disjoint_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd1 fd2: struct_field l)
: Lemma
  (requires (fd1 <> fd2))
  (ensures (loc_disjoint (loc_pointer (gfield p fd1)) (loc_pointer (gfield p fd2))))
  [SMTPat (loc_disjoint (loc_pointer (gfield p fd1)) (loc_pointer (gfield p fd2)))]

val loc_disjoint_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i1: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 < UInt32.v length /\
    UInt32.v i2 < UInt32.v length /\
    UInt32.v i1 <> UInt32.v i2
  ))
  (ensures (
    UInt32.v i1 < UInt32.v length /\
    UInt32.v i2 < UInt32.v length /\  
    loc_disjoint (loc_pointer (gcell p i1)) (loc_pointer (gcell p i2))
  ))
  [SMTPat (loc_disjoint (loc_pointer (gcell p i1)) (loc_pointer (gcell p i2)))]

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

(* TODO: The following is now wrong, should be replaced with readable

val live_not_equal_disjoint
  (#t: typ)
  (h: HS.mem)
  (p1 p2: pointer t)
: Lemma
  (requires (live h p1 /\ live h p2 /\ equal p1 p2 == false))
  (ensures (disjoint p1 p2))
*)

val live_unused_in_disjoint_strong
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))

val live_unused_in_disjoint
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (loc_disjoint (loc_pointer p1) (loc_pointer p2)))
  [SMTPatOr [
    [SMTPat (loc_disjoint (loc_pointer p1) (loc_pointer p2)); SMTPat (live h p1)];
    [SMTPat (loc_disjoint (loc_pointer p1) (loc_pointer p2)); SMTPat (unused_in p2 h)];
    [SMTPat (live h p1); SMTPat (unused_in p2 h)];
  ]]

val pointer_live_reference_unused_in_disjoint
  (#value1: typ)
  (#value2: Type0)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: HS.reference value2)
: Lemma
  (requires (live h p1 /\ HS.unused_in p2 h))
  (ensures (loc_disjoint (loc_pointer p1) (loc_addresses (HS.frameOf p2) (Set.singleton (HS.as_addr p2)))))
  [SMTPat (live h p1); SMTPat (HS.unused_in p2 h)]

val reference_live_pointer_unused_in_disjoint
  (#value1: Type0)
  (#value2: typ)
  (h: HS.mem)
  (p1: HS.reference value1)
  (p2: pointer value2)
: Lemma
  (requires (HS.contains h p1 /\ unused_in p2 h))
  (ensures (loc_disjoint (loc_addresses (HS.frameOf p1) (Set.singleton (HS.as_addr p1))) (loc_pointer p2)))
  [SMTPat (HS.contains h p1); SMTPat (unused_in p2 h)]

val loc_disjoint_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v (buffer_length b) /\ (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
    UInt32.v i2 + UInt32.v len2 <= UInt32.v i1
  )))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v (buffer_length b) /\
    loc_disjoint (loc_buffer (gsub_buffer b i1 len1)) (loc_buffer (gsub_buffer b i2 len2))
  ))
  [SMTPat (loc_disjoint (loc_buffer (gsub_buffer b i1 len1)) (loc_buffer (gsub_buffer b i2 len2)))]

val loc_disjoint_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 < UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v (buffer_length b) /\ (
    UInt32.v i1 <> UInt32.v i2
  )))
  (ensures (
    UInt32.v i1 < UInt32.v (buffer_length b) /\
    UInt32.v i2 < UInt32.v (buffer_length b) /\
    loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i1)) (loc_pointer (gpointer_of_buffer_cell b i2))
  ))
  [SMTPat (loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i1)) (loc_pointer (gpointer_of_buffer_cell b i2)))]

let loc_disjoint_gpointer_of_buffer_cell_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i))))
  [SMTPat (loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i)))]
= loc_disjoint_includes l (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i))

let loc_disjoint_gpointer_of_buffer_cell_l
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer b) l))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l))
  [SMTPat (loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l)]
= loc_disjoint_includes (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i)) l

val loc_disjoint_addresses
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2))]

val loc_disjoint_pointer_addresses
  (#t: typ)
  (p: pointer t)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> frameOf p \/ (~ (Set.mem (as_addr p) n))))
  (ensures (loc_disjoint (loc_pointer p) (loc_addresses r n)))
  [SMTPat (loc_disjoint (loc_pointer p) (loc_addresses r n))]

val loc_disjoint_buffer_addresses
  (#t: typ)
  (p: buffer t)
  (r: HH.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> frameOf_buffer p \/ (~ (Set.mem (buffer_as_addr p) n))))
  (ensures (loc_disjoint (loc_buffer p) (loc_addresses r n)))
  [SMTPat (loc_disjoint (loc_buffer p) (loc_addresses r n))]
  
val loc_disjoint_regions
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions rs1) (loc_regions rs2)))
  [SMTPat (loc_disjoint (loc_regions rs1) (loc_regions rs2))]

(** The modifies clause proper *)

val modifies
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_loc_regions_intro
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions rs) h1 h2))

val modifies_pointer_elim
  (s: loc)
  (h1 h2: HS.mem)
  (#a': typ)
  (p': pointer a')
: Lemma
  (requires (
    modifies s h1 h2 /\
    live h1 p' /\
    loc_disjoint (loc_pointer p') s
  ))
  (ensures (
    equal_values h1 p' h2 p'
  ))
  [SMTPatOr [
    [ SMTPat (modifies s h1 h2); SMTPat (gread h1 p') ] ;
    [ SMTPat (modifies s h1 h2); SMTPat (readable h1 p') ] ;
    [ SMTPat (modifies s h1 h2); SMTPat (live h1 p') ];
    [ SMTPat (modifies s h1 h2); SMTPat (gread h2 p') ] ;
    [ SMTPat (modifies s h1 h2); SMTPat (readable h2 p') ] ;
    [ SMTPat (modifies s h1 h2); SMTPat (live h2 p') ]
  ] ]

val modifies_buffer_elim
  (#t1: typ)
  (b: buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    buffer_live h b /\
    (UInt32.v (buffer_length b) == 0 ==> buffer_live h' b) /\ // necessary for liveness, because all buffers of size 0 are disjoint for any memory location, so we cannot talk about their liveness individually without referring to a larger nonempty buffer
    modifies p h h'
  ))
  (ensures (
    buffer_live h' b /\ (
      buffer_readable h b ==> (
	buffer_readable h' b /\
	buffer_as_seq h b == buffer_as_seq h' b
  ))))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (buffer_as_seq h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (buffer_readable h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (buffer_live h b) ];
    [ SMTPat (modifies p h h'); SMTPat (buffer_as_seq h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (buffer_readable h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (buffer_live h' b) ]
  ] ]

val modifies_reference_elim
  (#t: Type0)
  (b: HS.reference t)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))) p /\
    HS.contains h b /\
    modifies p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h' b) ]
  ] ]

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

let modifies_0 (h0 h1: HS.mem) : GTot Type0 =
  modifies loc_none h0 h1

let modifies_1 (#t: typ) (p: pointer t) (h0 h1: HS.mem) : GTot Type0 =
  modifies (loc_pointer p) h0 h1

(** Concrete allocators, getters and setters *)

val screate
  (value:typ)
  (s: option (type_of_typ value))
: HST.StackInline (pointer value)
  (requires (fun h -> True))
  (ensures (fun (h0:HS.mem) b h1 ->
       unused_in b h0
     /\ live h1 b
     /\ frameOf b = HS.get_tip h0
     /\ modifies_0 h0 h1
     /\ begin match s with
       | Some s' ->
	 readable h1 b /\
	 gread h1 b == s'
       | _ -> True
       end
  ))

val ecreate
  (t:typ)
  (r:HS.rid)
  (s: option (type_of_typ t))
: HST.ST (pointer t)
  (requires (fun h -> is_eternal_region r /\ HST.witnessed (region_contains_pred r)))
  (ensures (fun (h0:HS.mem) b h1 -> unused_in b h0
    /\ live h1 b
    /\ frameOf b == r
    /\ modifies_0 h0 h1
    /\ begin match s with
      | Some s' ->
	readable h1 b /\
	gread h1 b == s'
      | _ -> True
      end
    /\ ~(is_mm b)))

val field
 (#l: struct_typ)
 (p: pointer (TStruct l))
 (fd: struct_field l)
: HST.Stack (pointer (typ_of_struct_field l fd))
  (requires (fun h -> live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gfield p fd))

val ufield
 (#l: union_typ)
 (p: pointer (TUnion l))
 (fd: struct_field l)
: HST.Stack (pointer (typ_of_struct_field l fd))
  (requires (fun h -> live h p))
  (ensures (fun h0 p' h1 -> h0 == h1 /\ p' == gufield p fd))

val cell
 (#length: array_length_t)
 (#value: typ)
 (p: pointer (TArray length value))
 (i: UInt32.t)
: HST.Stack (pointer value)
  (requires (fun h -> UInt32.v i < UInt32.v length /\ live h p))
  (ensures (fun h0 p' h1 -> UInt32.v i < UInt32.v length /\ h0 == h1 /\ p' == gcell p i))

val read
 (#value: typ)
 (p: pointer value)
: HST.Stack (type_of_typ value)
  (requires (fun h -> readable h p))
  (ensures (fun h0 v h1 -> readable h0 p /\ h0 == h1 /\ v == gread h0 p))

val is_null
  (#t: typ)
  (p: npointer t)
: HST.Stack bool
  (requires (fun h -> nlive h p))
  (ensures (fun h b h' -> h' == h /\ b == g_is_null p))

val write: #a:typ -> b:pointer a -> z:type_of_typ a -> HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b
    /\ modifies_1 b h0 h1
    /\ readable h1 b
    /\ gread h1 b == z ))

(** Given our model, this operation is stateful, however it should be translated
    to a no-op by Karamel, as the tag does not actually exist at runtime.
*)
val write_union_field
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: HST.Stack unit
  (requires (fun h -> live h p))
  (ensures (fun h0 _ h1 -> live h0 p /\ live h1 p
    /\ modifies_1 p h0 h1
    /\ is_active_union_field h1 p fd
  ))

val modifies_fresh_frame_popped
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_regions (HS.mod_set (Set.singleton (HS.get_tip h1)))) s) h1 h2 /\
    (HS.get_tip h2) == (HS.get_tip h1) /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    (HS.get_tip h3) == HS.get_tip h0
  ))
  [SMTPat (HS.fresh_frame h0 h1); SMTPat (HS.popped h2 h3); SMTPat (modifies s h0 h3)]

val modifies_only_live_regions
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

val modifies_loc_addresses_intro
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_regions (Set.singleton r)) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses r a) l) h1 h2))

(* `modifies` and the readable permission *)

(** NOTE: we historically used to have this lemma for arbitrary
pointer inclusion, but that became wrong for unions. *)

val modifies_1_readable_struct
  (#l: struct_typ)
  (f: struct_field l)
  (p: pointer (TStruct l))
  (h h' : HS.mem)
: Lemma
  (requires (readable h p /\ modifies_1 (gfield p f) h h' /\ readable h' (gfield p f)))
  (ensures (readable h' p))
  [SMTPatOr [
    [SMTPat (modifies_1 (gfield p f) h h'); SMTPat (readable h p)];
    [SMTPat (modifies_1 (gfield p f) h h'); SMTPat (readable h' p)];
    [SMTPat (readable h p); SMTPat (readable h' (gfield p f))];
//    [SMTPat (readable h' p); SMTPat (readable h' (gfield p f))]; // this pattern is incomplete
    [SMTPat (readable h p); SMTPat (readable h' p); SMTPat (gfield p f)];
]]

val modifies_1_readable_array
  (#t: typ)
  (#len: array_length_t)
  (i: UInt32.t)
  (p: pointer (TArray len t))
  (h h' : HS.mem)
: Lemma
  (requires (UInt32.v i < UInt32.v len /\ readable h p /\ modifies_1 (gcell p i) h h' /\ readable h' (gcell p i)))
  (ensures (readable h' p))
  [SMTPatOr [
    [SMTPat (modifies_1 (gcell p i) h h'); SMTPat (readable h p)];
    [SMTPat (modifies_1 (gcell p i) h h'); SMTPat (readable h' p)];
    [SMTPat (readable h p); SMTPat (readable h' (gcell p i))];
//    [SMTPat (readable h' p); SMTPat (readable h' (gcell p i))]; // this pattern is incomplete
    [SMTPat (readable h p); SMTPat (readable h' p); SMTPat (gcell p i)];
  ]]

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)		
val read_buffer		
  (#t: typ)		
  (b: buffer t)		
  (i: UInt32.t)		
: HST.Stack (type_of_typ t)		
  (requires (fun h -> UInt32.v i < UInt32.v (buffer_length b) /\ readable h (gpointer_of_buffer_cell b i)))		
  (ensures (fun h v h' -> UInt32.v i < UInt32.v (buffer_length b) /\ h' == h /\ v == Seq.index (buffer_as_seq h b) (UInt32.v i)))		
		
(* buffer write: needs clearer "modifies" clauses *)		
		
val write_buffer		
  (#t: typ)		
  (b: buffer t)		
  (i: UInt32.t)		
  (v: type_of_typ t)		
: HST.Stack unit		
  (requires (fun h -> UInt32.v i < UInt32.v (buffer_length b) /\ buffer_live h b))		
  (ensures (fun h _ h' ->		
    UInt32.v i < UInt32.v (buffer_length b) /\		
    modifies_1 (gpointer_of_buffer_cell b i) h h' /\		
    buffer_live h' b /\		
    readable h' (gpointer_of_buffer_cell b i) /\		
    Seq.index (buffer_as_seq h' b) (UInt32.v i) == v /\		
    (buffer_readable h b ==> buffer_readable h' b)		
  ))		
  
(* unused_in, cont'd *)

val buffer_live_unused_in_disjoint
  (#t1 #t2: typ)
  (h: HS.mem)
  (b1: buffer t1)
  (b2: buffer t2)
: Lemma
  (requires (buffer_live h b1 /\ buffer_unused_in b2 h))
  (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))
  [SMTPat (buffer_live h b1); SMTPat (buffer_unused_in b2 h)]

val pointer_live_buffer_unused_in_disjoint
  (#t1 #t2: typ)
  (h: HS.mem)
  (b1: pointer t1)
  (b2: buffer t2)
: Lemma
  (requires (live h b1 /\ buffer_unused_in b2 h))
  (ensures (loc_disjoint (loc_pointer b1) (loc_buffer b2)))
  [SMTPat (live h b1); SMTPat (buffer_unused_in b2 h)]

val buffer_live_pointer_unused_in_disjoint
  (#t1 #t2: typ)
  (h: HS.mem)
  (b1: buffer t1)
  (b2: pointer t2)
: Lemma
  (requires (buffer_live h b1 /\ unused_in b2 h))
  (ensures (loc_disjoint (loc_buffer b1) (loc_pointer b2)))
  [SMTPat (buffer_live h b1); SMTPat (unused_in b2 h)]

val reference_live_buffer_unused_in_disjoint
  (#t1: Type0)
  (#t2: typ)
  (h: HS.mem)
  (b1: HS.reference t1)
  (b2: buffer t2)
: Lemma
  (requires (HS.contains h b1 /\ buffer_unused_in b2 h))
  (ensures (loc_disjoint (loc_addresses (HS.frameOf b1) (Set.singleton (HS.as_addr b1))) (loc_buffer b2)))
  [SMTPat (HS.contains h b1); SMTPat (buffer_unused_in b2 h)]

val buffer_live_reference_unused_in_disjoint
  (#t1: typ)
  (#t2: Type0)
  (h: HS.mem)
  (b1: buffer t1)
  (b2: HS.reference t2)
: Lemma
  (requires (buffer_live h b1 /\ HS.unused_in b2 h))
  (ensures (loc_disjoint (loc_buffer b1) (loc_addresses (HS.frameOf b2) (Set.singleton (HS.as_addr b2)))))

(* Buffer inclusion without existential quantifiers: remnants of the legacy buffer interface *)

(* Returns the greatest buffer (of the same type) including b *)

val root_buffer
  (#t: typ)
  (b: buffer t)
: GTot (buffer t)

(* Return the "offset" of b within its root buffer *)

val buffer_idx
  (#t: typ)
  (b: buffer t)
: Ghost UInt32.t
  (requires True)
  (ensures (fun y ->
    UInt32.v y + UInt32.v (buffer_length b) <=
      UInt32.v (buffer_length (root_buffer b))
  ))

val buffer_eq_gsub_root
  (#t: typ)
  (b: buffer t)
: Lemma
  (b == gsub_buffer (root_buffer b) (buffer_idx b) (buffer_length b))

val root_buffer_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    root_buffer (gsub_buffer b i len) == root_buffer b
  ))
  [SMTPat (root_buffer (gsub_buffer b i len))]

val buffer_idx_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_idx (gsub_buffer b i len) == UInt32.add (buffer_idx b) i
  ))
  [SMTPat (buffer_idx (gsub_buffer b i len))]

val buffer_includes
  (#t: typ)
  (blarge bsmall: buffer t)
: GTot Type0

val buffer_includes_refl
  (#t: typ)
  (b: buffer t)
: Lemma
  (buffer_includes b b)
  [SMTPat (buffer_includes b b)]

val buffer_includes_trans
  (#t: typ)
  (b1 b2 b3: buffer t)
: Lemma
  (requires (buffer_includes b1 b2 /\ buffer_includes b2 b3))
  (ensures (buffer_includes b1 b3))

val buffer_includes_gsub_r
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_includes b (gsub_buffer b i len)
  ))

val buffer_includes_gsub
  (#t: typ)
  (b: buffer t)
  (i1: UInt32.t)
  (i2: UInt32.t)
  (len1: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 <= UInt32.v i2 /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v (buffer_length b) /\
    UInt32.v i2 + UInt32.v len2 <= UInt32.v (buffer_length b) /\
    buffer_includes (gsub_buffer b i1 len1) (gsub_buffer b i2 len2)
  ))
  [SMTPat (buffer_includes (gsub_buffer b i1 len1) (gsub_buffer b i2 len2))]

val buffer_includes_elim
  (#t: typ)
  (b1 b2: buffer t)
: Lemma
  (requires (
    buffer_includes b1 b2
  ))
  (ensures (
    UInt32.v (buffer_idx b1) <= UInt32.v (buffer_idx b2) /\
    UInt32.v (buffer_idx b2) + UInt32.v (buffer_length b2) <= UInt32.v (buffer_idx b1) + UInt32.v (buffer_length b1) /\
    b2 == gsub_buffer b1 (UInt32.sub (buffer_idx b2) (buffer_idx b1)) (buffer_length b2)
  ))

val buffer_includes_loc_includes
  (#t: typ)
  (b1 b2: buffer t)
: Lemma
  (requires (buffer_includes b1 b2))
  (ensures (loc_includes (loc_buffer b1) (loc_buffer b2)))
  [SMTPatOr [
    [SMTPat (buffer_includes b1 b2)];
    [SMTPat (loc_includes(loc_buffer b1) (loc_buffer b2))]
  ]]



/// Type class instantiation for compositionality with other kinds of memory locations than regions, references or buffers (just in case).
/// No usage pattern has been found yet.

module MG = FStar.ModifiesGen

val cloc_aloc: HS.rid -> nat -> Tot Type0

val cloc_cls: MG.cls cloc_aloc

val cloc_of_loc (l: loc) : Tot (MG.loc cloc_cls)

val loc_of_cloc (l: MG.loc cloc_cls) : Tot loc

val loc_of_cloc_of_loc (l: loc) : Lemma
  (loc_of_cloc (cloc_of_loc l) == l)
  [SMTPat (loc_of_cloc (cloc_of_loc l))]

val cloc_of_loc_of_cloc (l: MG.loc cloc_cls) : Lemma
  (cloc_of_loc (loc_of_cloc l) == l)
  [SMTPat (cloc_of_loc (loc_of_cloc l))]

val loc_includes_to_cloc (l1 l2: loc) : Lemma
  (loc_includes l1 l2 <==> MG.loc_includes (cloc_of_loc l1) (cloc_of_loc l2))

val loc_disjoint_to_cloc (l1 l2: loc) : Lemma
  (loc_disjoint l1 l2 <==> MG.loc_disjoint (cloc_of_loc l1) (cloc_of_loc l2))

val modifies_to_cloc (l: loc) (h1 h2: HS.mem) : Lemma
  (modifies l h1 h2 <==> MG.modifies (cloc_of_loc l) h1 h2)
