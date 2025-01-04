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

module DM = FStar.DependentMap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*** Definitions *)

(** Pointers to data of type t.

    This defines two main types:
    - `npointer (t: typ)`, a pointer that may be "NULL";
    - `pointer (t: typ)`, a pointer that cannot be "NULL"
      (defined as a refinement of `npointer`).

    `nullptr #t` (of type `npointer t`) represents the "NULL" value.
*)

#set-options "--initial_fuel 1 --initial_ifuel 1 --max_fuel 1 --max_ifuel 1"

type step: (from: typ) -> (to: typ) -> Tot Type0 =
  | StepField:
    (l: struct_typ) ->
    (fd: struct_field l) ->
    step (TStruct l) (typ_of_struct_field l fd)
  | StepUField:
    (l: union_typ) ->
    (fd: struct_field l) ->
    step (TUnion l) (typ_of_struct_field l fd)
  | StepCell:
    (length: UInt32.t) ->
    (value: typ) ->
    (index: UInt32.t { UInt32.v index < UInt32.v length } ) ->
    step (TArray length value) value

type path (from: typ) : (to: typ) -> Tot Type0 =
  | PathBase:
    path from from
  | PathStep:
    (through: typ) ->
    (to: typ) ->
    (p: path from through) ->
    (s: step through to) ->
    path from to

let step_typ_depth
  (#from #to: typ)
  (s: step from to)
: Lemma
  (typ_depth from > typ_depth to)
= match s with
  | StepUField l fd
  | StepField l fd ->
    typ_depth_typ_of_struct_field l.fields fd
  | _ -> ()

let rec path_typ_depth
  (#from #to: typ)
  (p: path from to)
: Lemma
  (ensures (
    typ_depth from >= typ_depth to /\ (
      (~ (PathBase? p)) ==> typ_depth from <> typ_depth to
  )))
  (decreases p)
= match p with
  | PathBase -> ()
  | PathStep _ _ p' s ->
    path_typ_depth p';
    step_typ_depth s

(*
private
let not_cell
  (#from #to: typ)
  (p: path from to)
: GTot bool
= match p with
  | PathStep _ _ _ (StepCell _ _ _) -> false
  | _ -> true

private type array_path (from: typ) (to_elem: typ) : (length: UInt32.t) -> Tot Type0 =
| PSingleton:
  (p: path from to_elem { not_cell p } ) ->
  array_path from to_elem 1ul
| PArray:
  length: UInt32.t ->
  path from (TArray length to_elem) ->
  array_path from to_elem length

private let path' (from: typ) (to: typ) : Tot Type0 =
  if TArray? to
  then
    let length = TArray?.length to in
    (array_path from (TArray?.t to) length * (offset: UInt32.t & (length': UInt32.t {UInt32.v offset + UInt32.v length' <= UInt32.v length})))
  else path from to
*)

noeq type _npointer (to : typ): Type0 =
  | Pointer:
    (from: typ) ->
    (contents: HS.aref) ->
    (p: path from to) ->
    _npointer to
  | NullPtr

let npointer (t: typ): Tot Type0 =
  _npointer t

(** The null pointer *)

let nullptr (#t: typ): Tot (npointer t) = NullPtr

let g_is_null (#t: typ) (p: npointer t) : GTot bool =
  match p with
  | NullPtr -> true
  | _ -> false

let g_is_null_intro
  (t: typ)
: Lemma
  (g_is_null (nullptr #t) == true)
= ()

(** Buffers *)

let not_an_array_cell (#t: typ) (p: pointer t) : GTot bool =
  match Pointer?.p p with
  | PathStep _ _ _ (StepCell _ _ _) -> false
  | _ -> true

noeq type buffer_root (t: typ) =
| BufferRootSingleton:
  (p: pointer t { not_an_array_cell p } ) ->
  buffer_root t
| BufferRootArray:
  (#max_length: array_length_t) ->
  (p: pointer (TArray max_length t)) ->
  buffer_root t

let buffer_root_length (#t: typ) (b: buffer_root t): Tot UInt32.t = match b with
| BufferRootSingleton _ -> 1ul
| BufferRootArray #_ #len _ -> len

noeq type _buffer (t: typ) =
| Buffer:
  (broot: buffer_root t) ->
  (bidx: UInt32.t) ->
  (blength: UInt32.t { UInt32.v bidx + UInt32.v blength <= UInt32.v (buffer_root_length broot) } ) ->
  _buffer t
let buffer (t: typ): Tot Type0 = _buffer t

(** Helper for the interpretation of unions.

    A C union is interpreted as a dependent pair of a key and a value (which
    depends on the key). The intent is for the key to be ghost, as it will not
    exist at runtime (C unions are untagged).

    Therefore,
    - `gtdata_get_key` (defined below) is in `GTot`, and
    - `gtdata_get_value` asks for the key `k` to read, and a proof that `k`
      matches the ghost key.
*)

let gtdata (* ghostly-tagged data *)
  (key: eqtype)
  (value: (key -> Tot Type0))
: Tot Type0
= ( k: key & value k )

let _gtdata_get_key
  (#key: eqtype)
  (#value: (key -> Tot Type0))
  (u: gtdata key value)
: Tot key
= dfst u

let gtdata_get_key
  (#key: eqtype)
  (#value: (key -> Tot Type0))
  (u: gtdata key value)
: GTot key // important: must be Ghost, the tag is not actually stored in memory
= _gtdata_get_key u

let gtdata_get_value
  (#key: eqtype)
  (#value: (key -> Tot Type0))
  (u: gtdata key value)
  (k: key)
: Pure (value k)
  (requires (gtdata_get_key u == k))
  (ensures (fun _ -> True))
= let (| _, v |) = u in v

let gtdata_create
  (#key: eqtype)
  (#value: (key -> Tot Type0))
  (k: key)
  (v: value k)
: Pure (gtdata key value)
  (requires True)
  (ensures (fun x -> gtdata_get_key x == k /\ gtdata_get_value x k == v))
= (| k, v |)

let gtdata_extensionality
  (#key: eqtype)
  (#value: (key -> Tot Type0))
  (u1 u2: gtdata key value)
: Lemma
  (requires (
    let k = gtdata_get_key u1 in (
    k == gtdata_get_key u2 /\
    gtdata_get_value u1 k == gtdata_get_value u2 k
  )))
  (ensures (u1 == u2))
= ()

(* Interprets a type code (`typ`) as a FStar type (`Type0`). *)
let rec type_of_typ'
  (t: typ)
: Tot Type0
= match t with
  | TBase b -> type_of_base_typ b
  | TStruct l ->
    struct l
  | TUnion l ->
    union l
  | TArray length t ->
    array length (type_of_typ' t)
  | TPointer t ->
    pointer t
  | TNPointer t ->
    npointer t
  | TBuffer t ->
    buffer t
and struct (l: struct_typ) : Tot Type0 =
  DM.t (struct_field l) (type_of_struct_field' l (fun x -> type_of_typ' x))
and union (l: union_typ) : Tot Type0 =
  gtdata (struct_field l) (type_of_struct_field' l (fun x -> type_of_typ' x))

let rec type_of_typ'_eq (t: typ) : Lemma (type_of_typ' t == type_of_typ t)
  [SMTPat (type_of_typ t)]
=
  match t with
  | TArray _ t' -> type_of_typ'_eq t'
  | TPointer t' -> type_of_typ'_eq t'
  | TNPointer t' -> type_of_typ'_eq t'
  | TBuffer t' -> type_of_typ'_eq t'
  | _ -> ()

(** Interpretation of unions, as ghostly-tagged data
    (see `gtdata` for more information).
*)
let _union_get_key (#l: union_typ) (v: union l) : Tot (struct_field l) = _gtdata_get_key v

let struct_sel (#l: struct_typ) (s: struct l) (f: struct_field l) : Tot (type_of_struct_field l f) =
  DM.sel s f
 
let struct_upd (#l: struct_typ) (s: struct l) (f: struct_field l) (v: type_of_struct_field l f) : Tot (struct l) =
  DM.upd s f v

let struct_create_fun (l: struct_typ) (f: ((fd: struct_field l) -> Tot (type_of_struct_field l fd))) : Tot (struct l) =
  DM.create #(struct_field l) #(type_of_struct_field' l (fun x -> type_of_typ' x)) f

let struct_sel_struct_create_fun l f fd = ()

let union_get_key (#l: union_typ) (v: union l) : GTot (struct_field l) = gtdata_get_key v

let union_get_value #l v fd = gtdata_get_value v fd

let union_create l fd v = gtdata_create fd v

(** For any `t: typ`, `dummy_val t` provides a default value of this type.

    This is useful to represent uninitialized data.
*)
let rec dummy_val
  (t: typ)
: Tot (type_of_typ t)
= match t with
  | TBase b ->
    begin match b with
    | TUInt -> 0
    | TUInt8 -> UInt8.uint_to_t 0
    | TUInt16 -> UInt16.uint_to_t 0
    | TUInt32 -> UInt32.uint_to_t 0
    | TUInt64 -> UInt64.uint_to_t 0
    | TInt -> 0
    | TInt8 -> Int8.int_to_t 0
    | TInt16 -> Int16.int_to_t 0
    | TInt32 -> Int32.int_to_t 0
    | TInt64 -> Int64.int_to_t 0
    | TChar -> 'c'
    | TBool -> false
    | TUnit -> ()
    end
  | TStruct l ->
    struct_create_fun l (fun f -> (
      dummy_val (typ_of_struct_field l f)
    ))
  | TUnion l ->
    let dummy_field : string = List.Tot.hd (List.Tot.map fst l.fields) in
    union_create l dummy_field (dummy_val (typ_of_struct_field l dummy_field))
  | TArray length t -> Seq.create (UInt32.v length) (dummy_val t)
  | TPointer t -> Pointer t HS.dummy_aref PathBase
  | TNPointer t -> NullPtr #t
  | TBuffer t -> Buffer (BufferRootSingleton (Pointer t HS.dummy_aref PathBase)) 0ul 1ul

(** The interpretation of type codes (`typ`) defined previously (`type_of_typ`)
    maps codes to fully defined FStar types. In other words, a struct is
    interpreted as a dependent map where all fields have a well defined value.

    However, in practice, C structures (or any other type) can be uninitialized
    or partially-initialized.

    To account for that:

    - First, we define an alternative interpretation of type codes,
      `otype_of_typ`, which makes uninitialized data explicit (essentially
      wrapping all interpretations with `option`).

      This concrete interpretation is what is stored in the model of the heap,
      and what is manipulated internally. As it is quite verbose, it is not
      exposed to the user.

    - Then, interpretations with explicit uninitialized data (`otype_of_type t`)
      can be mapped to fully-initialized data (`type_of_type t`) by inserting
      dummy values. This is done by the `value_of_ovalue` function.

    - Finally, reading from a fully-initialized data is guarded by a `readable`
      predicate, which ensures that the dummy values cannot be accessed, and
      therefore that reading uninitialized data is actually forbidden.
*)

let rec otype_of_typ
  (t: typ)
: Tot Type0
= match t with
  | TBase b -> option (type_of_base_typ b)
  | TStruct l ->
    option (DM.t (struct_field l) (type_of_struct_field' l otype_of_typ))
  | TUnion l ->
    option (gtdata (struct_field l) (type_of_struct_field' l otype_of_typ))
  | TArray length t ->
    option (array length (otype_of_typ t))
  | TPointer t ->
    option (pointer t)
  | TNPointer t ->
    option (npointer t)
  | TBuffer t ->
    option (buffer t)

let otype_of_struct_field
  (l: struct_typ)
: Tot (struct_field l -> Tot Type0)
= type_of_struct_field' l otype_of_typ

let otype_of_typ_otype_of_struct_field
  (l: struct_typ)
  (f: struct_field l)
: Lemma
  (otype_of_typ (typ_of_struct_field l f) == otype_of_struct_field l f)
  [SMTPat (type_of_typ (typ_of_struct_field l f))]
= ()

let otype_of_typ_base
  (b: base_typ)
: Lemma
  (otype_of_typ (TBase b) == option (type_of_base_typ b))
  [SMTPat (otype_of_typ (TBase b))]
= ()

let otype_of_typ_array
  (len: array_length_t )
  (t: typ)
: Lemma
  (otype_of_typ (TArray len t) == option (array len (otype_of_typ t)))
  [SMTPat (otype_of_typ (TArray len t))]
= ()

let ostruct (l: struct_typ) = option (DM.t (struct_field l) (otype_of_struct_field l))

let ostruct_sel (#l: struct_typ) (s: ostruct l { Some? s }) (f: struct_field l) : Tot (otype_of_struct_field l f) =
  DM.sel (Some?.v s) f

let ostruct_upd (#l: struct_typ) (s: ostruct l { Some? s }) (f: struct_field l) (v: otype_of_struct_field l f) : Tot (s': ostruct l { Some? s' } ) =
  Some (DM.upd (Some?.v s) f v)

let ostruct_create (l: struct_typ) (f: ((fd: struct_field l) -> Tot (otype_of_struct_field l fd))) : Tot (s': ostruct l { Some? s' } ) =
  Some (DM.create #(struct_field l) #(otype_of_struct_field l) f)

let otype_of_typ_struct
  (l: struct_typ)
: Lemma
  (otype_of_typ (TStruct l) == ostruct l)
  [SMTPat (otype_of_typ (TStruct l))]
= assert_norm(otype_of_typ (TStruct l) == ostruct l)

let ounion (l: struct_typ) = option (gtdata (struct_field l) (otype_of_struct_field l))

let ounion_get_key (#l: union_typ) (v: ounion l { Some? v } ) : Tot (struct_field l) = _gtdata_get_key (Some?.v v)

let ounion_get_value
  (#l: union_typ)
  (v: ounion l { Some? v } )
  (fd: struct_field l)
: Pure (otype_of_struct_field l fd)
  (requires (ounion_get_key v == fd))
  (ensures (fun _ -> True))
= gtdata_get_value (Some?.v v) fd

let ounion_create
  (l: union_typ)
  (fd: struct_field l)
  (v: otype_of_struct_field l fd)
: Tot (ounion l)
= Some (gtdata_create fd v)

let otype_of_typ_union
  (l: union_typ)
: Lemma
  (otype_of_typ (TUnion l) == ounion l)
  [SMTPat (otype_of_typ (TUnion l))]
= assert_norm (otype_of_typ (TUnion l) == ounion l)

let struct_field_is_readable
  (l: struct_typ)
  (ovalue_is_readable: (
    (t: typ) ->
    (v: otype_of_typ t) ->
    Pure bool
    (requires (t << l))
    (ensures (fun _ -> True))
  ))
  (v: ostruct l { Some? v } )
  (s: string)
: Tot bool
= if List.Tot.mem s (List.Tot.map fst l.fields)
  then ovalue_is_readable (typ_of_struct_field l s) (ostruct_sel v s)
  else true

let rec ovalue_is_readable
  (t: typ)
  (v: otype_of_typ t)
: Tot bool
  (decreases t)
= match t with
  | TStruct l ->
    let (v: ostruct l) = v in
    Some? v && (
      let keys = List.Tot.map fst l.fields in
      let pred
        (t': typ)
        (v: otype_of_typ t')
      : Pure bool
        (requires (t' << l))
        (ensures (fun _ -> True))
      = ovalue_is_readable t' v
      in
      List.Tot.for_all (struct_field_is_readable l pred v) keys
    )
  | TUnion l ->
    let v : ounion l = v in
    Some? v && (
      let k = ounion_get_key v in
      ovalue_is_readable (typ_of_struct_field l k) (ounion_get_value v k)
    )
  | TArray len t ->
    let (v: option (array len (otype_of_typ t))) = v in
    Some? v &&
    Seq.for_all (ovalue_is_readable t) (Some?.v v)
  | TBase t ->
    let (v: option (type_of_base_typ t)) = v in
    Some? v
  | TPointer t ->
    let (v: option (pointer t)) = v in
    Some? v
  | TNPointer t ->
    let (v: option (npointer t)) = v in
    Some? v
  | TBuffer t ->
    let (v: option (buffer t)) = v in
    Some? v

let ovalue_is_readable_struct_intro'
  (l: struct_typ)
  (v: otype_of_typ (TStruct l))
: Lemma
  (requires (
    let (v: ostruct l) = v in (
    Some? v /\
    List.Tot.for_all (struct_field_is_readable l (fun x y -> ovalue_is_readable x y) v) (List.Tot.map fst l.fields)
  )))
  (ensures (ovalue_is_readable (TStruct l) v))
= assert_norm (ovalue_is_readable (TStruct l) v == true)

let ovalue_is_readable_struct_intro
  (l: struct_typ)
  (v: otype_of_typ (TStruct l))
: Lemma
  (requires (
    let (v: ostruct l) = v in (
    Some? v /\ (
    forall (f: struct_field l) .
    ovalue_is_readable (typ_of_struct_field l f) (ostruct_sel v f)
  ))))
  (ensures (ovalue_is_readable (TStruct l) v))
= List.Tot.for_all_mem (struct_field_is_readable l (fun x y -> ovalue_is_readable x y) v) (List.Tot.map fst l.fields);
  ovalue_is_readable_struct_intro' l v

let ovalue_is_readable_struct_elim
  (l: struct_typ)
  (v: otype_of_typ (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (ovalue_is_readable (TStruct l) v))
  (ensures (
    let (v: ostruct l) = v in (
    Some? v /\
    ovalue_is_readable (typ_of_struct_field l fd) (ostruct_sel v fd)
  )))
  [SMTPat (ovalue_is_readable (typ_of_struct_field l fd) (ostruct_sel v fd))]
= let (v: ostruct l) = v in
  assert_norm (ovalue_is_readable (TStruct l) v == List.Tot.for_all (struct_field_is_readable l (fun x y -> ovalue_is_readable x y) v) (List.Tot.map fst l.fields));
  assert (List.Tot.for_all (struct_field_is_readable l (fun x y -> ovalue_is_readable x y) v) (List.Tot.map fst l.fields));
  List.Tot.for_all_mem (struct_field_is_readable l (fun x y -> ovalue_is_readable x y) v) (List.Tot.map fst l.fields);
  assert (ovalue_is_readable (typ_of_struct_field l fd) (ostruct_sel v fd))

let ovalue_is_readable_array_elim
  (#len: array_length_t )
  (#t: typ)
  (v: otype_of_typ (TArray len t))
  (i: UInt32.t { UInt32.v i < UInt32.v len } )
: Lemma
  (requires (ovalue_is_readable (TArray len t) v))
  (ensures (
    let (v: option (array len (otype_of_typ t))) = v in (
    Some? v /\
    ovalue_is_readable t (Seq.index (Some?.v v) (UInt32.v i))
  )))
= ()

let ovalue_is_readable_array_intro
  (#len: array_length_t )
  (#t: typ)
  (v: otype_of_typ (TArray len t))
: Lemma
  (requires (
    let (v: option (array len (otype_of_typ t))) = v in (
    Some? v /\ (
    forall (i: UInt32.t { UInt32.v i < UInt32.v len } ) .
    ovalue_is_readable t (Seq.index (Some?.v v) (UInt32.v i))
  ))))
  (ensures (ovalue_is_readable (TArray len t) v))
= let (v: option (array len (otype_of_typ t))) = v in
  let (v: array len (otype_of_typ t)) = Some?.v v in
  let f
    (i: nat { i < UInt32.v len } )
  : Lemma
    (ovalue_is_readable t (Seq.index v i))
  = let (j : UInt32.t { UInt32.v j < UInt32.v len } ) = UInt32.uint_to_t i in
    assert (ovalue_is_readable t (Seq.index v (UInt32.v j)))
  in
  Classical.forall_intro f

let ostruct_field_of_struct_field
  (l: struct_typ)
  (ovalue_of_value: (
    (t: typ) ->
    (v: type_of_typ t) ->
    Pure (otype_of_typ t)
    (requires (t << l))
    (ensures (fun _ -> True))
  ))
  (v: struct l)
  (f: struct_field l)
: Tot (otype_of_struct_field l f)
= ovalue_of_value (typ_of_struct_field l f) (struct_sel #l v f)

(* TODO: move to Seq.Base *)

let seq_init_index
  (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a)) (i: nat)
: Lemma
  (requires (i < len))
  (ensures (i < len /\ Seq.index (Seq.init len contents) i == contents i))
  [SMTPat (Seq.index (Seq.init len contents) i)]
= Seq.init_index len contents

let rec ovalue_of_value
  (t: typ)
  (v: type_of_typ t)
: Tot (otype_of_typ t)
  (decreases t)
= match t with
  | TStruct l ->
    let oval
      (t' : typ)
      (v' : type_of_typ t')
    : Pure (otype_of_typ t')
      (requires (t' << l))
      (ensures (fun _ -> True))
    = ovalue_of_value t' v'
    in
    ostruct_create l (ostruct_field_of_struct_field l oval v)
  | TArray len t ->
    let (v: array len (type_of_typ t)) = v in
    assert (UInt32.v len == Seq.length v);
    let f
      (i: nat {i < UInt32.v len})
    : Tot (otype_of_typ t)
    = ovalue_of_value t (Seq.index v i)
    in
    let (v': array len (otype_of_typ t)) = Seq.init (UInt32.v len) f in
    Some v'
  | TUnion l ->
    let (v: union l) = v in
    let k = _union_get_key v in
    ounion_create l k (ovalue_of_value (typ_of_struct_field l k) (union_get_value v k))
  | _ -> Some v

let ovalue_is_readable_ostruct_field_of_struct_field
  (l: struct_typ)
  (ih: (
    (t: typ) ->
    (v: type_of_typ t) ->
    Lemma
    (requires (t << l))
    (ensures (ovalue_is_readable t (ovalue_of_value t v)))
  ))
  (v: struct l)
  (f: struct_field l)
: Lemma
  (ovalue_is_readable (typ_of_struct_field l f) (ostruct_field_of_struct_field l ovalue_of_value v f))
= ih (typ_of_struct_field l f) (struct_sel #l v f)

let rec ovalue_is_readable_ovalue_of_value
  (t: typ)
  (v: type_of_typ t)
: Lemma
  (requires True)
  (ensures (ovalue_is_readable t (ovalue_of_value t v)))
  (decreases t)
  [SMTPat (ovalue_is_readable t (ovalue_of_value t v))]
= match t with
  | TStruct l ->
    let (v: struct l) = v in
    let (v': ostruct l) = ovalue_of_value (TStruct l) v in
    let phi
      (t: typ)
      (v: type_of_typ t)
    : Lemma
      (requires (t << l))
      (ensures (ovalue_is_readable t (ovalue_of_value t v)))
    = ovalue_is_readable_ovalue_of_value t v
    in
    Classical.forall_intro (ovalue_is_readable_ostruct_field_of_struct_field l phi v);
    ovalue_is_readable_struct_intro l v'
  | TArray len t ->
    let (v: array len (type_of_typ t)) = v in
    let (v': otype_of_typ (TArray len t)) = ovalue_of_value (TArray len t) v in
    let (v': array len (otype_of_typ t)) = Some?.v v' in
    let phi
      (i: nat { i < Seq.length v' } )
    : Lemma
      (ovalue_is_readable t (Seq.index v' i))
    = ovalue_is_readable_ovalue_of_value t (Seq.index v i)
    in
    Classical.forall_intro phi
  | TUnion l ->
    let (v: union l) = v in
    let k = _union_get_key v in
    ovalue_is_readable_ovalue_of_value (typ_of_struct_field l k) (union_get_value v k)
  | _ -> ()

let rec value_of_ovalue
  (t: typ)
  (v: otype_of_typ t)
: Tot (type_of_typ t)
  (decreases t)
= match t with
  | TStruct l ->
    let (v: ostruct l) = v in
    if Some? v
    then
      let phi
        (f: struct_field l)
      : Tot (type_of_struct_field l f)
      = value_of_ovalue (typ_of_struct_field l f) (ostruct_sel v f)
      in
      struct_create_fun l phi
    else dummy_val t
  | TArray len t' ->
    let (v: option (array len (otype_of_typ t'))) = v in
    begin match v with
    | None -> dummy_val t
    | Some v ->
      let phi
        (i: nat { i < UInt32.v len } )
      : Tot (type_of_typ t')
      = value_of_ovalue t' (Seq.index v i)
      in
      Seq.init (UInt32.v len) phi
    end
  | TUnion l ->
    let (v: ounion l) = v in
    begin match v with
    | None -> dummy_val t
    | _ ->
      let k = ounion_get_key v in
      union_create l k (value_of_ovalue (typ_of_struct_field l k) (ounion_get_value v k))
    end
  | TBase b ->
    let (v: option (type_of_base_typ b)) = v in
    begin match v with
    | None -> dummy_val t
    | Some v -> v
    end
  | TPointer t' ->
    let (v: option (pointer t')) = v in
    begin match v with
    | None -> dummy_val t
    | Some v -> v
    end
  | TNPointer t' ->
    let (v: option (npointer t')) = v in
    begin match v with
    | None -> dummy_val t
    | Some v -> v
    end
  | TBuffer t' ->
    let (v: option (buffer t')) = v in
    begin match v with
    | None -> dummy_val t
    | Some v -> v
    end

let ovalue_of_value_array_index
  (#len: array_length_t)
  (t' : typ)
  (v: array len (type_of_typ t'))
  (sv: array len (otype_of_typ t'))
: Lemma
  (requires (ovalue_of_value (TArray len t') v == Some sv))
  (ensures (forall (i: nat) . i < UInt32.v len ==> Seq.index sv i == ovalue_of_value t' (Seq.index v i)))
= ()


let value_of_ovalue_array_index
  (#len: array_length_t)
  (t': typ)
  (sv: array len (otype_of_typ t'))
: Lemma
  (ensures (forall (i: nat) . i < UInt32.v len ==> Seq.index (value_of_ovalue (TArray len t') (Some sv)) i == value_of_ovalue t' (Seq.index sv i)))
= ()

#set-options "--z3rlimit 16"

let rec value_of_ovalue_of_value
  (t: typ)
  (v: type_of_typ t)
: Lemma
  (value_of_ovalue t (ovalue_of_value t v) == v)
  [SMTPat (value_of_ovalue t (ovalue_of_value t v))]
= match t with
  | TStruct l ->
    let v : struct l = v in
    let v' : struct l = value_of_ovalue t (ovalue_of_value t v) in
    let phi
      (f: struct_field l)
    : Lemma
      (struct_sel #l v' f == struct_sel #l v f)
    = value_of_ovalue_of_value (typ_of_struct_field l f) (struct_sel #l v f)
    in
    Classical.forall_intro phi;
    DM.equal_intro v' v;
    DM.equal_elim #(struct_field l) #(type_of_struct_field' l (fun x -> type_of_typ' x)) v' v
  | TArray len t' ->
    let (v: array len (type_of_typ t')) = v in
    let ov : option (array len (otype_of_typ t')) = ovalue_of_value (TArray len t') v in
    assert (Some? ov);
    let sv : array len (otype_of_typ t') = Some?.v ov in
    assert (Seq.length sv == UInt32.v len);
//    assert (forall (i : nat { i < UInt32.v len } ) . Seq.index sv i == ovalue_of_value t' (Seq.index v i));
    ovalue_of_value_array_index t' v sv;
    let v'  : array len (type_of_typ t') = value_of_ovalue t ov in
    assert (Seq.length v' == UInt32.v len);
//    assert (forall (i: nat { i < UInt32.v len } ) . Seq.index v' i == value_of_ovalue t' (Seq.index sv i));
    value_of_ovalue_array_index t' sv;
    let phi
      (i: nat { i < UInt32.v len } )
    : Lemma
      (value_of_ovalue t' (ovalue_of_value t' (Seq.index v i)) == Seq.index v i)
    = value_of_ovalue_of_value t' (Seq.index v i)
    in
    Classical.forall_intro phi;
    Seq.lemma_eq_intro v' v;
    Seq.lemma_eq_elim v' v
  | TUnion l ->
    let v : union l = v in
    let k = _union_get_key v in
    value_of_ovalue_of_value (typ_of_struct_field l k) (union_get_value v k)
  | _ -> ()

let none_ovalue
  (t: typ)
: Tot (otype_of_typ t)
= match t with
  | TStruct l -> (None <: ostruct l)
  | TArray len t' -> (None <: option (array len (otype_of_typ t')))
  | TUnion l -> (None <: ounion l)
  | TBase b -> (None <: option (type_of_base_typ b))
  | TPointer t' -> (None <: option (pointer t'))
  | TNPointer t' -> (None <: option (npointer t'))
  | TBuffer t' -> (None <: option (buffer t'))

let not_ovalue_is_readable_none_ovalue
  (t: typ)
: Lemma
  (ovalue_is_readable t (none_ovalue t) == false)
= ()

(*** Semantics of pointers *)

(** Pointer paths *)

let step_sel
  (#from: typ)
  (#to: typ)
  (m': otype_of_typ from)
  (s: step from to)
= match s with
  | StepField l fd ->
    let (m': ostruct l) = m' in
    begin match m' with
    | None -> none_ovalue to
    | _ -> ostruct_sel m' fd
    end
  | StepUField l fd ->
    let (m' : ounion l) = m' in
    begin match m' with
    | None -> none_ovalue to
    | _ ->
      if fd = ounion_get_key m'
      then ounion_get_value m' fd
      else none_ovalue to
    end
  | StepCell length value i ->
    let (m': option (array length (otype_of_typ to))) = m' in
    begin match m' with
    | None -> none_ovalue to
    | Some m' -> Seq.index m' (UInt32.v i)
    end

(* TODO: we used to have this:
<<<
let ovalue_is_readable_step_sel
  (#from: typ)
  (#to: typ)
  (m': otype_of_typ from)
  (s: step from to)
: Lemma
  (requires (ovalue_is_readable from m'))
  (ensures (ovalue_is_readable to (step_sel m' s)))
  [SMTPat (ovalue_is_readable to (step_sel m' s))]
= match s with
  | StepField l fd -> ovalue_is_readable_struct_elim l m' fd
  | _ -> ()
>>>
Which is, of course, wrong with unions. So we have to specialize this rule for each step:
*)

let ovalue_is_readable_step_sel_cell
  (#length: array_length_t)
  (#value: typ)
  (m': otype_of_typ (TArray length value))
  (index: UInt32.t { UInt32.v index < UInt32.v length } )
: Lemma
  (requires (ovalue_is_readable (TArray length value) m'))
  (ensures (ovalue_is_readable value (step_sel m' (StepCell length value index))))
  [SMTPat (ovalue_is_readable value (step_sel m' (StepCell length value index)))]
= ()

let ovalue_is_readable_step_sel_field
  (#l: struct_typ)
  (m: ostruct l)
  (fd: struct_field l)
: Lemma
  (requires (ovalue_is_readable (TStruct l) m))
  (ensures (ovalue_is_readable (typ_of_struct_field l fd) (step_sel m (StepField l fd))))
  [SMTPat (ovalue_is_readable (typ_of_struct_field l fd) (step_sel m (StepField l fd)))]
= ()

let ovalue_is_readable_step_sel_union_same
  (#l: union_typ)
  (m: ounion l)
  (fd: struct_field l)
: Lemma
  (requires (
    ovalue_is_readable (TUnion l) m /\
    ounion_get_key m == fd
  ))
  (ensures (ovalue_is_readable (typ_of_struct_field l fd) (step_sel m (StepUField l fd))))
= ()

let step_sel_none_ovalue
  (#from: typ)
  (#to: typ)
  (s: step from to)
: Lemma
  (step_sel (none_ovalue from) s == none_ovalue to)
= ()

let rec path_sel
  (#from: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (p: path from to)
: Tot (otype_of_typ to)
  (decreases p)
= match p with
  | PathBase -> m
  | PathStep through' to' p' s ->
    let (m': otype_of_typ through') = path_sel m p' in
    step_sel m' s

let rec path_sel_none_ovalue
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_sel (none_ovalue from) p == none_ovalue to))
  (decreases p)
= match p with
  | PathBase -> ()
  | PathStep through' to' p' s ->
    path_sel_none_ovalue p'

let step_upd
  (#from: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (s: step from to)
  (v: otype_of_typ to)
: Tot (otype_of_typ from)
  (decreases s)
= match s with
  | StepField l fd ->
    let (m: ostruct l) = m in
    begin match m with
    | None ->
      (* whole structure does not exist yet,
         so create one with only one field initialized,
         and all others uninitialized *)
      let phi
        (fd' : struct_field l)
      : Tot (otype_of_struct_field l fd')
      = if fd' = fd
        then v
        else none_ovalue (typ_of_struct_field l fd')
      in
      ostruct_create l phi
    | Some _ -> ostruct_upd m fd v
    end
  | StepCell len _ i ->
    let (m: option (array len (otype_of_typ to))) = m in
    begin match m with
    | None ->
      (* whole array does not exist yet,
         so create one with only one cell initialized,
         and all others uninitialized *)
      let phi
        (j: nat { j < UInt32.v len } )
      : Tot (otype_of_typ to)
      = if j = UInt32.v i
        then v
        else none_ovalue to
      in
      let (m' : option (array len (otype_of_typ to))) =
        Some (Seq.init (UInt32.v len) phi)
      in
      m'
    | Some m ->
      let (m' : option (array len (otype_of_typ to))) =
        Some (Seq.upd m (UInt32.v i) v)
      in
      m'
    end
  | StepUField l fd ->
    (* overwrite the whole union with the new field *)
    ounion_create l fd v

let step_sel_upd_same
  (#from: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (s: step from to)
  (v: otype_of_typ to)
: Lemma
  (step_sel (step_upd m s v) s == v)
= ()

let rec path_upd
  (#from: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (p: path from to)
  (v: otype_of_typ to)
: Tot (otype_of_typ from)
  (decreases p)
= match p with
  | PathBase -> v
  | PathStep through' to' p' st ->
    let s = path_sel m p' in
    path_upd m p' (step_upd s st v)

let rec path_sel_upd_same
  (#from: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (p: path from to)
  (v: otype_of_typ to)
: Lemma
  (requires True)
  (ensures (path_sel (path_upd m p v) p == v))
  (decreases p)
  [SMTPat (path_sel (path_upd m p v) p)]
= match p with
  | PathBase -> ()
  | PathStep through' to' p' st ->
    let s = path_sel m p' in
    step_sel_upd_same s st v;
    let s' = step_upd s st v in
    path_sel_upd_same m p' s'

let rec path_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (q: path through to)
: Pure (path from to)
  (requires True)
  (ensures (fun _ -> True))
  (decreases q)
= match q with
  | PathBase -> p
  | PathStep through' to' q' st -> PathStep through' to' (path_concat p q') st

let path_concat_base_r
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (ensures (path_concat p PathBase == p))
= ()

let rec path_concat_base_l
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_concat PathBase p == p))
  (decreases p)
  [SMTPat (path_concat PathBase p)]
= match p with
  | PathBase -> ()
  | PathStep _ _ p' _ -> path_concat_base_l p'

let rec path_concat_assoc
  (#t0 #t1 #t2 #t3: typ)
  (p01: path t0 t1)
  (p12: path t1 t2)
  (p23: path t2 t3)
: Lemma
  (requires True)
  (ensures (path_concat (path_concat p01 p12) p23 == path_concat p01 (path_concat p12 p23)))
  (decreases p23)
= match p23 with
  | PathBase -> ()
  | PathStep _ _ p23' _ -> path_concat_assoc p01 p12 p23'

let rec path_sel_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_sel m (path_concat p q) == path_sel (path_sel m p) q))
  (decreases q)
  [SMTPat (path_sel m (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathStep _ _ q' _ -> path_sel_concat m p q'

let rec path_upd_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (m: otype_of_typ from)
  (p: path from through)
  (q: path through to)
  (v: otype_of_typ to)
: Lemma
  (requires True)
  (ensures (path_upd m (path_concat p q) v == path_upd m p (path_upd (path_sel m p) q v)))
  (decreases q)
  [SMTPat (path_upd m (path_concat p q) v)]
= match q with
  | PathBase -> ()
  | PathStep through' to' q' st ->
    let (s: otype_of_typ through') = path_sel m (path_concat p q') in
    let (s': otype_of_typ through') = step_upd s st v in
    path_upd_concat m p q' s'

// TODO: rename as: prefix_of; use infix notation (p1 `prefix_of` p2)
let rec path_includes
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2)
: Ghost bool
  (requires True)
  (ensures (fun _ -> True))
  (decreases p2)
= (to1 = to2 && p1 = p2) || (match p2 with
  | PathBase -> false
  | PathStep _ _ p2' _ ->
    path_includes p1 p2'
  )

let rec path_includes_base
  (#from: typ)
  (#to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes (PathBase #from) p))
  (decreases p)
  [SMTPat (path_includes PathBase p)]
= match p with
  | PathBase -> ()
  | PathStep _ _ p2' _ -> path_includes_base p2'

let path_includes_refl
  (#from #to: typ)
  (p: path from to)
: Lemma
  (requires True)
  (ensures (path_includes p p))
  [SMTPat (path_includes p p)]
= ()

let path_includes_step_r
  (#from #through #to: typ)
  (p: path from through)
  (s: step through to)
: Lemma
  (requires True)
  (ensures (path_includes p (PathStep through to p s)))
  [SMTPat (path_includes p (PathStep through to p s))]
= ()

let rec path_includes_trans
  (#from #to1 #to2 #to3: typ)
  (p1: path from to1)
  (p2: path from to2)
  (p3: path from to3  {path_includes p1 p2 /\ path_includes p2 p3})
: Lemma
  (requires True)
  (ensures (path_includes p1 p3))
  (decreases p3)
= FStar.Classical.or_elim
    #(to2 == to3 /\ p2 == p3)
    #(match p3 with
      | PathBase -> False
      | PathStep _ _ p3' _ ->
	path_includes p2 p3')
    #(fun _ -> path_includes p1 p3)
    (fun _ -> ())
    (fun _ -> match p3 with
      | PathBase -> assert False
      | PathStep _ _ p3' _ ->
	path_includes_trans p1 p2 p3'
    )

let rec path_includes_ind
  (#from: typ)
  (x:((#to1: typ) ->
      (#to2: typ) ->
      (p1: path from to1) ->
      (p2: path from to2 {path_includes p1 p2} ) ->
      GTot Type0))
  (h_step:
   ((#through: typ) ->
    (#to: typ) ->
    (p: path from through) ->
    (s: step through to { path_includes p (PathStep through to p s) } ) ->
    Lemma (x p (PathStep through to p s))))
  (h_refl:
   ((#to: typ) ->
    (p: path from to {path_includes p p}) ->
    Lemma (x p p)))
  (h_trans:
   ((#to1: typ) ->
    (#to2: typ) ->
    (#to3: typ) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (p3: path from to3 {path_includes p1 p2 /\ path_includes p2 p3 /\ path_includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3)))
  (#to1: typ)
  (#to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_includes p1 p2})
: Lemma
  (requires True)
  (ensures (x p1 p2))
  (decreases p2)
= FStar.Classical.or_elim
    #(to1 == to2 /\ p1 == p2)
    #(match p2 with
      | PathBase -> False
      | PathStep _ _  p' _ -> path_includes p1 p')
    #(fun _ -> x p1 p2)
    (fun _ -> h_refl p1)
    (fun _ -> match p2 with
     | PathBase -> assert False
     | PathStep _ _  p2' st ->
       let _ = path_includes_ind x h_step h_refl h_trans p1 p2' in
       let _ = path_includes_step_r p2' st in
       let _ = h_step p2' st in
       h_trans p1 p2' p2
    )

let rec path_length
  (#from #to: typ)
  (p: path from to)
: Tot nat
  (decreases p)
= match p with
  | PathBase -> 0
  | PathStep _ _ p' _ -> 1 + path_length p'

let path_includes_length
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_includes p1 p2})
: Lemma
  (ensures (path_length p1 <= path_length p2))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> path_length p1_ <= path_length p2_)
    (fun #through #to p st -> ())
    (fun #to p -> ())
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ -> ())
    p1 p2

let path_includes_step_l
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (s: step through to)
: Lemma
  (requires True)
  (ensures (~ (path_includes (PathStep through to p s) p)))
  [SMTPat (path_includes (PathStep through to p s) p)]
= assert (path_length (PathStep through to p s) > path_length p);
  FStar.Classical.forall_intro (path_includes_length #from #to #through (PathStep through to p s))

let rec path_includes_concat
  (#from: typ)
  (#through: typ)
  (#to: typ)
  (p: path from through)
  (q: path through to)
: Lemma
  (requires True)
  (ensures (path_includes p (path_concat p q)))
  (decreases q)
  [SMTPat (path_includes p (path_concat p q))]
= match q with
  | PathBase -> ()
  | PathStep _ _ q' _ -> path_includes_concat p q'

let path_includes_exists_concat
  (#from #through: typ)
  (p: path from through)
  (#to: typ)
  (q: path from to { path_includes p q } )
: Lemma
  (ensures (exists (r: path through to) . q == path_concat p r))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> exists r . p2_ == path_concat p1_ r)
    (fun #through #to_ p s -> 
      let r = PathStep through to_ PathBase s in
      assert_norm (PathStep through to_ p s == path_concat p r)
    )
    (fun #to p -> FStar.Classical.exists_intro (fun r -> p == path_concat p r) PathBase)
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ ->
      FStar.Classical.exists_elim  (exists r . p3_ == path_concat p1_ r) #_ #(fun r12 -> p2_ == path_concat p1_ r12) () (fun r12 ->
	FStar.Classical.exists_elim (exists r . p3_ == path_concat p1_ r) #_ #(fun r23 -> p3_ == path_concat p2_ r23) () (fun r23 ->
	  path_concat_assoc p1_ r12 r23;
	  FStar.Classical.exists_intro (fun r -> p3_ == path_concat p1_ r) (path_concat r12 r23)
	)
      )
    )
    p q

let path_concat_includes
  (#from #through: typ)
  (p: path from through)
  (phi: (
    (#to: typ) ->
    (p': path from to) ->
    Ghost Type0
    (requires (path_includes p p'))
    (ensures (fun _ -> True))
  ))
  (f: (
    (to: typ) ->
    (p': path through to) ->
    Lemma
    (ensures (phi (path_concat p p')))
  ))
  (#to: typ)
  (q: path from to)
: Lemma
  (requires (path_includes p q))
  (ensures (path_includes p q /\ phi q))
= Classical.forall_intro_2 f;
  path_includes_exists_concat p q

let step_disjoint
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: GTot bool
= match s1 with
  | StepField _ fd1 ->
    let (StepField _ fd2) = s2 in
    fd1 <> fd2
  | StepCell _ _ i1 ->
    let (StepCell _ _ i2) = s2 in
    UInt32.v i1 <> UInt32.v i2
  | StepUField _ _ ->
    (* two fields of the same union are never disjoint *)
    false

let step_eq
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Tot (b: bool { b = true <==> to1 == to2 /\ s1 == s2 } )
= match s1 with
  | StepField l1 fd1 ->
    let (StepField _ fd2) = s2 in
    fd1 = fd2
  | StepCell _ _ i1 ->
    let (StepCell _ _ i2) = s2 in
    i1 = i2
  | StepUField l1 fd1 ->
    let (StepUField _ fd2) = s2 in
    fd1 = fd2

let step_disjoint_not_eq
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Lemma
  (requires (step_disjoint s1 s2 == true))
  (ensures (step_eq s1 s2 == false))
= () (* Note: the converse is now wrong, due to unions *)

let step_disjoint_sym
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2)
: Lemma
  (requires (step_disjoint s1 s2))
  (ensures (step_disjoint s2 s1))
= ()

noeq type path_disjoint_t (#from: typ):
  (#to1: typ) ->
  (#to2: typ) ->
  (p1: path from to1) ->
  (p2: path from to2) ->
  Type0
= | PathDisjointStep:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 } ) ->
    path_disjoint_t (PathStep through to1 p s1) (PathStep through to2 p s2)
  | PathDisjointIncludes:
    (#to1: typ) ->
    (#to2: typ) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (#to1': typ) ->
    (#to2': typ) ->
    (p1': path from to1' {path_includes p1 p1'}) ->
    (p2': path from to2' {path_includes p2 p2'}) ->
    path_disjoint_t p1 p2 ->
    path_disjoint_t p1' p2'

let rec path_disjoint_t_rect
  (#from: typ)
  (x:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (h: path_disjoint_t p1 p2) ->
    GTot Type))
  (h_step:
   ((#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 } ) ->
    (h: path_disjoint_t (PathStep through to1 p s1) (PathStep through to2 p s2)) ->
    GTot (x (PathStep through to1 p s1) (PathStep through to2 p s2) h)))
  (h_includes:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2'}) ->
    (h: path_disjoint_t p1 p2) ->
    (h': path_disjoint_t p1' p2') ->
    (ihx: x p1 p2 h) ->
    GTot (x p1' p2' h')))
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
  (h: path_disjoint_t p1 p2)
: Ghost (x p1 p2 h)
  (requires True)
  (ensures (fun _ -> True))
  (decreases h)
= match h with
  | PathDisjointStep p s1 s2 -> h_step p s1 s2 h
  | PathDisjointIncludes p1_ p2_ p1' p2' h_ -> h_includes p1_ p2_ p1' p2' h_ h (path_disjoint_t_rect x h_step h_includes p1_ p2_ h_)

let path_disjoint
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: GTot Type0
= squash (path_disjoint_t p1 p2)

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
let path_disjoint_ind
  (#from: typ)
  (x:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2 {path_disjoint p1 p2} ) ->
    GTot Type))
  (h_step:
   ((#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 /\ path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2) } ) ->
    Lemma (x (PathStep through to1 p s1) (PathStep through to2 p s2) )))
  (h_includes:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2' /\ path_disjoint p1 p2 /\ path_disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2')))
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2 { path_disjoint p1 p2 } )
: Lemma (x p1 p2)
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun (h: path_disjoint_t p1 p2) ->
   path_disjoint_t_rect
     (fun #v1 #v2 p1 p2 h -> let _ = FStar.Squash.return_squash h in squash (x p1 p2))
     (fun #through #to1 #to2 p s1 s2 h -> let _ = FStar.Squash.return_squash h in h_step p s1 s2)
     (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' h h' hx ->
       let _ = FStar.Squash.return_squash h in
       let _ = FStar.Squash.return_squash h' in
       let _ = FStar.Squash.return_squash hx in
       h_includes p1 p2 p1' p2')
     p1 p2 h)
#pop-options

let path_disjoint_step
  (#from: typ)
  (#through: typ)
  (#to1: typ)
  (#to2: typ)
  (p: path from through)
  (s1: step through to1)
  (s2: step through to2 { step_disjoint s1 s2 } )
: Lemma
  (requires True)
  (ensures (path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2)))
  [SMTPat (path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2))]
= FStar.Classical.give_witness (FStar.Squash.return_squash (PathDisjointStep p s1 s2))

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
let path_disjoint_includes
  (#from: typ)
  (#to1: typ)
  (#to2: typ)
  (p1: path from to1)
  (p2: path from to2)
  (#to1': typ)
  (#to2': typ)
  (p1': path from to1')
  (p2': path from to2')
: Lemma
  (requires (path_disjoint p1 p2 /\ path_includes p1 p1' /\ path_includes p2 p2'))
  (ensures (path_disjoint p1' p2'))
= let h : squash (path_disjoint_t p1 p2) = FStar.Squash.join_squash () in
  FStar.Squash.bind_squash h (fun h -> FStar.Squash.return_squash (PathDisjointIncludes p1 p2 p1' p2' h))
#pop-options

let path_disjoint_includes_l
  (#from: typ)
  (#to1: typ)
  (#to2: typ)
  (p1: path from to1)
  (p2: path from to2)
  (#to1': typ)
  (p1': path from to1')
: Lemma
  (requires (path_disjoint p1 p2 /\ path_includes p1 p1'))
  (ensures (path_disjoint p1' p2))
  [SMTPatOr [
    [SMTPat (path_disjoint p1 p2); SMTPat (path_includes p1 p1')];
    [SMTPat (path_disjoint p1' p2); SMTPat (path_includes p1 p1')];
  ]]
= path_disjoint_includes p1 p2 p1' p2

let path_disjoint_sym
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_disjoint p2 p1))
  [SMTPatOr [[SMTPat (path_disjoint p1 p2)]; [SMTPat (path_disjoint p2 p1)]]]
= path_disjoint_ind
  (fun #v1 #v2 p1 p2 -> path_disjoint p2 p1)
  (fun #through #to1 #to2 p s1 s2 -> path_disjoint_step p s2 s1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> path_disjoint_includes p2 p1 p2' p1')
  p1 p2

let rec path_equal
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Tot (b: bool { b == true <==> (value1 == value2 /\ p1 == p2) } )
  (decreases p1)
= match p1 with
  | PathBase -> PathBase? p2
  | PathStep _ _ p1' s1 ->
    PathStep? p2 && (
      let (PathStep _ _ p2' s2) = p2 in (
        path_equal p1' p2' &&
        step_eq s1 s2
    ))

let rec path_length_concat
  (#t0 #t1 #t2: typ)
  (p01: path t0 t1)
  (p12: path t1 t2)
: Lemma
  (requires True)
  (ensures (path_length (path_concat p01 p12) == path_length p01 + path_length p12))
  (decreases p12)
= match p12 with
  | PathBase -> ()
  | PathStep _ _ p' s' -> path_length_concat p01 p'

let rec path_concat_inj_l
  (#from #through1: typ)
  (p1_: path from through1)
  (#v1: typ)
  (p1: path through1 v1)
  (#through2 #v2: typ)
  (p2_: path from through2)
  (p2: path through2 v2)
: Lemma
  (requires (path_equal (path_concat p1_ p1) (path_concat p2_ p2) == true /\ path_length p1_ == path_length p2_))
  (ensures (path_equal p1_ p2_ == true /\ path_equal p1 p2 == true))
  (decreases p1)
= path_length_concat p1_ p1;
  path_length_concat p2_ p2;
  match p1 with
  | PathBase -> ()
  | PathStep _ _ p1' s1 ->
    let (PathStep _ _ p2' s2) = p2 in
    path_concat_inj_l p1_ p1' p2_ p2'

type path_disjoint_decomp_t
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Type
= | PathDisjointDecomp:
    (d_through: typ) ->
    (d_p: path from d_through) ->
    (d_v1: typ) ->
    (d_s1: step d_through d_v1) ->
    (d_p1': path d_v1 value1) ->
    (d_v2: typ) ->
    (d_s2: step d_through d_v2) ->
    (d_p2': path d_v2 value2) ->
    squash (
      step_disjoint d_s1 d_s2 == true /\
      p1 == path_concat (PathStep _ _ d_p d_s1) d_p1' /\
      p2 == path_concat (PathStep _ _ d_p d_s2) d_p2'
    ) ->
    path_disjoint_decomp_t p1 p2

let path_disjoint_decomp_includes
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
  (#value1': typ)
  (#value2': typ)
  (p1': path from value1')
  (p2': path from value2')
: Lemma
  (requires (
    path_includes p1 p1' /\
    path_includes p2 p2' /\ (
    exists (d : path_disjoint_decomp_t p1 p2) . True
  )))
  (ensures (exists (d: path_disjoint_decomp_t p1' p2') . True))
= let f
    (q1: path value1 value1' )
    (q2: path value2 value2' )
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma
    (requires (
      p1' == path_concat p1 q1 /\
      p2' == path_concat p2 q2
    ))
    (ensures (exists (d: path_disjoint_decomp_t p1' p2') . True))
  = let (PathDisjointDecomp _ p _ s1 p1_ _ s2 p2_ _) = d in
    path_concat_assoc (PathStep _ _ p s1) p1_ q1;
    path_concat_assoc (PathStep _ _ p s2) p2_ q2;
    let d' : path_disjoint_decomp_t p1' p2' =
      PathDisjointDecomp _ p _ s1 (path_concat p1_ q1) _ s2 (path_concat p2_ q2) ()
    in
    Classical.exists_intro (fun _ -> True) d'
  in
  let g
    (q1: path value1 value1' )
    (q2: path value2 value2' )
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma
    ((
      p1' == path_concat p1 q1 /\
      p2' == path_concat p2 q2
    ) ==> (
      exists (d: path_disjoint_decomp_t p1' p2') . True
    ))
  = Classical.move_requires (f q1 q2) d // FIXME: annoying to repeat those type annotations above. WHY WHY WHY can't I just use (fun q1 q2 d -> Classical.move_requires (f q1 q2) d) as an argument of Classical.forall_intro_3 below instead of this g???
  in
  path_includes_exists_concat p1 p1' ;
  path_includes_exists_concat p2 p2' ;
  let _ : squash (exists (d: path_disjoint_decomp_t p1' p2') . True) =
    Classical.forall_intro_3 g
  in
  ()

let path_disjoint_decomp
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (exists (d: path_disjoint_decomp_t p1 p2) . True))
= path_disjoint_ind
  (fun #v1 #v2 p1 p2 -> exists (d: path_disjoint_decomp_t #from #v1 #v2 p1 p2) . True)
  (fun #through #to1 #to2 p s1 s2 ->
    let d : path_disjoint_decomp_t (PathStep _ _ p s1) (PathStep _ _ p s2) =
      PathDisjointDecomp _ p _ s1 PathBase _ s2 PathBase ()
    in
    Classical.exists_intro (fun _ -> True) d
  )
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> path_disjoint_decomp_includes p1 p2 p1' p2')
  p1 p2

let path_disjoint_not_path_equal
  (#from: typ)
  (#value1: typ)
  (#value2: typ)
  (p1: path from value1)
  (p2: path from value2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_equal p1 p2 == false))
= let f
    (d: path_disjoint_decomp_t p1 p2)
  : Lemma (path_equal p1 p2 == false)
  = if path_equal p1 p2
    then
      let (PathDisjointDecomp _ p _ s1 p1_ _ s2 p2_ _) = d in
      path_concat_inj_l (PathStep _ _ p s1) p1_ (PathStep _ _ p s2) p2_
    else ()
  in
  path_disjoint_decomp p1 p2;
  Classical.forall_intro f

let rec path_destruct_l
  (#t0 #t2: typ)
  (p: path t0 t2)
: Tot (
    x: option (t1: typ & (s: step t0 t1 & (p' : path t1 t2 { p == path_concat (PathStep _ _ PathBase s) p' /\ path_length p' < path_length p } ) ) )
    { None? x <==> PathBase? p }
  )
  (decreases p)
= match p with
  | PathBase -> None
  | PathStep _ _ p' s ->
    begin match path_destruct_l p' with
    | None -> Some (| _, (| s,  PathBase |) |)
    | Some (| t_, (| s_, p_ |) |) ->
      Some (| t_, (| s_, PathStep _ _ p_ s |) |)
    end

let rec path_equal'
  (#from #to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2)
: Tot (b: bool { b == true <==> to1 == to2 /\ p1 == p2 } )
  (decreases (path_length p1))
= match path_destruct_l p1 with
  | None -> PathBase? p2
  | Some (| t1, (| s1, p1' |) |) ->
    begin match path_destruct_l p2 with
    | None -> false
    | (Some (| t2, (| s2, p2' |) |) ) ->
      step_eq s1 s2 &&
      path_equal' p1' p2'
    end

let path_includes_concat_l
  (#from #through #to1 #to2: typ)
  (p0: path from through)
  (p1: path through to1)
  (p2: path through to2)
: Lemma
  (requires (path_includes p1 p2))
  (ensures (path_includes (path_concat p0 p1) (path_concat p0 p2)))
= path_includes_ind
    (fun #to1_ #to2_ p1_ p2_ -> path_includes (path_concat p0 p1_) (path_concat p0 p2_))
    (fun #through #to p st -> ())
    (fun #to p -> path_includes_refl (path_concat p0 p))
    (fun #to1_ #to2_ #to3_ p1_ p2_ p3_ -> path_includes_trans (path_concat p0 p1_) (path_concat p0 p2_) (path_concat p0 p3_))
    p1 p2

let path_disjoint_concat
  (#from #through #to1 #to2: typ)
  (p0: path from through)
  (p1: path through to1)
  (p2: path through to2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_disjoint (path_concat p0 p1) (path_concat p0 p2)))
= path_disjoint_ind
    (fun #v1 #v2 p1 p2 -> path_disjoint (path_concat p0 p1) (path_concat p0 p2))
    (fun #through #to1 #to2 p s1 s2 -> path_disjoint_step (path_concat p0 p) s1 s2)
    (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' ->
      path_includes_concat_l p0 p1 p1';
      path_includes_concat_l p0 p2 p2';
      path_disjoint_includes (path_concat p0 p1) (path_concat p0 p2) (path_concat p0 p1') (path_concat p0 p2'))
  p1 p2

(* TODO: the following is now wrong due to unions, but should still hold if we restrict ourselves to readable paths
let rec not_path_equal_path_disjoint_same_type
  (#from: typ)
  (#value: typ)
  (p1: path from value)
  (p2: path from value)
: Lemma
  (requires (path_equal p1 p2 == false))
  (ensures (path_disjoint p1 p2))
  (decreases (path_length p1))
= assert (path_equal p1 p2 == path_equal' p1 p2);
  match path_destruct_l p1 with
  | None -> path_typ_depth p2
  | Some (| t1, (| s1, p1' |) |) ->
    begin match path_destruct_l p2 with
    | None -> path_typ_depth p1
    | Some (| t2, (| s2, p2' |) |) ->
      if step_eq s1 s2
      then begin
	not_path_equal_path_disjoint_same_type p1' p2' ;
	path_disjoint_concat (PathStep _ _ PathBase s1) p1' p2'
      end else begin
        path_disjoint_step PathBase s1 s2;
	path_includes_concat (PathStep _ _ PathBase s1) p1';
	path_includes_concat (PathStep _ _ PathBase s2) p2';
	path_disjoint_includes (PathStep _ _ PathBase s1) (PathStep _ _ PathBase s2) p1 p2
      end
    end
*)

let step_sel_upd_other
  (#from: typ)
  (#to1 #to2: typ)
  (s1: step from to1)
  (s2: step from to2 {step_disjoint s1 s2})
  (m: otype_of_typ from)
  (v: otype_of_typ to1)
: Lemma
  (step_sel (step_upd m s1 v) s2 == step_sel m s2)
= match s1 with
  | StepField l1 fd1 ->
    let (m: ostruct l1) = m in
    let (StepField _ fd2) = s2 in
    begin match m with
    | None -> ()
    | Some m -> DM.sel_upd_other m fd1 v fd2
    end
  | StepCell length1 _ i1 ->
    let (m: option (array length1 (otype_of_typ to1))) = m in
    let (StepCell _ _ i2) = s2 in
    begin match m with
    | None -> ()
    | Some m ->
      Seq.lemma_index_upd2 m (UInt32.v i1) v (UInt32.v i2)
    end

let path_sel_upd_other
  (#from: typ)
  (#to1 #to2: typ)
  (p1: path from to1)
  (p2: path from to2 {path_disjoint p1 p2})
: Lemma
  (ensures (forall (m: otype_of_typ from) (v: otype_of_typ to1) . path_sel (path_upd m p1 v) p2 == path_sel m p2))
= path_disjoint_ind
  (fun #v1 #v2 p1_ p2_ -> forall (m: otype_of_typ from) (v: otype_of_typ v1) . path_sel (path_upd m p1_ v) p2_ == path_sel m p2_)
  (fun #through #to1_ #to2_ p s1 s2 ->
      FStar.Classical.forall_intro_sub #_ #(fun m -> forall  (v: otype_of_typ to1_) . path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun m ->
	  FStar.Classical.forall_intro_sub #_ #(fun v -> path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun v ->
	  let m0 = path_sel m p in
          let m1 = step_sel m0 s1 in
          let m2 = step_sel m0 s2 in
          let m0' = step_upd m0 s1 v in
          path_sel_upd_same m p m0';
          step_sel_upd_other s1 s2 m0 v
      )))
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' ->
    let h1: squash (exists r1 . p1' == path_concat p1 r1) = path_includes_exists_concat p1 p1' in
    let h2: squash (exists r2 . p2' == path_concat p2 r2) = path_includes_exists_concat p2 p2' in
    FStar.Classical.forall_intro_sub #_ #(fun (m: otype_of_typ from) -> forall v . path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (m: otype_of_typ from) ->
      FStar.Classical.forall_intro_sub #_ #(fun (v: otype_of_typ v1') -> path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (v: otype_of_typ v1') ->
      FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h1 (fun r1 ->
	FStar.Classical.exists_elim (path_sel (path_upd m p1' v) p2' == path_sel m p2') h2 (fun r2 ->
	  path_upd_concat m p1 r1 v;
	  path_sel_concat m p2 r2
	  )))))
  p1 p2

let path_sel_upd_other'
  (#from: typ)
  (#to1: typ)
  (p1: path from to1)
  (m: otype_of_typ from)
  (v: otype_of_typ to1)
  (#to2: typ)
  (p2: path from to2)
: Lemma
  (requires (path_disjoint p1 p2))
  (ensures (path_sel (path_upd m p1 v) p2 == path_sel m p2))
= path_sel_upd_other p1 p2

(** Operations on pointers *)

let equal
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> t1 == t2 /\ p1 == p2 ))
= Pointer?.from p1 = Pointer?.from p2 &&
  HS.aref_equal (Pointer?.contents p1) (Pointer?.contents p2) &&
  path_equal (Pointer?.p p1) (Pointer?.p p2)

let as_addr (#t: typ) (p: pointer t) =
  HS.aref_as_addr (Pointer?.contents p)

let _field
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
: Tot (pointer (typ_of_struct_field l fd))
= let (Pointer from contents p') = p in
  let p' : path from (TStruct l) = p' in
  let p'' : path from (typ_of_struct_field l fd) = PathStep _ _ p' (StepField _ fd) in
  Pointer from contents p''

let _cell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  (i: UInt32.t {UInt32.v i < UInt32.v length})
: Tot (pointer value)
= let (Pointer from contents p') = p in
  let p' : path from (TArray length value) = p' in
  let p'' : path from value = PathStep _ _ p' (StepCell _ _ i) in
  Pointer from contents p''

let _ufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: Tot (pointer (typ_of_struct_field l fd))
= let (Pointer from contents p') = p in
  let p' : path from (TUnion l) = p' in
  let p'' : path from (typ_of_struct_field l fd) = PathStep _ _ p' (StepUField _ fd) in
  Pointer from contents p''

let unused_in
  (#value: typ)
  (p: pointer value)
  (h: HS.mem)
: GTot Type0
= let (Pointer from contents p') = p in
  HS.aref_unused_in contents h

let pointer_ref_contents : Type0 = (t: typ & otype_of_typ t)

let live
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot Type0
= let rel = Heap.trivial_preorder pointer_ref_contents in
  let (Pointer from contents _) = p in (
    HS.aref_live_at h contents pointer_ref_contents rel /\ (
      let untyped_contents = HS.greference_of contents pointer_ref_contents rel in (
      dfst (HS.sel h untyped_contents) == from
  )))

let nlive
  (#value: typ)
  (h: HS.mem)
  (p: npointer value)
: GTot Type0
= if g_is_null p
  then True
  else live h p

let live_nlive
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
= ()

let g_is_null_nlive
  (#t: typ)
  (h: HS.mem)
  (p: npointer t)
= ()

let greference_of
  (#value: typ)
  (p: pointer value)
: Ghost (HS.reference pointer_ref_contents)
  (requires (exists h . live h p))
  (ensures (fun x -> (exists h . live h p) /\ x == HS.greference_of (Pointer?.contents p) pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) /\ HS.aref_of x == Pointer?.contents p))
= HS.greference_of (Pointer?.contents p) pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents)

let unused_in_greference_of
  (#value: typ)
  (p: pointer value)
  (h: HS.mem)
: Lemma
  (requires (exists h . live h p))
  (ensures ((exists h . live h p) /\ (HS.unused_in (greference_of p) h <==> unused_in p h)))
  [SMTPatOr [
    [SMTPat (HS.unused_in (greference_of p) h)];
    [SMTPat (unused_in p h)];
  ]]
= ()

let live_not_unused_in
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
= let f () : Lemma
    (requires (live h p /\ p `unused_in` h))
    (ensures False)
  = let r = greference_of p in
    HS.contains_aref_unused_in h r (Pointer?.contents p)
  in
  Classical.move_requires f ()

let gread
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: GTot (type_of_typ value)
= if StrongExcludedMiddle.strong_excluded_middle (live h p)
  then
    let content = greference_of p in
    let (| _, c |) = HS.sel h content in
    value_of_ovalue value (path_sel c (Pointer?.p p))
  else
    dummy_val value

let frameOf
  (#value: typ)
  (p: pointer value)
: GTot HS.rid
= HS.frameOf_aref (Pointer?.contents p)

let live_region_frameOf #value h p =
  let content = greference_of p in
  assert (HS.contains h content)

let disjoint_roots_intro_pointer_vs_pointer
  (#value1 value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 =!= as_addr p2))
= ()

let disjoint_roots_intro_pointer_vs_reference
  (#value1: typ)
  (#value2: Type)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: HS.reference value2)
: Lemma
  (requires (live h p1 /\ p2 `HS.unused_in` h))
  (ensures (frameOf p1 <> HS.frameOf p2 \/ as_addr p1 =!= HS.as_addr p2))
= let r = greference_of p1 in
  assert (HS.contains h r)

let disjoint_roots_intro_reference_vs_pointer
  (#value1: Type)
  (#value2: typ)
  (h: HS.mem)
  (p1: HS.reference value1)
  (p2: pointer value2)
: Lemma
  (requires (HS.contains h p1 /\ p2 `unused_in` h))
  (ensures (HS.frameOf p1 <> frameOf p2 \/ HS.as_addr p1 =!= as_addr p2))
= ()

let is_mm
  (#value: typ)
  (p: pointer value)
: GTot bool
= HS.aref_is_mm (Pointer?.contents p)

(* // TODO: recover with addresses?
let recall
  (#value: Type)
  (p: pointer value {is_eternal_region (frameOf p) && not (is_mm p)})
: HST.Stack unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ live m1 p))
= HST.recall (Pointer?.content p)
*)

let gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= _field p fd

let as_addr_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let unused_in_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
  (h: HS.mem)
= ()

let live_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let gread_gfield
  (h: HS.mem)
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let frameOf_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let is_mm_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= _ufield p fd

let as_addr_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let unused_in_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
  (h: HS.mem)
= ()

let live_gufield
  (h: HS.mem)
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let gread_gufield
  (h: HS.mem)
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let frameOf_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let is_mm_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  i
= _cell p i

let as_addr_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  i
= ()

let unused_in_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  i
= ()

let live_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  i
= ()

let gread_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  i
= ()

let frameOf_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  i
= ()

let is_mm_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  i
= ()

let includes
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: GTot bool
= Pointer?.from p1 = Pointer?.from p2 &&
  HS.aref_equal (Pointer?.contents p1) (Pointer?.contents p2) &&
  path_includes (Pointer?.p p1) (Pointer?.p p2)

let includes_refl
  (#value: typ)
  (p: pointer value)
= ()

let includes_trans
  (#value1 #value2 #value3: typ)
  (p1: pointer value1)
  (p2: pointer value2)
  (p3: pointer value3)
= path_includes_trans (Pointer?.p p1) (Pointer?.p p2) (Pointer?.p p3)

let includes_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let includes_gufield
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let includes_gcell
  (#length: array_length_t)
  (#value: typ)
  (p: pointer (TArray length value))
  i
= ()

let includes_ind
  (x:((#value1: typ) ->
      (#value2: typ) ->
      (p1: pointer value1) ->
      (p2: pointer value2 {includes p1 p2} ) ->
      GTot Type0))
  (h_field:
   ((l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd: struct_field l {includes p (gfield p fd)}) ->
    Lemma (x p (gfield p fd))))
  (h_ufield:
   ((l: union_typ) ->
    (p: pointer (TUnion l)) ->
    (fd: struct_field l {includes p (gufield p fd)}) ->
    Lemma (x p (gufield p fd))))
  (h_cell:
   ((#length: array_length_t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i: UInt32.t {UInt32.v i < UInt32.v length /\ includes p (gcell p i)}) ->
    Lemma (x p (gcell p i))))
  (h_refl:
   ((#value: typ) ->
    (p: pointer value {includes p p}) ->
    Lemma (x p p)))
  (h_trans:
   ((#value1: typ) ->
    (#value2: typ) ->
    (#value3: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (p3: pointer value3 {includes p1 p2 /\ includes p2 p3 /\ includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3)))
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2 {includes p1 p2})
: Lemma (x p1 p2)
= let (Pointer from contents _) = p1 in
  path_includes_ind
    (fun #to1 #to2 p1_ p2_ -> x (Pointer from contents p1_) (Pointer from contents p2_))
    (fun #through #to p s ->
      match s with
      | StepField l fd -> let (pt: pointer (TStruct l)) = (Pointer from contents p) in h_field l pt fd
      | StepUField l fd -> let (pt: pointer (TUnion l)) = (Pointer from contents p) in h_ufield l pt fd
      | StepCell length value i -> let (pt: pointer (TArray length value)) = (Pointer from contents p) in h_cell pt i
    )
    (fun #to p -> h_refl (Pointer from contents p))
    (fun #to1 #to2 #to3 p1_ p2_ p3_ -> h_trans (Pointer from contents p1_) (Pointer from contents p2_) (Pointer from contents p3_))
    (Pointer?.p p1)
    (Pointer?.p p2)

(*
let unused_in_includes
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (includes p1 p2))
  (unused_in p1 h <==> unused_in p2 h)
  [SMTPat (unused_in p2 h); SMTPat (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> unused_in p1 h <==> unused_in p2 h)
  (fun l p fd -> unused_in_gfield p fd h)
  (fun l p fd -> unused_in_gufield p fd h)
  (fun #length #value p i -> unused_in_gcell h p i)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2

let live_includes
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (includes p1 p2))
  (ensures (live h p1 <==> live h p2))
  [SMTPat (live h p2); SMTPat (includes p1 p2)]
= includes_ind
  (fun #v1 #v2 p1 p2 -> live h p1 <==> live h p2)
  (fun l p fd -> live_gfield h p fd)
  (fun l p fd -> live_gufield h p fd)
  (fun #length #value p i -> live_gcell h p i)
  (fun #v p -> ())
  (fun #v1 #v2 #v3 p1 p2 p3 -> ())
  p1 p2
*)

(** The readable permission.
    We choose to implement it only abstractly, instead of explicitly
    tracking the permission in the heap.
*)

let readable
  (#a: typ)
  (h: HS.mem)
  (b: pointer a)
: GTot Type0
= let () = () in // necessary to somehow remove the `logic` qualifier
  live h b /\ (
    let content = greference_of b in
    let (| _, c |) = HS.sel h content in
    ovalue_is_readable a (path_sel c (Pointer?.p b))
  )

let readable_live
  (#a: typ)
  (h: HS.mem)
  (b: pointer a)
= ()

let readable_gfield
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (fd: struct_field l)
= ()

let readable_struct
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
= let dummy_field : struct_field l = fst (List.Tot.hd l.fields) in // struct is nonempty
  let dummy_field_ptr = gfield p dummy_field in
  assert (readable h dummy_field_ptr);
  let content = greference_of p in
  let (| _, c |) = HS.sel h content in
  let (v: otype_of_typ (TStruct l)) = path_sel c (Pointer?.p p) in
  let (v: ostruct l {Some? v}) = v in
  ovalue_is_readable_struct_intro l v

let readable_struct_forall_mem
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
= let f
    (h: HS.mem)
  : Lemma // FIXME: WHY WHY WHY do we need this explicit annotation?
    (requires (
      forall (f: struct_field l) .
      readable h (gfield p f)
    ))
    (ensures (readable h p))
  = readable_struct h p
  in
  Classical.forall_intro (Classical.move_requires f)

let rec readable_struct_fields'
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (s: list string)
: GTot Type0
  (decreases s)
= match s with
  | [] -> True
  | f :: s' ->
    readable_struct_fields' h p s' /\ (
      if List.Tot.mem f (List.Tot.map fst l.fields)
      then
	let f : struct_field l = f in
	readable h (gfield p f)
      else
	True
    )

let readable_struct_fields #l h p s = readable_struct_fields' h p s

let readable_struct_fields_nil #l h p = ()

let readable_struct_fields_cons #l h p f q = ()

let rec readable_struct_fields_elim
  (#l: struct_typ)
  (h: HS.mem)
  (p: pointer (TStruct l))
  (s: list string)
: Lemma
  (requires (readable_struct_fields h p s))
  (ensures (forall f . (List.Tot.mem f s /\ List.Tot.mem f (List.Tot.map fst l.fields)) ==> (let f : struct_field l = f in readable h (gfield p f))))
  (decreases s)
= match s with
  | [] -> ()
  | _ :: q -> readable_struct_fields_elim h p q

let readable_struct_fields_readable_struct #l h p =
  readable_struct_fields_elim h p (List.Tot.map fst l.fields);
  readable_struct h p

let readable_gcell
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
  i
= ()

let readable_array
  (#length: array_length_t)
  (#value: typ)
  (h: HS.mem)
  (p: pointer (TArray length value))
= assert (readable h (gcell p 0ul)); // for Some?
  let content = greference_of p in
  let (| _, c |) = HS.sel h content in
  let (v0: otype_of_typ (TArray length value)) = path_sel c (Pointer?.p p) in
  ovalue_is_readable_array_intro v0

(* TODO: improve on the following interface *)
let readable_gufield
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

(** The active field of a union *)

let is_active_union_field
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
: GTot Type0
= let () = () in // necessary to somehow remove the `logic` qualifier
  live h p /\ (
    let content = greference_of p in
    let (| _, c |) = HS.sel h content in
    let vu : otype_of_typ (TUnion l) = path_sel c (Pointer?.p p) in
    let vu : option (gtdata (struct_field l) (type_of_struct_field' l otype_of_typ)) = vu in
    Some? vu /\ gtdata_get_key (Some?.v vu) == fd
  )

let is_active_union_live
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let is_active_union_field_live
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let is_active_union_field_eq
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd1 fd2: struct_field l)
= ()

let is_active_union_field_get_key
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let is_active_union_field_readable
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= ()

let is_active_union_field_includes_readable
  (#l: union_typ)
  (h: HS.mem)
  (p: pointer (TUnion l))
  (fd: struct_field l)
  (#t': typ)
  (p' : pointer t')
= let content = greference_of p in
  let (| _ , c |) = HS.sel h content in
  let t = typ_of_struct_field l fd in
  let (Pointer from cts p0) = p in
  let pf = PathStep _ _ p0 (StepUField l fd) in
  let (v0 : otype_of_typ t) = path_sel c pf in
  let phi
    (#t': typ)
    (pt': path from t')
  : Ghost Type0
    (requires (path_includes pf pt'))
    (ensures (fun _ -> True))
  = (~ (path_sel c pt' == none_ovalue t')) ==> is_active_union_field h p fd
  in
  let f
    (t' : typ)
    (pt' : path t t')
  : Lemma
    (ensures (phi (path_concat pf pt')))
  = path_sel_concat c pf pt';
    path_sel_none_ovalue pf;
    path_sel_none_ovalue pt'
  in
  path_concat_includes pf phi f (Pointer?.p p')

(*** Semantics of buffers *)

(** Operations on buffers *)

#push-options "--ifuel 2"
let _singleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Tot (buffer t)
= let Pointer from contents pth = p in
  match pth with
  | PathStep _ _ pth' (StepCell ln ty i) ->
    (* reconstruct the buffer to the enclosing array *)
    Buffer (BufferRootArray #ty #ln (Pointer from contents pth')) i 1ul 
  | _ ->
    Buffer (BufferRootSingleton p) 0ul 1ul
#pop-options

let gsingleton_buffer_of_pointer #t p = _singleton_buffer_of_pointer p

let singleton_buffer_of_pointer #t p = _singleton_buffer_of_pointer p

let gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: GTot (buffer t)
= Buffer (BufferRootArray p) 0ul length

let buffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
: HST.Stack (buffer t)
  (requires (fun h -> live h p))
  (ensures (fun h b h' -> h' == h /\ b == gbuffer_of_array_pointer p))
= Buffer (BufferRootArray p) 0ul length

let buffer_length
  (#t: typ)
  (b: buffer t)
: GTot UInt32.t
= Buffer?.blength b

let buffer_length_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires True)
  (ensures (buffer_length (gsingleton_buffer_of_pointer p) == 1ul))
  [SMTPat (buffer_length (gsingleton_buffer_of_pointer p))]
= ()

let buffer_length_gbuffer_of_array_pointer
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires True)
  (ensures (buffer_length (gbuffer_of_array_pointer p) == len))
  [SMTPat (buffer_length (gbuffer_of_array_pointer p))]
= ()

let buffer_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= let () = () in ( // necessary to somehow remove the `logic` qualifier
    match b.broot with
    | BufferRootSingleton p -> live h p
    | BufferRootArray p -> live h p
  )

let buffer_live_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  (h: HS.mem)
: Lemma
  (ensures (buffer_live h (gsingleton_buffer_of_pointer p) <==> live h p ))
  [SMTPat (buffer_live h (gsingleton_buffer_of_pointer p))]
= ()

let buffer_live_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
  (h: HS.mem)
: Lemma
  (requires True)
  (ensures (buffer_live h (gbuffer_of_array_pointer p) <==> live h p))
  [SMTPat (buffer_live h (gbuffer_of_array_pointer p))]
= ()

let buffer_unused_in #t b h =
  match b.broot with
  | BufferRootSingleton p -> unused_in p h
  | BufferRootArray p -> unused_in p h

let buffer_live_not_unused_in #t b h = ()

let buffer_unused_in_gsingleton_buffer_of_pointer #t p h = ()

let buffer_unused_in_gbuffer_of_array_pointer #t #length p h = ()

let frameOf_buffer
  (#t: typ)
  (b: buffer t)
: GTot HS.rid
= match b.broot with
  | BufferRootSingleton p -> frameOf p
  | BufferRootArray p -> frameOf p

let frameOf_buffer_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
= ()

let frameOf_buffer_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
= ()

let live_region_frameOf_buffer #value h p = ()

let buffer_as_addr #t b =
  match b.broot with
  | BufferRootSingleton p -> as_addr p
  | BufferRootArray p -> as_addr p

let buffer_as_addr_gsingleton_buffer_of_pointer #t p = ()

let buffer_as_addr_gbuffer_of_array_pointer #t #length p = ()

let gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  len
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

let frameOf_buffer_gsub_buffer #t b i len = ()

let buffer_as_addr_gsub_buffer #t b i len = ()

let sub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  len
= Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) len

let offset_buffer #t b i =
  sub_buffer b i (UInt32.sub (Buffer?.blength b) i)

let buffer_length_gsub_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  len
= ()

let buffer_live_gsub_buffer_equiv
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  len
  h
= ()

let buffer_live_gsub_buffer_intro
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  len
  h
= ()

let buffer_unused_in_gsub_buffer #t b i len h = ()

let gsub_buffer_gsub_buffer
  (#a: typ)
  (b: buffer a)
  (i1: UInt32.t)
  len1 i2 len2
= ()

let gsub_buffer_zero_buffer_length
  (#a: typ)
  (b: buffer a)
= ()

let buffer_root_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer_root t)
: GTot (Seq.seq (type_of_typ t))
= match b with
  | BufferRootSingleton p ->
    Seq.create 1 (gread h p)
  | BufferRootArray p ->
    gread h p

let length_buffer_root_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer_root t)
: Lemma
  (requires True)
  (ensures (Seq.length (buffer_root_as_seq h b) == UInt32.v (buffer_root_length b)))
  [SMTPat (Seq.length (buffer_root_as_seq h b))]
= ()

let buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot (Seq.seq (type_of_typ t))
= let i = UInt32.v (Buffer?.bidx b) in
  Seq.slice (buffer_root_as_seq h (Buffer?.broot b)) i (i + UInt32.v (Buffer?.blength b))

let buffer_length_buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
= ()

#push-options "--ifuel 2 --z3rlimit_factor 4 --retry 4"
let buffer_as_seq_gsingleton_buffer_of_pointer #t h p =
  let Pointer from contents pth = p in
  match pth with
  | PathStep through to pth' (StepCell ln ty i) ->
    assert (through == TArray ln ty);
    assert (to == ty);
    assert (t == ty);
    let p' : pointer (TArray ln ty) = Pointer from contents pth' in
    let s : array ln (type_of_typ t) = gread h p' in
    let s1 = Seq.slice s (UInt32.v i) (UInt32.v i + 1) in
    let v = gread h p in
    assert (v == Seq.index s (UInt32.v i));
    let s2 = Seq.create 1 v in
    assert (Seq.length s1 == 1);
    assert (Seq.length s2 == 1);
    assert (Seq.index s1 0 == v);
    assert (Seq.index s2 0 == v);
    assert (Seq.equal s1 s2)
  | _ ->
    Seq.slice_length (Seq.create 1 (gread h p))
#pop-options

let buffer_as_seq_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray length t))
= let s : array length (type_of_typ t) = gread h p in
  Seq.slice_length s

let buffer_as_seq_gsub_buffer
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  len
= Seq.slice_slice (buffer_root_as_seq h (Buffer?.broot b)) (UInt32.v (Buffer?.bidx b)) (UInt32.v (Buffer?.bidx b) + UInt32.v (Buffer?.blength b)) (UInt32.v i) (UInt32.v i + UInt32.v len)

let gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  i
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    gcell p FStar.UInt32.(Buffer?.bidx b +^ i)

let pointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  i
= match Buffer?.broot b with
  | BufferRootSingleton p -> p
  | BufferRootArray p ->
    _cell p FStar.UInt32.(Buffer?.bidx b +^ i)

let gpointer_of_buffer_cell_gsub_buffer
  (#t: typ)
  (b: buffer t)
  i1 len i2
= ()

let live_gpointer_of_buffer_cell
  (#t: typ)
  (b: buffer t)
  i h
= ()

#set-options "--initial_ifuel 2 --max_ifuel 2"
let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  i
= ()

#set-options "--initial_ifuel 1 --max_ifuel 1"
let gpointer_of_buffer_cell_gbuffer_of_array_pointer
  (#length: array_length_t)
  (#t: typ)
  (p: pointer (TArray length t))
  i
= ()

let frameOf_gpointer_of_buffer_cell #t b i = ()

let as_addr_gpointer_of_buffer_cell #t b i = ()

let gread_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  i
= ()

let gread_gpointer_of_buffer_cell'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  i
= ()

let index_buffer_as_seq
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  i
= ()

let gsingleton_buffer_of_pointer_gcell #t #len p i = ()

let gsingleton_buffer_of_pointer_gpointer_of_buffer_cell #t b i = ()

(* The readable permission lifted to buffers. *)

let buffer_readable'
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= buffer_live h b /\ (
    forall (i: UInt32.t) .
    UInt32.v i < UInt32.v (buffer_length b) ==>
    readable h (gpointer_of_buffer_cell b i)
  )

let buffer_readable
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: GTot Type0
= buffer_readable' h b

let buffer_readable_buffer_live
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
= ()

let buffer_readable_gsingleton_buffer_of_pointer
  (#t: typ)
  (h: HS.mem)
  (p: pointer t)
= let phi () : Lemma
      (requires (buffer_readable h (gsingleton_buffer_of_pointer p)))
      (ensures (readable h p))
  = assert (readable h (gpointer_of_buffer_cell (gsingleton_buffer_of_pointer p) 0ul))
  in
  Classical.move_requires phi ()

let buffer_readable_gbuffer_of_array_pointer
  (#len: array_length_t)
  (#t: typ)
  (h: HS.mem)
  (p: pointer (TArray len t))
= let phi ()
  : Lemma
    (requires (buffer_readable h (gbuffer_of_array_pointer p)))
    (ensures (readable h p))
  = let psi
      (i: UInt32.t { UInt32.v i < UInt32.v len } )
    : Lemma
      (readable h (gcell p i))
    = assert (readable h (gpointer_of_buffer_cell (gbuffer_of_array_pointer p) i))
    in
    Classical.forall_intro psi;
    readable_array h p
  in
  Classical.move_requires phi ()

let buffer_readable_gsub_buffer
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  len
= Classical.forall_intro (Classical.move_requires (gpointer_of_buffer_cell_gsub_buffer b i len))

let readable_gpointer_of_buffer_cell
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  i
= ()

let buffer_readable_intro
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
= ()

let buffer_readable_elim #t h b = ()

(*** Disjointness of pointers *)

let disjoint
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: GTot Type0
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    Pointer?.from p1 == Pointer?.from p2 /\
    Pointer?.contents p1 == Pointer?.contents p2 /\
    path_disjoint (Pointer?.p p1) (Pointer?.p p2)
  else
    True

let disjoint_root
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))
  (ensures (disjoint p1 p2))
= ()

let disjoint_gfield
  (#l: struct_typ)
  (p: pointer (TStruct l))
  (fd1 fd2: struct_field l)
: Lemma
  (requires (fd1 <> fd2))
  (ensures (disjoint (gfield p fd1) (gfield p fd2)))
  [SMTPat (disjoint (gfield p fd1) (gfield p fd2))]
= ()

let disjoint_gcell
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
    disjoint (gcell p i1) (gcell p i2)
  ))
  [SMTPat (disjoint (gcell p i1) (gcell p i2))]
= ()

let disjoint_includes
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
  (#value1': typ)
  (#value2': typ)
  (p1': pointer value1')
  (p2': pointer value2')
: Lemma
  (requires (includes p1 p1' /\ includes p2 p2' /\ disjoint p1 p2))
  (ensures (disjoint p1' p2'))
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    path_disjoint_includes (Pointer?.p p1) (Pointer?.p p2) (Pointer?.p p1') (Pointer?.p p2')
  else
    ()

let disjoint_ind
  (x:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 {disjoint p1 p2} ) ->
    GTot Type0))
  (h_root:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 { frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2 } ) ->
    Lemma (x p1 p2)))
  (h_field:
   ((#l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd1: struct_field l) ->
    (fd2: struct_field l { fd1 <> fd2 /\ disjoint (gfield p fd1) (gfield p fd2) } ) ->
    Lemma (x (gfield p fd1) (gfield p fd2))))
  (h_cell:
   ((#length: array_length_t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i1: UInt32.t {UInt32.v i1 < UInt32.v length}) ->
    (i2: UInt32.t {UInt32.v i2 < UInt32.v length /\ UInt32.v i1 <> UInt32.v i2 /\ disjoint (gcell p i1) (gcell p i2) }) ->
    Lemma (x (gcell p i1) (gcell p i2))
  ))
  (h_includes:
   ((#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': pointer value1' {includes p1 p1'}) ->
    (p2': pointer value2' {includes p2 p2' /\ disjoint p1 p2 /\ disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2')))
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2 { disjoint p1 p2 } )
: Lemma (x p1 p2)
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then
    let (Pointer from contents _) = p1 in
    path_disjoint_ind
      (fun #v1 #v2 p1_ p2_ -> x (Pointer from contents p1_) (Pointer from contents p2_))
      (fun #through #to1 #to2 p s1 s2 ->
         match s1 with
         | StepField l fd1 ->
           let (StepField _ fd2) = s2 in
           h_field #l (Pointer from contents p) fd1 fd2
         | StepCell le va i1 ->
           let (StepCell _ _ i2) = s2 in
           h_cell #le #va (Pointer from contents p) i1 i2
      )
      (fun #v1 #v2 p1_ p2_ #v1' #v2' p1' p2' -> h_includes (Pointer from contents p1_) (Pointer from contents p2_) (Pointer from contents p1') (Pointer from contents p2'))
      (Pointer?.p p1)
      (Pointer?.p p2);
      assert (x p1 p2)
  else
    h_root p1 p2

let disjoint_sym
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (disjoint p1 p2))
  (ensures (disjoint p2 p1))
= disjoint_ind
  (fun #v1 #v2 p1 p2 -> disjoint p2 p1)
  (fun #v1 #v2 p1 p2 -> disjoint_root p2 p1)
  (fun #l p fd1 fd2 -> disjoint_gfield p fd2 fd1)
  (fun #le #va p i1 i2 -> disjoint_gcell p i2 i1)
  (fun #v1 #v2 p1 p2 #v1' #v2' p1' p2' -> disjoint_includes p2 p1 p2' p1')
  p1 p2

let disjoint_sym'
  (#value1: typ)
  (#value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires True)
  (ensures (disjoint p1 p2 <==> disjoint p2 p1))
  [SMTPat (disjoint p1 p2)]
= FStar.Classical.move_requires (disjoint_sym #value1 #value2 p1) p2;
  FStar.Classical.move_requires (disjoint_sym #value2 #value1 p2) p1

let disjoint_sym''
  (value1: typ)
  (value2: typ)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (ensures (disjoint p1 p2 <==> disjoint p2 p1))
= disjoint_sym' p1 p2

let disjoint_includes_l #a #es #a' (x: pointer a) (subx:pointer es) (y:pointer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPat (disjoint subx y); SMTPat (includes x subx)]
  = disjoint_includes x y subx y

let disjoint_includes_l_swap #a #es #a' (x:pointer a) (subx:pointer es) (y:pointer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint y subx))
  [SMTPat (disjoint y subx); SMTPat (includes x subx)]
  = disjoint_includes_l x subx y;
    disjoint_sym subx y

let disjoint_includes_r
  #t1 #t2 #t3
  (p1: pointer t1)
  (p2: pointer t2)
  (p3: pointer t3)
: Lemma
  (requires (disjoint p1 p2 /\ includes p2 p3))
  (ensures (disjoint p1 p3))
  [SMTPat (disjoint p1 p2); SMTPat (includes p2 p3)]
= disjoint_sym p1 p2;
  disjoint_includes_l_swap p2 p3 p1

(* TODO: The following is now wrong, should be replaced with readable

let live_not_equal_disjoint
  (#t: typ)
  (h: HS.mem)
  (p1 p2: pointer t)
: Lemma
  (requires (live h p1 /\ live h p2 /\ equal p1 p2 == false))
  (ensures (disjoint p1 p2))
= if
    frameOf p1 = frameOf p2 &&
    as_addr p1 = as_addr p2
  then begin
    let c1 = greference_of p1 in
    let c2 = greference_of p2 in
    HS.lemma_same_addrs_same_types_same_refs h c1 c2;
    not_path_equal_path_disjoint_same_type p1.p p2.p
  end else
    disjoint_root p1 p2
*)


(*** The modifies clause *)

noeq
type loc_aux =
  | LocBuffer:
    (#t: typ) ->
    (b: buffer t) ->
    loc_aux
  | LocPointer:
    (#t: typ) ->
    (p: pointer t) ->
    loc_aux

(* Necessary to handle `exists` *)

let buffer_includes_pointer
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= exists (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) /\ gpointer_of_buffer_cell b i `includes` p

let loc_aux_includes_pointer
  (s: loc_aux)
  (#t: typ)
  (p: pointer t)
: GTot Type0
= match s with
  | LocPointer p' -> 
    p' `includes` p
  | LocBuffer b ->
    buffer_includes_pointer b p

let loc_aux_includes_pointer_trans
  (s: loc_aux)
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Lemma
  (requires (loc_aux_includes_pointer s p1 /\ p1 `includes` p2))
  (ensures (loc_aux_includes_pointer s p2))
= match s with
  | LocPointer p -> includes_trans p p1 p2
  | LocBuffer b ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (UInt32.v i < UInt32.v (buffer_length b) /\ gpointer_of_buffer_cell b i `includes` p1))
      (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ gpointer_of_buffer_cell b i `includes` p2))
    = includes_trans (gpointer_of_buffer_cell b i) p1 p2
    in
    Classical.forall_intro (Classical.move_requires f)

(* Same problem *)

let loc_aux_includes_buffer
  (s: loc_aux)
  (#t: typ)
  (b: buffer t)
: GTot Type0
= forall (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) ==> loc_aux_includes_pointer s (gpointer_of_buffer_cell b i)

let loc_aux_includes
  (s: loc_aux)
  (s2: loc_aux)
: GTot Type0
  (decreases s2)
= match s2 with
  | LocPointer p ->
    loc_aux_includes_pointer s p
  | LocBuffer b ->
    loc_aux_includes_buffer s b

let loc_aux_includes_refl'
  (s: loc_aux)
: Lemma
  (ensures (loc_aux_includes s s))
= ()

(* FIXME: WHY WHY WHY do I need to duplicate the lemma? Because Classical.forall_intro DOES NOT UNIFY/typecheck if there is a pattern *)
let loc_aux_includes_refl''
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
  [SMTPat (loc_aux_includes s s)]
= loc_aux_includes_refl' s

let loc_aux_includes_loc_aux_includes_pointer
  (s1: loc_aux)
  (s2: loc_aux)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_pointer s2 p))
  (ensures (loc_aux_includes_pointer s1 p))
= match s2 with
  | LocPointer p' ->
    loc_aux_includes_pointer_trans s1 p' p
  | LocBuffer b ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (UInt32.v i < UInt32.v (buffer_length b) /\ gpointer_of_buffer_cell b i `includes` p))
      (ensures (loc_aux_includes_pointer s1 p))
    = loc_aux_includes_pointer_trans s1 (gpointer_of_buffer_cell b i) p
    in
    Classical.forall_intro (Classical.move_requires f)

let loc_aux_includes_trans
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= match s3 with
  | LocPointer p ->
    loc_aux_includes_loc_aux_includes_pointer s1 s2 p
  | LocBuffer b ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (UInt32.v i < UInt32.v (buffer_length b)))
      (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_aux_includes_pointer s1 (gpointer_of_buffer_cell b i)))
    = loc_aux_includes_loc_aux_includes_pointer s1 s2 (gpointer_of_buffer_cell b i)
    in
    Classical.forall_intro (Classical.move_requires f)

(* the following is necessary because `decreases` messes up 2nd-order unification with `Classical.forall_intro_3` *)

let loc_aux_includes_trans'
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  ((loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3) ==> loc_aux_includes s1 s3)
= Classical.move_requires (loc_aux_includes_trans s1 s2) s3


(* Disjointness of two memory locations *)

let disjoint_buffer_vs_pointer
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= forall (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) ==> disjoint (gpointer_of_buffer_cell b i) p

let loc_aux_disjoint_pointer
  (l: loc_aux)
  (#t: typ)
  (p: pointer t)
: GTot Type0
= match l with
  | LocPointer p' -> disjoint p' p
  | LocBuffer b -> disjoint_buffer_vs_pointer b p

let loc_aux_disjoint_buffer
  (l: loc_aux)
  (#t: typ)
  (b: buffer t)
: GTot Type0
= forall (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) ==> loc_aux_disjoint_pointer l (gpointer_of_buffer_cell b i)

let loc_aux_disjoint_buffer_sym
  (#t1 #t2: typ)
  (b1: buffer t1)
  (b2: buffer t2)
: Lemma
  (loc_aux_disjoint_buffer (LocBuffer b1) b2 <==> loc_aux_disjoint_buffer (LocBuffer b2) b1)
= Classical.forall_intro_2 (disjoint_sym'' t1 t2)

let loc_aux_disjoint_pointer_buffer_sym
  (#t1 #t2: typ)
  (b1: buffer t1)
  (p2: pointer t2)
: Lemma
  (loc_aux_disjoint_pointer (LocBuffer b1) p2 <==> loc_aux_disjoint_buffer (LocPointer p2) b1)
= Classical.forall_intro_2 (disjoint_sym'' t1 t2)

let loc_aux_disjoint
  (l1 l2: loc_aux)
: GTot Type0
  (decreases l2)
= match l2 with
  | LocPointer p ->
    loc_aux_disjoint_pointer l1 p
  | LocBuffer b ->
    loc_aux_disjoint_buffer l1 b

let loc_aux_disjoint_sym
  (l1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
=
      begin match (l1, l2) with
      | (LocPointer p1, LocPointer p2) -> disjoint_sym' p1 p2
      | (LocPointer p1, LocBuffer b2) -> loc_aux_disjoint_pointer_buffer_sym b2 p1
      | (LocBuffer b1, LocPointer p2) -> loc_aux_disjoint_pointer_buffer_sym b1 p2
      | (LocBuffer b1, LocBuffer b2) -> loc_aux_disjoint_buffer_sym b1 b2
      end

(* Same problem with decreases here *)

let loc_aux_disjoint_sym'
  (l1 l2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1)
= loc_aux_disjoint_sym l1 l2

let loc_aux_disjoint_pointer_includes
  (l: loc_aux)
  (#t1: typ)
  (p1: pointer t1)
  (#t2: typ)
  (p2: pointer t2)
: Lemma
  (requires (loc_aux_disjoint_pointer l p1 /\ p1 `includes` p2))
  (ensures (loc_aux_disjoint_pointer l p2))
= ()

let loc_aux_disjoint_loc_aux_includes_pointer
  (l1 l2: loc_aux)
  (#t3: typ)
  (p3: pointer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_pointer l2 p3))
  (ensures (loc_aux_disjoint_pointer l1 p3))
= match l2 with
  | LocPointer p2 ->
    loc_aux_disjoint_pointer_includes l1 p2 p3
  | LocBuffer b2 ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (
        UInt32.v i < UInt32.v (buffer_length b2) /\
        gpointer_of_buffer_cell b2 i `includes` p3
      ))
      (ensures (loc_aux_disjoint_pointer l1 p3))
    = loc_aux_disjoint_pointer_includes l1 (gpointer_of_buffer_cell b2 i) p3
    in
    Classical.forall_intro (Classical.move_requires f)

let loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: loc_aux)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= match l3 with
  | LocPointer p3 ->
    loc_aux_disjoint_loc_aux_includes_pointer l1 l2 p3
  | LocBuffer b3 ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (
        UInt32.v i < UInt32.v (buffer_length b3)
      ))
      (ensures (
        UInt32.v i < UInt32.v (buffer_length b3) /\
        loc_aux_disjoint_pointer l1 (gpointer_of_buffer_cell b3 i)
      ))
    = loc_aux_disjoint_loc_aux_includes_pointer l1 l2 (gpointer_of_buffer_cell b3 i)
    in
    Classical.forall_intro (Classical.move_requires f)

let pointer_preserved
  (#t: typ)
  (p: pointer t)
  (h h' : HS.mem)
: GTot Type0
= equal_values h p h' p

let buffer_preserved
  (#t: typ)
  (b: buffer t)
  (h h' : HS.mem)
: GTot Type0
= forall (i: FStar.UInt32.t) . FStar.UInt32.v i < FStar.UInt32.v (buffer_length b) ==> pointer_preserved (gpointer_of_buffer_cell b i) h h'

let loc_aux_preserved (l: loc_aux) (h h' : HS.mem) : GTot Type0 =
  match l with
  | LocBuffer b -> buffer_preserved b h h'
  | LocPointer p -> pointer_preserved p h h'

let pointer_preserved_intro
  (#t: typ)
  (p: pointer t)
  (h1 h2 : HS.mem)
  (f: (
      (a' : Type0) ->
      (pre: Preorder.preorder a') ->
      (r': HS.mreference a' pre) ->
      Lemma
      (requires (h1 `HS.contains` r' /\ frameOf p == HS.frameOf r' /\ as_addr p == HS.as_addr r'))
      (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (pointer_preserved p h1 h2)
= let g () : Lemma
    (requires (live h1 p))
    (ensures (pointer_preserved p h1 h2))
  = f _ _ (greference_of p)
  in
  Classical.move_requires g ()

let buffer_preserved_intro
  (#t: typ)
  (p: buffer t)
  (h1 h2 : HS.mem)
  (f: (
      (a' : Type0) ->
      (pre: Preorder.preorder a') ->
      (r': HS.mreference a' pre) ->
      Lemma
      (requires (h1 `HS.contains` r' /\ frameOf_buffer p == HS.frameOf r' /\ buffer_as_addr p == HS.as_addr r'))
      (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (buffer_preserved p h1 h2)
= let g
    (i: FStar.UInt32.t { FStar.UInt32.v i < FStar.UInt32.v (buffer_length p) } )
  : Lemma
    (ensures (pointer_preserved (gpointer_of_buffer_cell p i) h1 h2))
  = pointer_preserved_intro (gpointer_of_buffer_cell p i) h1 h2 f
  in
  Classical.forall_intro g

let disjoint_not_self
  (#t: typ)
  (p: pointer t)
: Lemma
  (disjoint p p ==> False)
= Classical.move_requires (path_disjoint_not_path_equal (Pointer?.p p)) (Pointer?.p p)

let loc_aux_in_addr
  (l: loc_aux)
  (r: HS.rid)
  (n: nat)
: GTot Type0
= match l with
  | LocBuffer b ->
    frameOf_buffer b == r /\
    buffer_as_addr b == n
  | LocPointer p ->
    frameOf p == r /\
    as_addr p == n

let aloc (r: HS.rid) (n: nat) : Tot Type0 =
  (l: loc_aux { loc_aux_in_addr l r n } )

module MG = FStar.ModifiesGen

let cls : MG.cls aloc = MG.Cls #aloc
  (fun #r #a -> loc_aux_includes)
  (fun #r #a x -> ())
  (fun #r #a -> loc_aux_includes_trans)
  (fun #r #a -> loc_aux_disjoint)
  (fun #r #a -> loc_aux_disjoint_sym)
  (fun #r #a larger1 larger2 smaller1 smaller2 ->
    loc_aux_disjoint_loc_aux_includes larger1 larger2 smaller2;
    loc_aux_disjoint_sym larger1 smaller2;
    loc_aux_disjoint_loc_aux_includes smaller2 larger1 smaller1;
    loc_aux_disjoint_sym smaller2 smaller1
  )
  (fun #r #a -> loc_aux_preserved)
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f ->
    match b with
    | LocPointer p -> pointer_preserved_intro p h1 h2 f
    | LocBuffer p -> buffer_preserved_intro p h1 h2 f
  )

let loc = MG.loc cls

let loc_none = MG.loc_none

let loc_union = MG.loc_union

let loc_union_idem = MG.loc_union_idem

let loc_pointer #t p =
  MG.loc_of_aloc #_ #cls #(frameOf p) #(as_addr p) (LocPointer p)

let loc_buffer #t p =
  MG.loc_of_aloc #_ #cls #(frameOf_buffer p) #(buffer_as_addr p) (LocBuffer p)

let loc_addresses = MG.loc_addresses #_ #cls false

let loc_regions = MG.loc_regions false

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

let loc_includes_pointer_pointer #t1 #t2 p1 p2 =
  MG.loc_includes_aloc #_ #cls #(frameOf p1) #(as_addr p1) (LocPointer p1) (LocPointer p2)

let loc_includes_gsingleton_buffer_of_pointer l #t p =
  MG.loc_includes_aloc #_ #cls #(frameOf p) #(as_addr p) (LocPointer p) (LocBuffer (gsingleton_buffer_of_pointer p));
  MG.loc_includes_trans l (loc_pointer p) (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_includes_gbuffer_of_array_pointer l #len #t p =
  MG.loc_includes_aloc #_ #cls #(frameOf p) #(as_addr p) (LocPointer p) (LocBuffer (gbuffer_of_array_pointer p));
  MG.loc_includes_trans l (loc_pointer p) (loc_buffer (gbuffer_of_array_pointer p))

let loc_includes_gpointer_of_array_cell l #t b i =
  MG.loc_includes_aloc #_ #cls #(frameOf_buffer b) #(buffer_as_addr b) (LocBuffer b) (LocPointer (gpointer_of_buffer_cell b i));
  MG.loc_includes_trans l (loc_buffer b) (loc_pointer (gpointer_of_buffer_cell b i))

let loc_includes_gsub_buffer_r l #t b i len =
  MG.loc_includes_aloc #_ #cls #(frameOf_buffer b) #(buffer_as_addr b) (LocBuffer b) (LocBuffer (gsub_buffer b i len));
  MG.loc_includes_trans l (loc_buffer b) (loc_buffer (gsub_buffer b i len))

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  let b1 = gsub_buffer b i1 len1 in
  let b2 = gsub_buffer b1 (FStar.UInt32.sub i2 i1) len2 in
  MG.loc_includes_aloc #_ #cls #(frameOf_buffer b) #(buffer_as_addr b) (LocBuffer b1) (LocBuffer b2)

let loc_includes_addresses_pointer #t r s p =
  MG.loc_includes_addresses_aloc #_ #cls false r s #(as_addr p) (LocPointer p)

let loc_includes_addresses_buffer #t r s p =
  MG.loc_includes_addresses_aloc #_ #cls false r s #(buffer_as_addr p) (LocBuffer p)  

let loc_includes_region_pointer #t s p =
  MG.loc_includes_region_aloc #_ #cls false s #(frameOf p) #(as_addr p) (LocPointer p)

let loc_includes_region_buffer #t s b =
  MG.loc_includes_region_aloc #_ #cls false s #(frameOf_buffer b) #(buffer_as_addr b) (LocBuffer b)

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls false false

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls false false

let loc_includes_region_union_l = MG.loc_includes_region_union_l false

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

let loc_disjoint_root #value1 #value2 p1 p2 =
  MG.loc_disjoint_addresses #_ #cls false false (frameOf p1) (frameOf p2) (Set.singleton (as_addr p1)) (Set.singleton (as_addr p2));
  loc_includes_addresses_pointer (frameOf p1) (Set.singleton (as_addr p1)) p1;
  loc_includes_addresses_pointer (frameOf p2) (Set.singleton (as_addr p2)) p2;
  MG.loc_disjoint_includes #_ #cls (loc_addresses (frameOf p1) (Set.singleton (as_addr p1))) (loc_addresses (frameOf p2) (Set.singleton (as_addr p2))) (loc_pointer p1) (loc_pointer p2)

let loc_disjoint_gfield #l p fd1 fd2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf p) #(as_addr p) #(frameOf p) #(as_addr p) (LocPointer (gfield p fd1)) (LocPointer (gfield p fd2))

let loc_disjoint_gcell #length #value p i1 i2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf p) #(as_addr p) #(frameOf p) #(as_addr p) (LocPointer (gcell p i1)) (LocPointer (gcell p i2))

let loc_disjoint_includes = MG.loc_disjoint_includes

let live_unused_in_disjoint_strong #value1 #value2 h p1 p2 = ()

let live_unused_in_disjoint #value1 #value2 h p1 p2 =
  loc_disjoint_root p1 p2

let pointer_live_reference_unused_in_disjoint #value1 #value2 h p1 p2 =
  loc_includes_addresses_pointer (frameOf p1) (Set.singleton (as_addr p1)) p1;
  loc_includes_refl (MG.loc_freed_mreference p2);
  disjoint_roots_intro_pointer_vs_reference h p1 p2;
  MG.loc_disjoint_addresses #_ #cls false false (frameOf p1) (HS.frameOf p2) (Set.singleton (as_addr p1)) (Set.singleton (HS.as_addr p2));
  MG.loc_disjoint_includes #_ #cls (loc_addresses (frameOf p1) (Set.singleton (as_addr p1))) (MG.loc_freed_mreference p2) (loc_pointer p1) (MG.loc_freed_mreference p2)

let reference_live_pointer_unused_in_disjoint #value1 #value2 h p1 p2 =
  loc_includes_addresses_pointer (frameOf p2) (Set.singleton (as_addr p2)) p2;
  loc_includes_refl (MG.loc_freed_mreference p1);
  disjoint_roots_intro_reference_vs_pointer h p1 p2;
  MG.loc_disjoint_addresses #_ #cls false false (HS.frameOf p1) (frameOf p2) (Set.singleton (HS.as_addr p1)) (Set.singleton (as_addr p2));
  MG.loc_disjoint_includes #_ #cls (MG.loc_freed_mreference p1) (loc_addresses (frameOf p2) (Set.singleton (as_addr p2))) (MG.loc_freed_mreference p1) (loc_pointer p2)

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf_buffer b) #(buffer_as_addr b) #(frameOf_buffer b) #(buffer_as_addr b) (LocBuffer (gsub_buffer b i1 len1)) (LocBuffer (gsub_buffer b i2 len2))

let loc_disjoint_gpointer_of_buffer_cell #t b i1 i2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf_buffer b) #(buffer_as_addr b) #(frameOf_buffer b) #(buffer_as_addr b) (LocPointer (gpointer_of_buffer_cell b i1)) (LocPointer (gpointer_of_buffer_cell b i2))

let loc_disjoint_addresses = MG.loc_disjoint_addresses #_ #cls false false

let loc_disjoint_pointer_addresses #t p r n =
  loc_disjoint_includes (loc_addresses (frameOf p) (Set.singleton (as_addr p))) (loc_addresses r n) (loc_pointer p) (loc_addresses r n)

let loc_disjoint_buffer_addresses #t p r n =
  loc_disjoint_includes (loc_addresses (frameOf_buffer p) (Set.singleton (buffer_as_addr p))) (loc_addresses r n) (loc_buffer p) (loc_addresses r n)

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls false false

let modifies = MG.modifies

let modifies_loc_regions_intro rs h1 h2 =
  MG.modifies_loc_regions_intro #_ #cls rs h1 h2;
  MG.loc_includes_region_region #_ #cls false true rs rs;
  MG.modifies_loc_includes (loc_regions rs) h1 h2 (MG.loc_regions true rs)

let modifies_pointer_elim s h1 h2 #a' p' =
  MG.modifies_aloc_elim #_ #_ #(frameOf p') #(as_addr p') (LocPointer p') s h1 h2

val modifies_buffer_elim'
  (#t1: typ)
  (b: buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    buffer_live h b /\
    UInt32.v (buffer_length b) > 0 /\
    modifies p h h'
  ))
  (ensures (
    buffer_live h' b /\ (
      buffer_readable h b ==> (
	buffer_readable h' b /\
	buffer_as_seq h b == buffer_as_seq h' b
  ))))

let modifies_buffer_elim' #t1 b p h h' =
  Classical.forall_intro_2 HS.lemma_tip_top;
  loc_disjoint_sym (loc_buffer b) p;
  let n = UInt32.v (buffer_length b) in
  begin
    assert (n > 0);
    let pre
      (i: UInt32.t)
    : GTot Type0
    = UInt32.v i < n
    in
    let post
      (i: UInt32.t)
    : GTot Type0
    = pre i /\ (
	  let q = gpointer_of_buffer_cell b i in
	  equal_values h q h' q
      )
    in
    let f
      (i: UInt32.t)
    : Lemma
      (requires (pre i))
      (ensures (post i))
    = modifies_pointer_elim p h h' (gpointer_of_buffer_cell b i)
    in
    f 0ul; // for the liveness of the whole buffer
    Classical.forall_intro (Classical.move_requires f);
    assert (buffer_readable h b ==> buffer_readable h' b);
    let g () : Lemma
      (requires (buffer_readable h b))
      (ensures (buffer_as_seq h b == buffer_as_seq h' b))
    = let s = buffer_as_seq h b in
      let s' = buffer_as_seq h' b in
      Seq.lemma_eq_intro s s';
      Seq.lemma_eq_elim s s'
    in
    Classical.move_requires g ()
  end

let modifies_buffer_elim #t1 b p h h' =
  if buffer_length b = 0ul
  then ()
  else modifies_buffer_elim' b p h h'

let modifies_reference_elim #t b p h h' =
  MG.loc_includes_addresses_addresses #_ cls false true (HS.frameOf b) (Set.singleton (HS.as_addr b)) (Set.singleton (HS.as_addr b));
  MG.loc_includes_refl p;
  MG.loc_disjoint_includes (MG.loc_freed_mreference b) p (MG.loc_mreference b) p;
  MG.modifies_mreference_elim b p h h'

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let modifies_trans = MG.modifies_trans

(** Concrete allocators, getters and setters *)

let screate
  (value:typ)
  (s: option (type_of_typ value))
= let h0 = HST.get () in
  let s = match s with
  | Some s -> ovalue_of_value value s
  | _ -> none_ovalue value
  in
  let content: HS.reference pointer_ref_contents =
     HST.salloc (| value, s |)
  in
  let aref = HS.aref_of content in
  let p = Pointer value aref PathBase in
  let h1 = HST.get () in
  assert (HS.aref_live_at h1 aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents));
  let f () : Lemma (
    let gref = HS.greference_of aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) in
    HS.sel h1 gref == HS.sel h1 content
  )
  = let gref = HS.greference_of aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) in
    assert (HS.frameOf content == HS.frameOf gref);
    assert (HS.as_addr content == HS.as_addr gref);
    HS.lemma_sel_same_addr h1 content gref
  in
  f ();
  MG.modifies_intro loc_none h0 h1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r a b ->
      cls.MG.same_mreference_aloc_preserved b h0 h1 (fun _ _ _ -> ())
    )
  ;
  p

// TODO: move to HyperStack?
let domain_upd (#a:Type) (h:HS.mem) (x:HS.reference a{HS.live_region h (HS.frameOf x)}) (v:a) : Lemma
  (requires True)
  (ensures  (Map.domain (HS.get_hmap h) == Map.domain (HS.get_hmap (HS.upd h x v))))
  = let m = (HS.get_hmap h) in
    let m' = Map.upd m (HS.frameOf x) (Heap.upd (Map.sel m (HS.frameOf x)) (HS.as_ref x) v) in
    Set.lemma_equal_intro (Map.domain m) (Map.domain m')

let ecreate
  (t:typ)
  (r:HS.rid)
  (s: option (type_of_typ t))
= let h0 = HST.get () in
  let s0 = s in
  let s = match s with
  | Some s -> ovalue_of_value t s
  | _ -> none_ovalue t
  in
  let content: HS.ref pointer_ref_contents =
     HST.ralloc r (| t, s |)
  in
  domain_upd h0 content (| t, s |) ;
  let aref = HS.aref_of content in
  let p = Pointer t aref PathBase in
  let h1 = HST.get () in
  assert (HS.aref_live_at h1 aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents));
  let f () : Lemma (
    let gref = HS.greference_of aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) in
    HS.sel h1 gref == HS.sel h1 content
  )
  = let gref = HS.greference_of aref pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) in
    assert (HS.frameOf content == HS.frameOf gref);
    assert (HS.as_addr content == HS.as_addr gref);
    HS.lemma_sel_same_addr h1 content gref
  in
  f ();
  MG.modifies_intro loc_none h0 h1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r a b ->
      cls.MG.same_mreference_aloc_preserved b h0 h1 (fun _ _ _ -> ())
    )
  ;
  p

let field
 (#l: struct_typ)
 (p: pointer (TStruct l))
 (fd: struct_field l)
= _field p fd

let ufield
 (#l: union_typ)
 (p: pointer (TUnion l))
 (fd: struct_field l)
= _ufield p fd

let cell
 (#length: array_length_t)
 (#value: typ)
 (p: pointer (TArray length value))
 i
= _cell p i

let reference_of
  (#value: typ)
  (h: HS.mem)
  (p: pointer value)
: Pure (HS.reference pointer_ref_contents)
  (requires (live h p))
  (ensures (fun x -> 
    live h p /\
    x == HS.reference_of h (Pointer?.contents p) pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents) /\
    HS.frameOf x == HS.frameOf (greference_of p) /\
    HS.as_addr x == HS.as_addr (greference_of p) /\
    (forall h' . h' `HS.contains` x <==> h' `HS.contains` (greference_of p)) /\
    (forall h' . (h' `HS.contains` x \/ h' `HS.contains` (greference_of p)) ==> (h' `HS.contains` x /\ h' `HS.contains` (greference_of p) /\ HS.sel h' x == HS.sel h' (greference_of p))) /\
    (forall h' z .
      (h' `HS.contains` x \/ h' `HS.contains` (greference_of p)) ==>
      (h' `HS.contains` x /\ h' `HS.contains` (greference_of p) /\ HS.upd h' x z == HS.upd h' (greference_of p) z)
  )))
= let x =
    HS.reference_of h (Pointer?.contents p) pointer_ref_contents (Heap.trivial_preorder pointer_ref_contents)
  in
  let f (h' : HS.mem) : Lemma
    ( (exists h' . live h' p) /\ // necessary to typecheck Classical.forall_intro
      (h' `HS.contains` x <==> h' `HS.contains` (greference_of p)) /\
    ((h' `HS.contains` x \/ h' `HS.contains` (greference_of p)) ==> HS.sel h' x == HS.sel h' (greference_of p)))
  = let y = greference_of p in
    Classical.move_requires (HS.lemma_sel_same_addr h' y) x;
    Classical.move_requires (HS.lemma_sel_same_addr h' x) y
  in
  let g (z: pointer_ref_contents) (h' : HS.mem) : Lemma (
    (exists h' . live h' p) /\
    ((h' `HS.contains` x \/ h' `HS.contains` (greference_of p)) ==> (h' `HS.contains` x /\ h' `HS.contains` (greference_of p) /\ HS.upd h' x z == HS.upd h' (greference_of p) z))
  )
  = let y = greference_of p in
    Classical.move_requires (HS.lemma_upd_same_addr h' y x) z;
    Classical.move_requires (HS.lemma_upd_same_addr h' x y) z
  in
  Classical.forall_intro f ;
  Classical.forall_intro_2 g;
  x

let read
 (#value: typ)
 (p: pointer value)
= let h = HST.get () in
  let r = reference_of h p in
  HST.witness_region (HS.frameOf r);
  HST.witness_hsref r;
  let (| _ , c |) = !r in
  value_of_ovalue value (path_sel c (Pointer?.p p))

let is_null
  (#t: typ)
  (p: npointer t)
= match p with
  | NullPtr -> true
  | _ -> false

let owrite
  (#a: typ)
  (b: pointer a)
  (z: otype_of_typ a)
: HST.Stack unit
  (requires (fun h -> live h b))
  (ensures (fun h0 _ h1 ->
    live h0 b /\
    live h1 b /\
    modifies_1 b h0 h1 /\ (
    let g = greference_of b in
    let (| _, c1 |) = HS.sel h1 g in
    path_sel c1 (Pointer?.p b) == z
  )))
= let h0 = HST.get () in
  let r = reference_of h0 b in
  HST.witness_region (HS.frameOf r);
  HST.witness_hsref r;
  let v0 = !r in
  let (| t , c0 |) = v0 in
  let c1 = path_upd c0 (Pointer?.p b) z in
  let v1 = (| t, c1 |) in
  r := v1;
  let h1 = HST.get () in
  let e () : Lemma (
   let gref = greference_of b in (
    HS.frameOf r == HS.frameOf gref /\
    HS.as_addr r == HS.as_addr gref /\
    HS.sel h0 gref == v0 /\
    HS.sel h1 gref == v1
  ))
  = let gref = greference_of b in
    HS.lemma_sel_same_addr h0 r gref;
    HS.lemma_sel_same_addr h1 r gref
  in
  e ();
  let prf_alocs
    (r': HS.rid)
    (a': nat)
    (b' : aloc r' a')
  : Lemma
    (requires (MG.loc_disjoint (MG.loc_of_aloc b') (loc_pointer b)))
    (ensures (cls.MG.aloc_preserved b' h0 h1))
  =
    let f
      (t: typ)
      (p: pointer t)
    : Lemma
      (requires (
        live h0 p /\
        disjoint b p
      ))
      (ensures (
        equal_values h0 p h1 p
      ))
    = let grefp = greference_of p in
      if frameOf p = frameOf b && as_addr p = as_addr b
      then begin
        HS.lemma_sel_same_addr h0 r grefp;
        HS.lemma_sel_same_addr h1 r grefp;
        path_sel_upd_other' (Pointer?.p b) c0 z (Pointer?.p p)
      end
      else ()
    in
    let f'
      (t: typ)
      (p: pointer t)
    : Lemma
      ( (
        live h0 p /\
        disjoint b p
      ) ==> (
        equal_values h0 p h1 p
      ))
    = Classical.move_requires (f t) p
    in
    MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(frameOf b) #(as_addr b) b' (LocPointer b);
    Classical.forall_intro_2 f'
  in
  MG.modifies_intro (loc_pointer b) h0 h1
    (fun _ -> ())
    (fun t' pre' p' ->
      loc_disjoint_sym (MG.loc_mreference p') (loc_pointer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(frameOf b) #(as_addr b) (LocPointer b) true (HS.frameOf p') (Set.singleton (HS.as_addr p'))
    )
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    prf_alocs

let write #a b z =
  owrite b (ovalue_of_value a z)

let write_union_field
  (#l: union_typ)
  (p: pointer (TUnion l))
  (fd: struct_field l)
= let field_t : typ = typ_of_struct_field l fd in

  // We could avoid removing the data if `fd` is already the current tag.

  // However this seems impossible to specify with the current set of
  // user-available predicates and functions (the only thing we have to
  // distinguish between actual data and dummy values is `readable`, which is
  // too coarse-grained for our needs).
  let vu : option (gtdata (struct_field l) (type_of_struct_field' l otype_of_typ)) =
    Some (gtdata_create fd (none_ovalue field_t)) in
  let vu : otype_of_typ (TUnion l) = vu in
  owrite p vu

(** Lemmas and patterns *)

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_only_live_regions = MG.modifies_only_live_regions

let modifies_loc_addresses_intro r a l h1 h2 =
  MG.modifies_loc_addresses_intro r a l h1 h2;
  MG.loc_includes_addresses_addresses #_ cls false true r a a;
  MG.loc_includes_refl l;
  MG.loc_includes_union_l (loc_addresses r a) l l;
  MG.loc_includes_union_l (loc_addresses r a) l (MG.loc_addresses true r a);
  MG.loc_includes_union_r (loc_union (loc_addresses r a) l) (MG.loc_addresses true r a) l;
  MG.modifies_loc_includes (loc_union (loc_addresses r a) l) h1 h2 (loc_union (MG.loc_addresses true r a) l)

(* `modifies` and the readable permission *)

(** NOTE: we historically used to have this lemma for arbitrary
pointer inclusion, but that became wrong for unions. *)

let modifies_1_readable_struct #l f p h h' =
  readable_struct h' p

let modifies_1_readable_array #t #len i p h h' =
  readable_array h' p

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)
		
let read_buffer		
  (#t: typ)		
  (b: buffer t)		
  i		
= read (pointer_of_buffer_cell b i)		
		
let write_buffer		
  (#t: typ)		
  (b: buffer t)		
  i v		
= write (pointer_of_buffer_cell b i) v		

(* unused_in, cont'd *)

let buffer_live_unused_in_disjoint #t1 #t2 h b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf_buffer b1)  #(buffer_as_addr b1) #(frameOf_buffer b2) #(buffer_as_addr b2) (LocBuffer b1) (LocBuffer b2)

let pointer_live_buffer_unused_in_disjoint #t1 #t2 h b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf b1) #(as_addr b1) #(frameOf_buffer b2) #(buffer_as_addr b2) (LocPointer b1) (LocBuffer b2)

let buffer_live_pointer_unused_in_disjoint #t1 #t2 h b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(frameOf_buffer b1) #(buffer_as_addr b1) #(frameOf b2) #(as_addr b2) (LocBuffer b1) (LocPointer b2)

let reference_live_buffer_unused_in_disjoint #t1 #t2 h b1 b2 =
  loc_includes_addresses_buffer (frameOf_buffer b2) (Set.singleton (buffer_as_addr b2)) b2;
  loc_includes_refl (MG.loc_freed_mreference b1);
  MG.loc_disjoint_addresses #_ #cls false false (HS.frameOf b1) (frameOf_buffer b2) (Set.singleton (HS.as_addr b1)) (Set.singleton (buffer_as_addr b2));
  MG.loc_disjoint_includes #_ #cls (MG.loc_freed_mreference b1) (loc_addresses (frameOf_buffer b2) (Set.singleton (buffer_as_addr b2))) (MG.loc_freed_mreference b1) (loc_buffer b2)

let buffer_live_reference_unused_in_disjoint #t1 #t2 h b1 b2 =
  loc_includes_addresses_buffer (frameOf_buffer b1) (Set.singleton (buffer_as_addr b1)) b1;
  loc_includes_refl (MG.loc_freed_mreference b2);
  (match b1.broot with
    | BufferRootSingleton p1 -> disjoint_roots_intro_pointer_vs_reference h p1 b2
    | BufferRootArray p1 -> disjoint_roots_intro_pointer_vs_reference h p1 b2
  );
  MG.loc_disjoint_addresses #_ #cls false false (frameOf_buffer b1) (HS.frameOf b2) (Set.singleton (buffer_as_addr b1)) (Set.singleton (HS.as_addr b2));
  MG.loc_disjoint_includes #_ #cls (loc_addresses (frameOf_buffer b1) (Set.singleton (buffer_as_addr b1))) (MG.loc_freed_mreference b2) (loc_buffer b1) (MG.loc_freed_mreference b2)

(* Buffer inclusion without existential quantifiers: remnants of the legacy buffer interface *)

let root_buffer #t b =
  let root = Buffer?.broot b in 
  match root with
  | BufferRootSingleton p -> Buffer root 0ul 1ul
  | BufferRootArray #_ #len _ -> Buffer root 0ul len

let buffer_idx #t b =
  Buffer?.bidx b

let buffer_eq_gsub_root #t b =
  assert (UInt32.add 0ul (buffer_idx b) == buffer_idx b)

let root_buffer_gsub_buffer #t b i len = ()

let buffer_idx_gsub_buffer #t b i len = ()

let buffer_includes #t blarge bsmall =
  let () = () in (
    root_buffer blarge == root_buffer bsmall /\
    UInt32.v (buffer_idx blarge) <= UInt32.v (buffer_idx bsmall) /\
    UInt32.v (buffer_idx bsmall) + UInt32.v (buffer_length bsmall) <= UInt32.v (buffer_idx blarge) + UInt32.v (buffer_length blarge)
  )

let buffer_includes_refl #t b = ()

let buffer_includes_trans #t b1 b2 b3 = ()

let buffer_includes_gsub_r #t b i len = ()

let buffer_includes_gsub #t b i1 i2 len1 len2 = ()

let buffer_includes_elim #t b1 b2 = ()

let buffer_includes_loc_includes #t b1 b2 =
  buffer_includes_elim b1 b2;
  loc_includes_refl (loc_buffer b1);
  loc_includes_gsub_buffer_r (loc_buffer b1) b1 (UInt32.sub (buffer_idx b2) (buffer_idx b1)) (buffer_length b2)


(* Type class instance *)

let cloc_aloc = aloc

let cloc_cls = cls

let cloc_of_loc l = l

let loc_of_cloc l = l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
