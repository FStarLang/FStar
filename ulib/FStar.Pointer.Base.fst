module FStar.Pointer.Base

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open HST // for := , !

(*** Definitions *)

(** Pointers to data of type t.

    This defines two main types:
    - `npointer (t: typ)`, a pointer that may be "NULL";
    - `pointer (t: typ)`, a pointer that cannot be "NULL"
      (defined as a refinement of `npointer`).

    `nullptr #t` (of type `npointer t`) represents the "NULL" value.
*)

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
    typ_depth_typ_of_struct_field l fd
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
| BufferRootArray #t #len _ -> len

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
  (key: eqtype u#0)
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

(** Interpretation of unions, as ghostly-tagged data
    (see `gtdata` for more information).
*)
let _union_get_key (#l: union_typ) (v: union l) : Tot (struct_field l) = _gtdata_get_key v

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
    let dummy_field : string = List.Tot.hd (List.Tot.map fst l) in
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
= if List.Tot.mem s (List.Tot.map fst l)
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
      let keys = List.Tot.map fst l in
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
    List.Tot.for_all (struct_field_is_readable l ovalue_is_readable v) (List.Tot.map fst l)
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
= List.Tot.for_all_mem (struct_field_is_readable l ovalue_is_readable v) (List.Tot.map fst l);
  ovalue_is_readable_struct_intro' l v

let rec ovalue_is_readable_struct_elim
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
  assert_norm (ovalue_is_readable (TStruct l) v == List.Tot.for_all (struct_field_is_readable l ovalue_is_readable v) (List.Tot.map fst l));
  assert (List.Tot.for_all (struct_field_is_readable l ovalue_is_readable v) (List.Tot.map fst l));
  List.Tot.for_all_mem (struct_field_is_readable l ovalue_is_readable v) (List.Tot.map fst l);
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

#reset-options "--z3rlimit 16"

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
    DM.equal_elim #(struct_field l) #(type_of_struct_field l) v' v
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
  (x: (#to1: typ) ->
      (#to2: typ) ->
      (p1: path from to1) ->
      (p2: path from to2 {path_includes p1 p2} ) ->
      GTot Type0)
  (h_step:
    (#through: typ) ->
    (#to: typ) ->
    (p: path from through) ->
    (s: step through to { path_includes p (PathStep through to p s) } ) ->
    Lemma (x p (PathStep through to p s)))
  (h_refl:
    (#to: typ) ->
    (p: path from to {path_includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#to1: typ) ->
    (#to2: typ) ->
    (#to3: typ) ->
    (p1: path from to1) ->
    (p2: path from to2) ->
    (p3: path from to3 {path_includes p1 p2 /\ path_includes p2 p3 /\ path_includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
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
    (fun #through #to_ p s -> FStar.Classical.exists_intro (fun r -> PathStep through to_ p s == path_concat p r) (PathStep through to_ PathBase s))
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
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (h: path_disjoint_t p1 p2) ->
    GTot Type)
  (h_step:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 } ) ->
    (h: path_disjoint_t (PathStep through to1 p s1) (PathStep through to2 p s2)) ->
    GTot (x (PathStep through to1 p s1) (PathStep through to2 p s2) h))
  (h_includes:
    (#value1: typ) ->
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
    GTot (x p1' p2' h'))
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

let path_disjoint_ind
  (#from: typ)
  (x:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2 {path_disjoint p1 p2} ) ->
    GTot Type)
  (h_step:
    (#through: typ) ->
    (#to1: typ) ->
    (#to2: typ) ->
    (p: path from through) ->
    (s1: step through to1) ->
    (s2: step through to2 { step_disjoint s1 s2 /\ path_disjoint (PathStep through to1 p s1) (PathStep through to2 p s2) } ) ->
    Lemma (x (PathStep through to1 p s1) (PathStep through to2 p s2) ))
  (h_includes:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: path from value1) ->
    (p2: path from value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': path from value1' {path_includes p1 p1'}) ->
    (p2': path from value2' {path_includes p2 p2' /\ path_disjoint p1 p2 /\ path_disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
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
= FStar.Squash.return_squash (PathDisjointStep p s1 s2)

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

let rec path_disjoint_sym
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
  (fun #v1 #v2 p1 p2 -> exists (d: path_disjoint_decomp_t p1 p2) . True)
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
      FStar.Classical.forall_intro' #_ #(fun m -> forall  (v: otype_of_typ to1_) . path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun m ->
	  FStar.Classical.forall_intro' #_ #(fun v -> path_sel (path_upd m (PathStep through to1_ p s1) v) (PathStep through to2_ p s2) == path_sel m (PathStep through to2_ p s2)) (fun v ->
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
    FStar.Classical.forall_intro' #_ #(fun (m: otype_of_typ from) -> forall v . path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (m: otype_of_typ from) ->
      FStar.Classical.forall_intro' #_ #(fun (v: otype_of_typ v1') -> path_sel (path_upd m p1' v) p2' == path_sel m p2') (fun (v: otype_of_typ v1') ->
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

let as_addr (#t: typ) (p: pointer t): GTot nat =
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
: GTot HH.rid
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
  (p: pointer value {HS.is_eternal_region (frameOf p) && not (is_mm p)})
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
  (x: (#value1: typ) ->
      (#value2: typ) ->
      (p1: pointer value1) ->
      (p2: pointer value2 {includes p1 p2} ) ->
      GTot Type0)
  (h_field:
    (l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd: struct_field l {includes p (gfield p fd)}) ->
    Lemma (x p (gfield p fd)))
  (h_ufield:
    (l: union_typ) ->
    (p: pointer (TUnion l)) ->
    (fd: struct_field l {includes p (gufield p fd)}) ->
    Lemma (x p (gufield p fd)))
  (h_cell:
    (#length: array_length_t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i: UInt32.t {UInt32.v i < UInt32.v length /\ includes p (gcell p i)}) ->
    Lemma (x p (gcell p i)))
  (h_refl:
    (#value: typ) ->
    (p: pointer value {includes p p}) ->
    Lemma (x p p))
  (h_trans:
    (#value1: typ) ->
    (#value2: typ) ->
    (#value3: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (p3: pointer value3 {includes p1 p2 /\ includes p2 p3 /\ includes p1 p3 /\ x p1 p2 /\ x p2 p3}) ->
    Lemma (x p1 p3))
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
= let dummy_field : struct_field l = fst (List.Tot.hd l) in // struct is nonempty
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
      if List.Tot.mem f (List.Tot.map fst l)
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
  (ensures (forall f . (List.Tot.mem f s /\ List.Tot.mem f (List.Tot.map fst l)) ==> (let f : struct_field l = f in readable h (gfield p f))))
  (decreases s)
= match s with
  | [] -> ()
  | _ :: q -> readable_struct_fields_elim h p q

let readable_struct_fields_readable_struct #l h p =
  readable_struct_fields_elim h p (List.Tot.map fst l);
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
    | BufferRootArray #mlen p -> live h p
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

let frameOf_buffer
  (#t: typ)
  (b: buffer t)
: GTot HH.rid
= match b.broot with
  | BufferRootSingleton p -> frameOf p
  | BufferRootArray #mlen p -> frameOf p

let frameOf_buffer_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
= ()

let frameOf_buffer_gbuffer_of_array_pointer
  (#t: typ)
  (#length: array_length_t)
  (p: pointer (TArray length t))
= ()

let buffer_as_addr #t b =
  match b.broot with
  | BufferRootSingleton p -> as_addr p
  | BufferRootArray #mlen p -> as_addr p

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
  Buffer (Buffer?.broot b) FStar.UInt32.(Buffer?.bidx b +^ i) (UInt32.sub (Buffer?.blength b) i)

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

let gpointer_of_buffer_cell_gsingleton_buffer_of_pointer
  (#t: typ)
  (p: pointer t)
  i
= ()

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
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 {disjoint p1 p2} ) ->
    GTot Type0)
  (h_root:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2 { frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2 } ) ->
    Lemma (x p1 p2))
  (h_field:
    (#l: struct_typ) ->
    (p: pointer (TStruct l)) ->
    (fd1: struct_field l) ->
    (fd2: struct_field l { fd1 <> fd2 /\ disjoint (gfield p fd1) (gfield p fd2) } ) ->
    Lemma (x (gfield p fd1) (gfield p fd2)))
  (h_cell:
    (#length: array_length_t) ->
    (#value: typ) ->
    (p: pointer (TArray length value)) ->
    (i1: UInt32.t {UInt32.v i1 < UInt32.v length}) ->
    (i2: UInt32.t {UInt32.v i2 < UInt32.v length /\ UInt32.v i1 <> UInt32.v i2 /\ disjoint (gcell p i1) (gcell p i2) }) ->
    Lemma (x (gcell p i1) (gcell p i2))
  )
  (h_includes:
    (#value1: typ) ->
    (#value2: typ) ->
    (p1: pointer value1) ->
    (p2: pointer value2) ->
    (#value1': typ) ->
    (#value2': typ) ->
    (p1': pointer value1' {includes p1 p1'}) ->
    (p2': pointer value2' {includes p2 p2' /\ disjoint p1 p2 /\ disjoint p1' p2' /\ x p1 p2}) ->
    Lemma (x p1' p2'))
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

let disjoint_includes_l #a #as #a' (x: pointer a) (subx:pointer as) (y:pointer a') : Lemma
  (requires (includes x subx /\ disjoint x y))
  (ensures  (disjoint subx y))
  [SMTPat (disjoint subx y); SMTPat (includes x subx)]
  = disjoint_includes x y subx y

let disjoint_includes_l_swap #a #as #a' (x:pointer a) (subx:pointer as) (y:pointer a') : Lemma
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
type loc_aux : Type0 =
  | LocBuffer:
    (#t: typ) ->
    (b: buffer t) ->
    loc_aux
  | LocPointer:
    (#t: typ) ->
    (p: pointer t) ->
    loc_aux
  | LocUnion:
    (l1: loc_aux) ->
    (l2: loc_aux) ->
    loc_aux

let rec loc_aux_in_addr
  (l: loc_aux)
  (r: HH.rid)
  (n: nat)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion l1 l2 -> loc_aux_in_addr l1 r n /\ loc_aux_in_addr l2 r n
  | LocBuffer b ->
    frameOf_buffer b == r /\
    buffer_as_addr b == n /\
    UInt32.v (buffer_length b) > 0
  | LocPointer p ->
    frameOf p == r /\
    as_addr p == n

(* TODO: move to FStar.Set?
   Necessary to handle quantifiers *)
let set_nonempty
  (#t: eqtype)
  (s: Set.set t)
: GTot Type0
= exists (i: t) . Set.mem i s

noeq
type loc' : Type0 =
  | Loc:
      (whole_regions: Ghost.erased (Set.set HH.rid)) ->
      (addr_regions: Ghost.erased (Set.set HH.rid)) ->
      (addrs: (
	(r: HH.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal addr_regions)))
	(ensures (fun _ -> True))
      )) ->
      (aux_regions: Ghost.erased (Set.set HH.rid)) ->
      (aux_addrs: (
	(r: HH.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal aux_regions)))
	(ensures (fun y -> set_nonempty y))
      )) ->
      (aux: (
	(r: HH.rid) ->
	(n: nat) ->
	Ghost loc_aux
	(requires (
	  Set.mem r (Ghost.reveal aux_regions) /\
	  Set.mem n (aux_addrs r)
	))
	(ensures (fun y ->
          loc_aux_in_addr y r n
      )))) ->
      loc'

let loc = loc'

let aux_addrs_nonempty
  (l: loc)
: Lemma
  (forall r .
    Set.mem r (Ghost.reveal (Loc?.aux_regions l)) ==>
    (exists i . Set.mem i (Loc?.aux_addrs l r))
  )
= let f
    (r: HH.rid)
  : Lemma
    (requires (Set.mem r (Ghost.reveal (Loc?.aux_regions l))))
    (ensures (Set.mem r (Ghost.reveal (Loc?.aux_regions l)) /\ set_nonempty (Loc?.aux_addrs l r)))
  = ()
  in
  Classical.forall_intro (Classical.move_requires f)

let loc_none = Loc
  (Ghost.hide (Set.empty))
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (fun _ _ -> false_elim ())

let loc_union s1 s2 =
  let addr_regions1 = Ghost.reveal (Loc?.addr_regions s1) in
  let addr_regions2 = Ghost.reveal (Loc?.addr_regions s2) in
  let addr_regions = Set.union addr_regions1 addr_regions2 in
  let addrs
    (r: HH.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r addr_regions))
    (ensures (fun _ -> True))
  = Set.union
      (if Set.mem r addr_regions1 then Loc?.addrs s1 r else Set.empty)
      (if Set.mem r addr_regions2 then Loc?.addrs s2 r else Set.empty)
  in
  let aux_regions1 = Ghost.reveal (Loc?.aux_regions s1) in
  let aux_regions2 = Ghost.reveal (Loc?.aux_regions s2) in
  let aux_regions = Set.union aux_regions1 aux_regions2 in
  let aux_addrs
    (r: HH.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r aux_regions))
    (ensures (fun y -> exists i . Set.mem i y))
  = Set.union
      (if Set.mem r aux_regions1 then Loc?.aux_addrs s1 r else Set.empty)
      (if Set.mem r aux_regions2 then Loc?.aux_addrs s2 r else Set.empty)
  in
  let aux
    (r: HH.rid)
    (n: nat)
  : Ghost loc_aux
    (requires (Set.mem r aux_regions /\ Set.mem n (aux_addrs r)))
    (ensures (fun y -> loc_aux_in_addr y r n))
  = let l1 =
      if Set.mem r aux_regions1 && Set.mem n (Loc?.aux_addrs s1 r)
      then Some (Loc?.aux s1 r n)
      else None
    in
    let l2 =
      if Set.mem r aux_regions2 && Set.mem n (Loc?.aux_addrs s2 r)
      then Some (Loc?.aux s2 r n)
      else None
    in
    match l1, l2 with
    | Some l1, Some l2 -> LocUnion l1 l2
    | Some l1, _ -> l1
    | _, Some l2 -> l2
  in
  Loc
    (Ghost.hide (Set.union (Ghost.reveal (Loc?.whole_regions s1)) (Ghost.reveal (Loc?.whole_regions s2))))
    (Ghost.hide addr_regions)
    addrs
    (Ghost.hide aux_regions)
    aux_addrs
    aux

let loc_pointer #t p =
  Loc
    (Ghost.hide Set.empty)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (Ghost.hide (Set.singleton (frameOf p)))
    (fun _ -> Set.singleton (as_addr p))
    (fun _ _ -> LocPointer p)

let loc_buffer #t b =
  if UInt32.v (buffer_length b) = 0
  then loc_none
  else
  Loc
    (Ghost.hide Set.empty)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (Ghost.hide (Set.singleton (frameOf_buffer b)))
    (fun _ -> Set.singleton (buffer_as_addr b))
    (fun _ _ -> LocBuffer b)

let loc_addresses r n =
  Loc
    (Ghost.hide Set.empty)
    (Ghost.hide (Set.singleton r))
    (fun _ -> n)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let loc_regions r =
  Loc
    (Ghost.hide r)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let rec loc_aux_syntactically_includes
  (s1 s2: loc_aux)
: GTot Type0
  (decreases s1)
= s1 == s2 \/ (
    match s1 with
    | LocUnion sl sr -> loc_aux_syntactically_includes sl s2 \/ loc_aux_syntactically_includes sr s2
    | _ -> False
  )

let loc_aux_syntactically_includes_refl
  (s: loc_aux)
: Lemma
  (loc_aux_syntactically_includes s s)
= ()

let rec loc_aux_syntactically_includes_trans
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s1 s2 /\ loc_aux_syntactically_includes s2 s3))
  (ensures (loc_aux_syntactically_includes s1 s3))
  (decreases s1)
= match s1 with
  | LocUnion sl sr ->
    Classical.or_elim
      #(loc_aux_syntactically_includes sl s2)
      #(loc_aux_syntactically_includes sr s2)
      #(fun _ -> loc_aux_syntactically_includes s1 s3)
      (fun _ -> loc_aux_syntactically_includes_trans sl s2 s3)
      (fun _ -> loc_aux_syntactically_includes_trans sr s2 s3)
  | _ -> ()

let loc_aux_syntactically_includes_union_r
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s1 (LocUnion s2 s3)))
  (ensures (loc_aux_syntactically_includes s1 s2 /\ loc_aux_syntactically_includes s1 s3))
= loc_aux_syntactically_includes_trans s1 (LocUnion s2 s3) s2;
  loc_aux_syntactically_includes_trans s1 (LocUnion s2 s3) s3

(* Necessary to handle `exists` *)

let buffer_includes_pointer
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= exists (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) /\ gpointer_of_buffer_cell b i `includes` p

let rec loc_aux_includes_pointer
  (s: loc_aux)
  (#t: typ)
  (p: pointer t)
: GTot Type0
= match s with
  | LocPointer p' -> 
    p' `includes` p
  | LocBuffer b ->
    buffer_includes_pointer b p
  | LocUnion s1 s2 -> loc_aux_includes_pointer s1 p \/ loc_aux_includes_pointer s2 p

let rec loc_aux_includes_pointer_refl_pointer
  (s: loc_aux)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (
    loc_aux_syntactically_includes s (LocPointer p)
  ))
  (ensures (loc_aux_includes_pointer s p))
  (decreases s)
= match s with
  | LocUnion s1 s2 ->
    Classical.or_elim
      #(loc_aux_syntactically_includes s1 (LocPointer p))
      #(loc_aux_syntactically_includes s2 (LocPointer p))
      #(fun _ -> loc_aux_includes_pointer s p)
      (fun _ -> loc_aux_includes_pointer_refl_pointer s1 p)
      (fun _ -> loc_aux_includes_pointer_refl_pointer s2 p)
  | _ -> ()

let rec loc_aux_includes_pointer_refl_buffer
  (s: loc_aux)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (
    UInt32.v i < UInt32.v (buffer_length b) /\
    loc_aux_syntactically_includes s (LocBuffer b)
  ))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_aux_includes_pointer s (gpointer_of_buffer_cell b i)))
  (decreases s)
= match s with
  | LocUnion s1 s2 ->
    Classical.or_elim
      #(loc_aux_syntactically_includes s1 (LocBuffer b))
      #(loc_aux_syntactically_includes s2 (LocBuffer b))
      #(fun _ -> loc_aux_includes_pointer s (gpointer_of_buffer_cell b i))
      (fun _ -> loc_aux_includes_pointer_refl_buffer s1 b i)
      (fun _ -> loc_aux_includes_pointer_refl_buffer s2 b i)
  | _ -> ()

let rec loc_aux_includes_pointer_trans
  (s: loc_aux)
  (#t1 #t2: typ)
  (p1: pointer t1)
  (p2: pointer t2)
: Lemma
  (requires (loc_aux_includes_pointer s p1 /\ p1 `includes` p2))
  (ensures (loc_aux_includes_pointer s p2))
= match s with
  | LocUnion s1 s2 ->
    Classical.or_elim
      #(loc_aux_includes_pointer s1 p1)
      #(loc_aux_includes_pointer s2 p1)
      #(fun _ -> loc_aux_includes_pointer s p2)
      (fun _ -> loc_aux_includes_pointer_trans s1 p1 p2)
      (fun _ -> loc_aux_includes_pointer_trans s2 p1 p2)
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

let rec loc_aux_includes
  (s: loc_aux)
  (s2: loc_aux)
: GTot Type0
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    loc_aux_includes s s2l /\
    loc_aux_includes s s2r
  | LocPointer p ->
    loc_aux_includes_pointer s p
  | LocBuffer b ->
    loc_aux_includes_buffer s b

let rec loc_aux_includes_refl
  (s: loc_aux)
  (s2: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s s2))
  (ensures (loc_aux_includes s s2))
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    loc_aux_syntactically_includes_union_r s s2l s2r;
    loc_aux_includes_refl s s2l;
    loc_aux_includes_refl s s2r
  | LocPointer p ->
    loc_aux_includes_pointer_refl_pointer s p
  | LocBuffer b ->
    Classical.forall_intro (Classical.move_requires (loc_aux_includes_pointer_refl_buffer s b))

let rec loc_aux_includes_refl'
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
= loc_aux_includes_refl s s

(* FIXME: WHY WHY WHY do I need to duplicate the lemma? Because Classical.forall_intro DOES NOT UNIFY/typecheck if there is a pattern *)
let rec loc_aux_includes_refl''
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
  [SMTPat (loc_aux_includes s s)]
= loc_aux_includes_refl' s

let rec loc_aux_includes_union_l_r
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s s') s)
= loc_aux_includes_refl (LocUnion s s') s

let rec loc_aux_includes_union_l_l
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s' s) s)
= loc_aux_includes_refl (LocUnion s' s) s

let rec loc_aux_includes_loc_aux_includes_pointer
  (s1: loc_aux)
  (s2: loc_aux)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_pointer s2 p))
  (ensures (loc_aux_includes_pointer s1 p))
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    Classical.or_elim
      #(loc_aux_includes_pointer s2l p)
      #(loc_aux_includes_pointer s2r p)
      #(fun _ -> loc_aux_includes_pointer s1 p)
      (fun _ -> loc_aux_includes_loc_aux_includes_pointer s1 s2l p)
      (fun _ -> loc_aux_includes_loc_aux_includes_pointer s1 s2r p)
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

let rec loc_aux_includes_trans
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
  (decreases s3)
= match s3 with
  | LocUnion s3l s3r ->
    loc_aux_includes_trans s1 s2 s3l;
    loc_aux_includes_trans s1 s2 s3r
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

let rec loc_aux_includes_trans'
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  ((loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3) ==> loc_aux_includes s1 s3)
= Classical.move_requires (loc_aux_includes_trans s1 s2) s3

let addrs_of_loc_weak
  (l: loc)
  (r: HH.rid)
: GTot (Set.set nat)
= if Set.mem r (Ghost.reveal (Loc?.whole_regions l))
  then Set.complement Set.empty
  else if Set.mem r (Ghost.reveal (Loc?.addr_regions l))
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_weak_loc_union
  (l1 l2: loc)
  (r: HH.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc
  (l: loc)
  (r: HH.rid)
: GTot (Set.set nat)
= Set.union
    (addrs_of_loc_weak l r)
    (if Set.mem r (Ghost.reveal (Loc?.aux_regions l)) then Loc?.aux_addrs l r else Set.empty)

let addrs_of_loc_union
  (l1 l2: loc)
  (r: HH.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc (loc_union l1 l2) r) (Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes s1 s2 =
  let whole_regions1 = Ghost.reveal (Loc?.whole_regions s1) in
  let whole_regions2 = Ghost.reveal (Loc?.whole_regions s2) in
  let addr_regions1 = Ghost.reveal (Loc?.addr_regions s1) in
  let addr_regions2 = Ghost.reveal (Loc?.addr_regions s2) in (
    Set.subset whole_regions2 whole_regions1 /\
    Set.subset addr_regions2 (Set.union whole_regions1 addr_regions1) /\
    (
      forall (r: HH.rid) .
      (Set.mem r addr_regions2 /\ (~ (Set.mem r whole_regions1))) ==>
      Set.subset (Loc?.addrs s2 r) (Loc?.addrs s1 r)
    ) /\ (
      forall (r: HH.rid) .
      Set.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HH.rid) .
      Set.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      forall (r: HH.rid) (n: nat) .
      (Set.mem r (Ghost.reveal (Loc?.aux_regions s2)) /\ Set.mem n (Loc?.aux_addrs s2 r)) ==>
      (
        Set.mem n (addrs_of_loc_weak s1 r) \/ (
        Set.mem r (Ghost.reveal (Loc?.aux_regions s1)) /\
        Set.mem n (Loc?.aux_addrs s1 r) /\
        loc_aux_includes (Loc?.aux s1 r n) (Loc?.aux s2 r n)
  ))))

let loc_includes_refl s =
  let pre
    (r: HH.rid)
    (n: nat)
  : GTot Type0
  = Set.mem r (Ghost.reveal (Loc?.aux_regions s)) /\
    Set.mem n (Loc?.aux_addrs s r)
  in
  let post
    (r: HH.rid)
    (n: nat)
  : GTot Type0
  = pre r n /\
    loc_aux_includes (Loc?.aux s r n) (Loc?.aux s r n)
  in
  let f
    (r: HH.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = loc_aux_includes_refl (Loc?.aux s r n) (Loc?.aux s r n)
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r))

let loc_includes_trans s1 s2 s3 =
  Classical.forall_intro_3 loc_aux_includes_trans'

let loc_includes_union_r s s1 s2 = ()

let loc_includes_union_l s1 s2 s =
  let u12 = loc_union s1 s2 in
  Classical.forall_intro loc_aux_includes_refl';
  Classical.forall_intro_2 loc_aux_includes_union_l_l;    
  Classical.forall_intro_2 loc_aux_includes_union_l_r;
  Classical.or_elim
    #(loc_includes s1 s)
    #(loc_includes s2 s)
    #(fun _ -> loc_includes (loc_union s1 s2) s)
    (fun _ -> loc_includes_trans u12 s1 s)
    (fun _ -> loc_includes_trans u12 s2 s)

#reset-options "--z3rlimit 32"

let loc_includes_none s = ()

let loc_includes_pointer_pointer #t1 #t2 p1 p2 = ()

let loc_includes_gsingleton_buffer_of_pointer l #t p =
  loc_includes_trans l (loc_pointer p) (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_includes_gbuffer_of_array_pointer l #len #t p =
  loc_includes_trans l (loc_pointer p) (loc_buffer (gbuffer_of_array_pointer p))

let loc_includes_gpointer_of_array_cell l #t b i =
  loc_includes_trans l (loc_buffer b) (loc_pointer (gpointer_of_buffer_cell b i))

#reset-options "--z3rlimit 64"

let loc_includes_gsub_buffer_r l #t b i len =
  if len = 0ul
  then
    loc_includes_none l
  else begin
    let g = gsub_buffer b i len in
    let f () : Lemma
      (loc_aux_includes (LocBuffer b) (LocBuffer g))
    = let pre
        (j: UInt32.t)
      : GTot Type0
      = UInt32.v j < UInt32.v len
      in
      let post
        (j: UInt32.t)
      : GTot Type0
      = pre j /\
        loc_aux_includes_pointer (LocBuffer b) (gpointer_of_buffer_cell g j)
      in
      let k
        (j: UInt32.t)
      : Lemma
        (requires (pre j))
        (ensures (post j))
      = gpointer_of_buffer_cell_gsub_buffer b i len j
      in
      Classical.forall_intro (Classical.move_requires k)
    in
    f ();
    loc_includes_trans l (loc_buffer b) (loc_buffer g)
  end

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  let g1 = gsub_buffer b i1 len1 in
  let g2 = gsub_buffer b i2 len2 in
  if len2 = 0ul
  then
    loc_includes_none (loc_buffer g1)
  else begin
    let pre (j: UInt32.t) : GTot Type0 =
      UInt32.v j < UInt32.v (buffer_length g2)
    in
    let post (j: UInt32.t) : GTot Type0 =
      pre j /\
      buffer_includes_pointer g1 (gpointer_of_buffer_cell g2 j)
    in
    let f
      (j: UInt32.t)
    : Lemma
      (requires (pre j))
      (ensures (post j))
    = assert (gpointer_of_buffer_cell g1 (FStar.UInt32.add (FStar.UInt32.sub i2 i1) j) `includes` gpointer_of_buffer_cell g2 j)
    in
    Classical.forall_intro (Classical.move_requires f);
    assert (loc_aux_includes (LocBuffer g1) (LocBuffer g2))
  end

let loc_includes_addresses_pointer #t r s p = ()

let loc_includes_addresses_buffer #t r s p = ()

let loc_includes_region_pointer #t s p = ()

let loc_includes_region_buffer #t s b = ()

let loc_includes_region_addresses s r a = ()

let loc_includes_region_region s1 s2 = ()

let loc_includes_region_union_l l s1 s2 = ()


(* Disjointness of two memory locations *)

let disjoint_buffer_vs_pointer
  (#t1 #t2: typ)
  (b: buffer t1)
  (p: pointer t2)
: GTot Type0
= forall (i: UInt32.t) . UInt32.v i < UInt32.v (buffer_length b) ==> disjoint (gpointer_of_buffer_cell b i) p

let rec loc_aux_disjoint_pointer
  (l: loc_aux)
  (#t: typ)
  (p: pointer t)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_pointer ll p /\ loc_aux_disjoint_pointer lr p
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

let rec loc_aux_disjoint
  (l1 l2: loc_aux)
: GTot Type0
  (decreases l2)
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint l1 ll /\ loc_aux_disjoint l1 lr
  | LocPointer p ->
    loc_aux_disjoint_pointer l1 p
  | LocBuffer b ->
    loc_aux_disjoint_buffer l1 b

let rec loc_aux_disjoint_union_l
  (ll1 lr1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint (LocUnion ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
  (decreases l2)
= match l2 with
  | LocUnion ll2 lr2 ->
    loc_aux_disjoint_union_l ll1 lr1 ll2;
    loc_aux_disjoint_union_l ll1 lr1 lr2
  | _ -> ()

let loc_aux_disjoint_union_r
  (l1 ll2 lr2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 (LocUnion ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let rec loc_aux_size
  (l: loc_aux)
: GTot nat
= match l with
  | LocUnion l1 l2 ->
    let n1 = loc_aux_size l1 in
    let n2 = loc_aux_size l2 in
    1 + (if n1 > n2 then n1 else n2)
  | _ -> 0

let rec loc_aux_disjoint_sym
  (l1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
  (decreases (loc_aux_size l1 + loc_aux_size l2))
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint_union_r l1 ll lr;
    loc_aux_disjoint_sym l1 ll;
    loc_aux_disjoint_sym l1 lr;
    loc_aux_disjoint_union_l ll lr l1
  | _ ->
    begin match l1 with
    | LocUnion ll lr ->
      loc_aux_disjoint_union_l ll lr l2;
      loc_aux_disjoint_sym ll l2;
      loc_aux_disjoint_sym lr l2;
      loc_aux_disjoint_union_r l2 ll lr
    | _ ->
      begin match (l1, l2) with
      | (LocPointer p1, LocPointer p2) -> disjoint_sym' p1 p2
      | (LocPointer p1, LocBuffer b2) -> loc_aux_disjoint_pointer_buffer_sym b2 p1
      | (LocBuffer b1, LocPointer p2) -> loc_aux_disjoint_pointer_buffer_sym b1 p2
      | (LocBuffer b1, LocBuffer b2) -> loc_aux_disjoint_buffer_sym b1 b2
      end
    end

(* Same problem with decreases here *)

let loc_aux_disjoint_sym'
  (l1 l2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1)
= loc_aux_disjoint_sym l1 l2

let regions_of_loc
  (s: loc)
: GTot (Set.set HH.rid)
= Set.union
    (Ghost.reveal (Loc?.whole_regions s))
    (Set.union
      (Ghost.reveal (Loc?.addr_regions s))
      (Ghost.reveal (Loc?.aux_regions s))
    )

let regions_of_loc_loc_union
  (s1 s2: loc)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (s1 s2: loc)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint'
  (l1 l2: loc)
: GTot Type0
= Set.subset (Set.intersect (regions_of_loc l1) (Ghost.reveal (Loc?.whole_regions l2))) Set.empty /\
  Set.subset (Set.intersect (regions_of_loc l2) (Ghost.reveal (Loc?.whole_regions l1))) Set.empty /\
  (forall (r: HH.rid) .
      Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
      Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty
  ) /\
  (forall (r: HH.rid) (n: nat) .
    (Set.mem r (Ghost.reveal (Loc?.aux_regions l1)) /\ Set.mem n (Loc?.aux_addrs l1 r) /\
     Set.mem r (Ghost.reveal (Loc?.aux_regions l2)) /\ Set.mem n (Loc?.aux_addrs l2 r)) ==>
    loc_aux_disjoint (Loc?.aux l1 r n) (Loc?.aux l2 r n)
  )

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym l1 l2 =
  Classical.forall_intro_2 loc_aux_disjoint_sym'

let loc_disjoint_none_r s = ()

let loc_disjoint_union_r s s1 s2 = ()

let loc_disjoint_root #value1 #value2 p1 p2 =
  disjoint_root p1 p2

let loc_disjoint_gfield #l p fd1 fd2 = ()

let loc_disjoint_gcell #length #value p i1 i2 = ()

let rec loc_aux_disjoint_pointer_includes
  (l: loc_aux)
  (#t1: typ)
  (p1: pointer t1)
  (#t2: typ)
  (p2: pointer t2)
: Lemma
  (requires (loc_aux_disjoint_pointer l p1 /\ p1 `includes` p2))
  (ensures (loc_aux_disjoint_pointer l p2))
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_pointer_includes ll p1 p2;
    loc_aux_disjoint_pointer_includes lr p1 p2
  | _ -> ()

let rec loc_aux_disjoint_loc_aux_includes_pointer
  (l1 l2: loc_aux)
  (#t3: typ)
  (p3: pointer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_pointer l2 p3))
  (ensures (loc_aux_disjoint_pointer l1 p3))
  (decreases l2)
= match l2 with
  | LocUnion ll2 lr2 ->
    Classical.or_elim
      #(loc_aux_includes_pointer ll2 p3)
      #(loc_aux_includes_pointer lr2 p3)
      #(fun _ -> loc_aux_disjoint_pointer l1 p3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_pointer l1 ll2 p3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_pointer l1 lr2 p3)
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

let rec loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: loc_aux)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
  (decreases l3)
= match l3 with
  | LocUnion ll3 lr3 ->
    loc_aux_disjoint_loc_aux_includes l1 l2 ll3;
    loc_aux_disjoint_loc_aux_includes l1 l2 lr3
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

let loc_disjoint_includes p1 p2 p1' p2' =
  regions_of_loc_monotonic p1 p1';
  regions_of_loc_monotonic p2 p2';
  let pre
    (r: HH.rid)
    (n: nat)
  : GTot Type0
  = Set.mem r (Ghost.reveal (Loc?.aux_regions p1')) /\ Set.mem n (Loc?.aux_addrs p1' r) /\
    Set.mem r (Ghost.reveal (Loc?.aux_regions p2')) /\ Set.mem n (Loc?.aux_addrs p2' r)
  in
  let post
    (r: HH.rid)
    (n: nat)
  : GTot Type0
  = pre r n /\
    loc_aux_disjoint (Loc?.aux p1' r n) (Loc?.aux p2' r n)
  in
  let f
    (r: HH.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = let l1 = Loc?.aux p1 r n in
    let l2 = Loc?.aux p2 r n in
    let l1' = Loc?.aux p1' r n in
    let l2' = Loc?.aux p2' r n in
    loc_aux_disjoint_loc_aux_includes l1 l2 l2';
    loc_aux_disjoint_sym l1 l2';
    loc_aux_disjoint_loc_aux_includes l2' l1 l1';
    loc_aux_disjoint_sym l2' l1'
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r));
  assert (forall r n . pre r n ==> post r n)

let live_unused_in_disjoint_strong
  (#value1: typ)
  (#value2: typ)
  (h: HS.mem)
  (p1: pointer value1)
  (p2: pointer value2)
: Lemma
  (requires (live h p1 /\ unused_in p2 h))
  (ensures (frameOf p1 <> frameOf p2 \/ as_addr p1 <> as_addr p2))
= ()

let live_unused_in_disjoint #value1 #value2 h p1 p2 =
  live_unused_in_disjoint_strong h p1 p2;
  disjoint_root p1 p2

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_gpointer_of_buffer_cell #t b i1 i2 = ()

let loc_disjoint_addresses r1 r2 n1 n2 = ()

let loc_disjoint_pointer_addresses #t p r n = ()

let loc_disjoint_regions rs1 rs2 = ()

(** The modifies clause proper *)

let modifies'
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= HH.modifies_just (regions_of_loc s) h1.HS.h h2.HS.h /\ (
    forall r . (
      HS.live_region h1 r /\
      Set.mem r (regions_of_loc s) /\
      (~ (Set.mem r (Ghost.reveal (Loc?.whole_regions s))))
    ) ==> (
      HS.live_region h2 r /\
      HH.modifies_rref r (addrs_of_loc s r) h1.HS.h h2.HS.h
    )
  ) /\ (
    forall t (p: pointer t) . (
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s)) /\
      Set.mem (as_addr p) (Loc?.aux_addrs s (frameOf p)) /\
      (~ (Set.mem (as_addr p) (addrs_of_loc_weak s (frameOf p)))) /\
      loc_aux_disjoint_pointer (Loc?.aux s (frameOf p) (as_addr p)) p
    ) ==>
    equal_values h1 p h2 p
  )

let modifies = modifies'

let modifies_loc_regions_intro rs h1 h2 = ()

let modifies_loc_addresses_intro_weak
  (r: HH.rid)
  (s: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions (Set.singleton r)) l) h1 h2 /\
    HH.modifies_rref r s h1.HS.h h2.HS.h /\
    HS.live_region h1 r /\
    loc_disjoint l (loc_regions (Set.singleton r))
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= ()

let modifies_pointer_elim s h1 h2 #a' p' =
  loc_disjoint_sym (loc_pointer p') s;
  let r = frameOf p' in
  let a = as_addr p' in
  if Set.mem r (Ghost.reveal (Loc?.aux_regions s)) &&
     Set.mem a (Loc?.aux_addrs s r)
  then
    ()
  else
    let r = greference_of p' in
    assert (HS.sel h1 r == HS.sel h2 r)

#reset-options "--z3rlimit 256"

let modifies_buffer_elim #t1 b p h h' =
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

let modifies_reference_elim #t b p h h' =
  loc_disjoint_sym (loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))) p

let modifies_refl s h = ()

#reset-options "--z3rlimit 512"

let modifies_loc_includes s1 h h' s2 =
  assert (
    forall rs r . (
      HH.modifies_just rs h.HS.h h'.HS.h /\
      HS.live_region h r /\
      (~ (Set.mem r rs))
    ) ==>
    HH.modifies_rref r Set.empty h.HS.h h'.HS.h
  );
  aux_addrs_nonempty s1;
  aux_addrs_nonempty s2;
  let h1 = h in
  let h2 = h' in
  assert (HH.modifies_just (regions_of_loc s1) h1.HS.h h2.HS.h);
  assert (
    forall r . (
      HS.live_region h1 r /\
      Set.mem r (regions_of_loc s1) /\
      (~ (Set.mem r (Ghost.reveal (Loc?.whole_regions s1))))
    ) ==> (
      HS.live_region h2 r /\
      HH.modifies_rref r (addrs_of_loc s1 r) h1.HS.h h2.HS.h
  ));
  let f
    (t: typ)
    (p: pointer t)
  : Lemma
    (requires (
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s1)) /\
      Set.mem (as_addr p) (Loc?.aux_addrs s1 (frameOf p)) /\
      (~ (Set.mem (as_addr p) (addrs_of_loc_weak s1 (frameOf p)))) /\
      loc_aux_disjoint_pointer (Loc?.aux s1 (frameOf p) (as_addr p)) p /\
      live h1 p
    ))
    (ensures (
      equal_values h1 p h2 p
    ))
  = assert (~ (Set.mem (as_addr p) (addrs_of_loc_weak s2 (frameOf p))));
    if
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s2)) &&
      Set.mem (as_addr p) (Loc?.aux_addrs s2 (frameOf p))
    then begin
      let l1 = Loc?.aux s1 (frameOf p) (as_addr p) in
      let l2 = Loc?.aux s2 (frameOf p) (as_addr p) in
      loc_aux_disjoint_sym l1 (LocPointer p);
      loc_aux_disjoint_loc_aux_includes (LocPointer p) l1 l2;
      loc_aux_disjoint_sym (LocPointer p) l2
    end else
      ()
  in
  Classical.forall_intro_2 (fun t -> Classical.move_requires (f t))

let modifies_only_live_regions_weak
  (rs: Set.set HH.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= ()

let modifies_regions_elim rs h h' = ()

let modifies_addresses_elim r a l h h' =
  assert (Set.equal (addrs_of_loc (loc_addresses r a) r) a);
  assert (Set.equal (addrs_of_loc l r) Set.empty)

let modifies_trans'
  (s: loc)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= ()

let modifies_trans s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

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
  p

// TODO: move to HyperStack?
let domain_upd (#a:Type) (h:HS.mem) (x:HS.reference a{HS.live_region h x.HS.id}) (v:a) : Lemma
  (requires True)
  (ensures  (Map.domain h.HS.h == Map.domain (HS.upd h x v).HS.h))
  = let m = h.HS.h in
    let m' = Map.upd m x.HS.id (Heap.upd (Map.sel m x.HS.id) (HH.as_ref x.HS.ref) v) in
    Set.lemma_equal_intro (Map.domain m) (Map.domain m')

let ecreate
  (t:typ)
  (r:HH.rid)
  (s: option (type_of_typ t))
= let h0 = HST.get () in
  let s = match s with
  | Some s -> ovalue_of_value t s
  | _ -> none_ovalue t
  in
  let content: HS.reference pointer_ref_contents =
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
  let f
    (t: typ)
    (p: pointer t)
  : Lemma
    (requires (
      frameOf p == frameOf b /\
      as_addr p == as_addr b /\
      live h0 p /\
      disjoint b p
    ))
    (ensures (
      equal_values h0 p h1 p
    ))
  = let grefp = greference_of p in
    HS.lemma_sel_same_addr h0 r grefp;
    HS.lemma_sel_same_addr h1 r grefp;
    path_sel_upd_other' (Pointer?.p b) c0 z (Pointer?.p p)
  in
  Classical.forall_intro_2 (fun t -> Classical.move_requires (f t))

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

let no_upd_fresh h0 h1 = ()

(* TODO: move to FStar.Monotonic.HyperStack *)
let hs_modifies_just_fresh_frame_popped 
  (h0 h1: HS.mem)
  (s: Set.set HH.rid)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    HH.modifies_just s h1.HS.h h2.HS.h /\
    h2.HS.tip == h1.HS.tip /\
    HS.popped h2 h3
  ))
  (ensures (
    HH.modifies_just (Set.intersect s (Set.complement (HH.mod_set (Set.singleton h1.HS.tip)))) h0.HS.h h3.HS.h /\
    h3.HS.tip == h0.HS.tip
  ))
= ()

let hs_modifies_rref_fresh_frame_popped 
  (h0 h1: HS.mem)
  (h2 h3: HS.mem)
  (r: HH.rid)
  (a: Set.set nat)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    (~ (Set.mem r (HH.mod_set (Set.singleton h1.HS.tip)))) /\
    HS.live_region h0 r /\
    Set.subset (Map.domain h1.HS.h) (Map.domain h2.HS.h) /\
    HH.modifies_rref r a h1.HS.h h2.HS.h /\
    h2.HS.tip == h1.HS.tip /\
    HS.popped h2 h3
  ))
  (ensures (
    HS.live_region h3 r /\
    HH.modifies_rref r a h0.HS.h h3.HS.h
  ))
= ()

let modifies_fresh_frame_popped_weak
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_regions (HH.mod_set (Set.singleton h1.HS.tip))) s) h1 h2 /\
    h2.HS.tip == h1.HS.tip /\
    HS.popped h2 h3 /\
    loc_disjoint (loc_regions (HH.mod_set (Set.singleton h1.HS.tip))) s
  ))
  (ensures (
    modifies s h0 h3 /\
    h3.HS.tip == h0.HS.tip
  ))
= let rs = regions_of_loc s in
  let mask = HH.mod_set (Set.singleton h1.HS.tip) in
  let ru = Set.union mask rs in
  assert (Set.equal (Set.intersect ru (Set.complement mask)) rs);
  hs_modifies_just_fresh_frame_popped h0 h1 ru h2 h3;
  let f
    (r: HH.rid)
  : Lemma
    (requires (
      HS.live_region h0 r /\
      Set.mem r (regions_of_loc s) /\
      (~ (Set.mem r (Ghost.reveal (Loc?.whole_regions s))))
    ))
    (ensures (
      HS.live_region h3 r /\
      HH.modifies_rref r (addrs_of_loc s r) h0.HS.h h3.HS.h
    ))
  = hs_modifies_rref_fresh_frame_popped h0 h1 h2 h3 r (addrs_of_loc s r)
  in
  Classical.forall_intro (Classical.move_requires f);
  let u = loc_union (loc_regions mask) s in
  let g
    (t: typ)
    (p: pointer t)
  : Lemma
    (requires (
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s)) /\
      Set.mem (as_addr p) (Loc?.aux_addrs s (frameOf p)) /\
      (~ (Set.mem (as_addr p) (addrs_of_loc_weak s (frameOf p)))) /\
      loc_aux_disjoint_pointer (Loc?.aux s (frameOf p) (as_addr p)) p /\
      live h0 p
    ))
    (ensures (
      equal_values h0 p h3 p
    ))
  = let r = frameOf p in
    let a = as_addr p in
    assert (Set.mem a (Loc?.aux_addrs u r));
    assert (Set.equal (addrs_of_loc_weak u r) (addrs_of_loc_weak s r));
    assert (Loc?.aux u r a == Loc?.aux s r a)
  in
  Classical.forall_intro_2 (fun t -> Classical.move_requires (g t))

let no_upd_popped #t h0 h1 b =
  let g = greference_of b in
  assert (HS.sel h1 g == HS.sel h0 g)

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
: GTot loc
= let (Loc whole_regions addr_regions addrs aux_regions aux_addrs aux) = l in
  Loc
    (Ghost.hide (Set.intersect (Ghost.reveal whole_regions) rs))
    (Ghost.hide (Set.intersect (Ghost.reveal addr_regions) rs))
    (fun r -> addrs r)
    (Ghost.hide (Set.intersect (Ghost.reveal aux_regions) rs))
    (fun r -> aux_addrs r)
    (fun r n -> aux r n)

let regions_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
  (r: HH.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
  (r: HH.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else Set.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else Set.empty))

let loc_includes_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl'

let loc_includes_loc_union_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
: Lemma
  (loc_includes (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= Classical.forall_intro loc_aux_includes_refl'

let loc_includes_loc_regions_restrict_to_regions
  (l: loc)
  (rs: Set.set HH.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl'

let modifies_fresh_frame_popped h0 h1 s h2 h3 =
  (* NOTE: I could automate the proof, but at least this way here
     it is replayable and also readable. *)
  let rs = HH.mod_set (Set.singleton h1.HS.tip) in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h1 h2 (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_fresh_frame_popped_weak h0 h1 s_c_rs h2 h3;
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h0 h3 s_c_rs

let modifies_only_live_regions rs l h h' =
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h h' (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let modifies_loc_addresses_intro r a l h1 h2 =
  let rs = Set.singleton r in
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  if StrongExcludedMiddle.strong_excluded_middle (HS.live_region h1 r)
  then begin
    loc_includes_loc_regions_restrict_to_regions s rs;
    loc_includes_union_l lrs s_c_rs s_rs;
    loc_includes_refl s_c_rs;
    loc_includes_union_l lrs s_c_rs s_c_rs;
    loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
    loc_includes_loc_union_restrict_to_regions s rs;
    loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
    modifies_loc_includes (loc_union lrs s_c_rs) h1 h2 (loc_union lrs s);
    loc_includes_loc_regions_restrict_to_regions s c_rs;
    loc_disjoint_regions rs c_rs;
    loc_includes_refl lrs;
    loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
    modifies_loc_addresses_intro_weak r a s_c_rs h1 h2;
    loc_includes_restrict_to_regions s c_rs;
    loc_includes_union_l (loc_addresses r a) l s_c_rs;
    loc_includes_refl (loc_addresses r a);
    loc_includes_union_l (loc_addresses r a) l (loc_addresses r a);
    loc_includes_union_r (loc_union (loc_addresses r a) l) (loc_addresses r a) s_c_rs;
    modifies_loc_includes (loc_union (loc_addresses r a) l) h1 h2 (loc_union (loc_addresses r a) s_c_rs)
  end else begin
    modifies_only_live_regions rs l h1 h2;
    loc_includes_refl l;
    loc_includes_union_l (loc_addresses r a) l l;
    modifies_loc_includes (loc_union (loc_addresses r a) l) h1 h2 l
  end


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
