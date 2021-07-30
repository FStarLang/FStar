module Steel.C.StructLiteral

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Typedef
open Steel.C.Ref // for refine
open Steel.C.Connection
open FStar.List.Tot

let struct_fields =
  struct_fields:list (string * typedef){Cons? struct_fields}

[@@iter_unfold]
let has_field_bool (fields: struct_fields) (field: string): bool =
  field `mem` map fst fields

[@@iter_unfold]
let has_field (fields: struct_fields) (field: string): prop =
  has_field_bool fields field == true

let field_of (fields: struct_fields) =
  refine string (has_field fields)

[@@iter_unfold]
let mk_field_of (fields: struct_fields) (field: string)
: Pure (field_of fields)
    (requires normalize_term (has_field_bool fields field) == true)
    (ensures fun field' -> field' == field)
= field

[@@iter_unfold]
let get_field (fields: struct_fields) (field: field_of fields): typedef =
  assoc_mem field fields;
  match assoc field fields with
  | Some v -> v
  | None -> false_elim ()

/// A view type for structs

[@@iter_unfold]
let struct_views (fields: struct_fields) (field: field_of fields)
: sel_view ((get_field fields field).pcm) ((get_field fields field).view_type) false
= (get_field fields field).view

val struct (tag: string) (fields: struct_fields): Type0

let rec list_fn (dom: list Type) (cod: Type) = match dom with
  | [] -> cod
  | d :: dom -> d -> list_fn dom cod

let rec list_fn_map #dom (f: 'a -> 'b) (g: dom `list_fn` 'a): dom `list_fn` 'b = match dom with 
  | [] -> f g <: [] `list_fn` 'b
  | d :: dom' ->
    let g: d -> dom' `list_fn` 'a = g in
    fun (x:d) -> list_fn_map f (g x) <: dom' `list_fn` 'b

let struct_field_view_type ((_, td): string * typedef): Type = td.view_type

let mk_struct_ty_dom (tag: string) (fields: list (string * typedef)): list Type =
  map struct_field_view_type fields

let mk_struct_ty (tag: string) (fields: struct_fields): Type =
  mk_struct_ty_dom tag fields `list_fn` struct tag fields

/// A struct literal
val mk_struct (tag: string) (fields: struct_fields): mk_struct_ty tag fields

/// Reading a struct field
val struct_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields) (field: field_of fields)
: (get_field fields field).view_type

/// Writing a struct field
val struct_put
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (get_field fields field).view_type)
: struct tag fields

/// For a fixed field name, struct_get and struct_put form a lens

val struct_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v: (get_field fields field).view_type)
: Lemma (struct_put x field v `struct_get` field == v)
  [SMTPat (struct_put x field v `struct_get` field)]

val struct_put_get
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
: Lemma (struct_put x field (x `struct_get` field) == x)
  [SMTPat (struct_put x field (x `struct_get` field))]

val struct_put_put
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v w: (get_field fields field).view_type)
: Lemma (struct_put (struct_put x field v) field w == struct_put x field w)
  [SMTPat (struct_put (struct_put x field v) field w)]

/// struct_get/struct_put pairs for different fields don't interfere with each other

val struct_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (get_field fields field1).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_put x field1 v `struct_get` field2 == x `struct_get` field2)
  [SMTPat (struct_put x field1 v `struct_get` field2)]
  
val struct_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct tag fields)
  (field1: field_of fields)
  (v: (get_field fields field1).view_type)
  (field2: field_of fields)
  (w: (get_field fields field2).view_type)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_put (struct_put x field1 v) field2 w ==
      struct_put (struct_put x field2 w) field1 v)

/// Similarly, a PCM for structs

[@@iter_unfold]
let struct_carriers (fields: struct_fields) (field: field_of fields) =
  (get_field fields field).carrier

[@@iter_unfold]
let struct_pcms (tag: string) (fields: struct_fields) (field: field_of fields)
: pcm (struct_carriers fields field)
= (get_field fields field).pcm

val struct_pcm_carrier (tag: string) (fields: struct_fields): Type0
val struct_pcm (tag: string) (fields: struct_fields): pcm (struct_pcm_carrier tag fields)

let struct_field_carrier ((_, td): string * typedef): Type = td.carrier

let mk_struct_pcm_ty_dom (tag: string) (fields: list (string * typedef)): list Type =
  map struct_field_carrier fields

let mk_struct_pcm_ty (tag: string) (fields: struct_fields): Type =
  mk_struct_pcm_ty_dom tag fields `list_fn` struct_pcm_carrier tag fields

/// A struct PCM carrier literal
val mk_struct_pcm (tag: string) (fields: struct_fields): mk_struct_pcm_ty tag fields

/// Reading a pcm_struct_carrier field
val struct_pcm_get
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields) (field: field_of fields)
: (get_field fields field).carrier

/// Writing a struct_pcm_carrier field
val struct_pcm_put
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (get_field fields field).carrier)
: struct_pcm_carrier tag fields

/// For a fixed field name, struct_pcm_get and struct_pcm_put form a lens

val struct_pcm_get_put 
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (get_field fields field).carrier)
: Lemma (struct_pcm_put x field v `struct_pcm_get` field == v)
  [SMTPat (struct_pcm_put x field v `struct_pcm_get` field)]

val struct_pcm_put_get
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
: Lemma (struct_pcm_put x field (x `struct_pcm_get` field) == x)
  [SMTPat (struct_pcm_put x field (x `struct_pcm_get` field))]

val struct_pcm_put_put
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v w: (get_field fields field).carrier)
: Lemma (struct_pcm_put (struct_pcm_put x field v) field w == struct_pcm_put x field w)
  [SMTPat (struct_pcm_put (struct_pcm_put x field v) field w)]

/// struct_pcm_get/struct_pcm_put pairs for different fields don't interfere with each other

val struct_pcm_get_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (get_field fields field1).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_pcm_put x field1 v `struct_pcm_get` field2 == x `struct_pcm_get` field2)
  [SMTPat (struct_pcm_put x field1 v `struct_pcm_get` field2)]
  
val struct_pcm_put_put_ne
  (#tag: string) (#fields: struct_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (v: (get_field fields field1).carrier)
  (field2: field_of fields)
  (w: (get_field fields field2).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_pcm_put (struct_pcm_put x field1 v) field2 w ==
      struct_pcm_put (struct_pcm_put x field2 w) field1 v)

/// View a struct_pcm_carrier as a struct
val struct_view (tag: string) (fields: struct_fields)
: sel_view (struct_pcm tag fields) (struct tag fields) false

// /// View a struct_pcm_carrier as a struct
// val struct_view (tag: string) (fields: struct_fields) (fields': struct_fields{normalize_term (fields' \subset fields) == true})
// : sel_view (struct_pcm tag fields) (struct tag fields') false
// 
// val struct_view (tag: string) (fields: struct_fields) (fields': struct_fields)
// : sel_view (struct_pcm tag fields) (struct tag (normalize (fields - fields'))) false
// 
// struct_view_convert #opened
//   (v: struct_view tag fields fields'1)
// : SteelGhost (struct_view tag fields fields'2) opened
//     (p `pts_to_view` v)
//     (fun w -> (p `pts_to_view` w))
//     (requires fun _ -> normalize (fields - fields'1 == fields - fields'2))
//     (ensures fun h w h' -> forall field. field in (fields - fields'1) ==>
//        h (p `pts_to_view` v) `struct_get` field == 
//        h' (p `pts_to_view` w) `struct_get` field)
// 
// struct_view_convert
//   (v: struct_view tag fields fields'1)
// : Pure (struct_view tag fields fields'2)
//     (requires normalize (fields - fields'1 == fields - fields'2))
//     (ensures fun w -> True)
//
// val struct_view (tag: string) (fields: struct_fields) (fields': struct_fields) (fields_fields': struct_fields) (heq: squash (fields_fields' == normalize_term (fields - fields')))
// : sel_view (struct_pcm tag fields) (struct tag fields_fields') false

// struct_view tag fields fields' (_ by (T.norm _; T.trefl ()))

/// Typedef for struct from typedefs for its fields

let typedef_struct (tag: string) (fields: struct_fields): typedef = {
  carrier = struct_pcm_carrier tag fields; 
  pcm = struct_pcm tag fields;
  view_type = struct tag fields;
  view = struct_view tag fields;
}

/// Connections for fields of structs

val struct_field
  (tag: string) (fields: struct_fields) (field: field_of fields)
: connection (struct_pcm tag fields) (struct_pcms tag fields field)

/// Explode and recombine

