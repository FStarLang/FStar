module Steel.C.StructLiteral

open Steel.C.Typedef
open Steel.C.Ref // for refine
open FStar.List.Tot

let struct_fields = list (string * typedef)

let has_field (fields: struct_fields) (field: string): prop =
  field `mem` map fst fields == true
  
let field_of (fields: struct_fields) =
  refine string (has_field fields)

let get_field (fields: struct_fields) (field: field_of fields): typedef =
  assoc_mem field fields;
  Some?.v (assoc field fields)

let struct_view_types (fields: struct_fields) (field: field_of fields) =
  (get_field fields field).view_type

/// A view type for structs
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

let mk_struct_ty (tag: string) (fields: list (string * typedef)): Type =
  mk_struct_ty_dom tag fields `list_fn` struct tag fields

/// A struct literal
val mk_struct (tag: string) (fields: list (string * typedef)): mk_struct_ty tag fields

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
