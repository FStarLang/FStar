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

module Pulse2Rust.Rust.Syntax

open FStar.Compiler.Effect

module L = FStar.Compiler.List

let vec_new_fn = "vec_new"
let panic_fn = "panic"

let mk_scalar_typ (name:string) : typ =
  Typ_path [ {path_segment_name = name; path_segment_generic_args = [] } ]

let mk_ref_typ (is_mut:bool) (t:typ) : typ =
  Typ_reference { typ_ref_mut = is_mut; typ_ref_typ = t }

let mk_box_typ (t:typ) : typ =
  Typ_path [
    { path_segment_name = "std"; path_segment_generic_args = [] };
    { path_segment_name = "boxed"; path_segment_generic_args = [] };
    { path_segment_name = "Box"; path_segment_generic_args = [t] };
  ]

let mk_slice_typ (t:typ) : typ = Typ_slice t

let mk_vec_typ (t:typ) : typ =
  Typ_path [
    { path_segment_name = "std"; path_segment_generic_args = [] };
    { path_segment_name = "vec"; path_segment_generic_args = [] };
    { path_segment_name = "Vec"; path_segment_generic_args = [t] };
  ]

let mk_mutex_typ (t:typ) : typ =
  Typ_path [
    { path_segment_name = "std"; path_segment_generic_args = [] };
    { path_segment_name = "sync"; path_segment_generic_args = [] };
    { path_segment_name = "Mutex"; path_segment_generic_args = [t] };
  ]

let mk_option_typ (t:typ) : typ =
  Typ_path [
    { path_segment_name = "std"; path_segment_generic_args = [] };
    { path_segment_name = "option"; path_segment_generic_args = [] };
    { path_segment_name = "Option"; path_segment_generic_args = [t] };
  ]

let mk_array_typ (t:typ) (len:expr) : typ =
  Typ_array { typ_array_elem = t; typ_array_len = len }

let mk_named_typ (path:list string) (s:string) (generic_args:list typ) : typ =
  let path = path |> L.map (fun s -> {
      path_segment_name = s;
      path_segment_generic_args = []
  }) in
  let s = { path_segment_name = s; path_segment_generic_args = generic_args } in
  Typ_path (List.append path [s])

let mk_fn_typ (typ_fn_args:list typ) (typ_fn_ret:typ) : typ =
  Typ_fn { typ_fn_args; typ_fn_ret }

let mk_tuple_typ (l:list typ) : typ = Typ_tuple l

let mk_expr_path_singl s = Expr_path [{ path_segment_name = s; path_segment_generic_args = [] }]
let mk_expr_path l =
  Expr_path (L.map (fun s -> { path_segment_name = s; path_segment_generic_args = [] }) l)

let mk_lit_bool (b:bool) : expr = Expr_lit (Lit_bool b)

let mk_binop (l:expr) (op:binop) (r:expr) : expr =
  Expr_binop { expr_bin_left = l; expr_bin_op = op; expr_bin_right = r }

let mk_block_expr l = Expr_block l

let mk_assign (l r:expr) =
  Expr_assign {
    expr_assignment_l = l;
    expr_assignment_r = r;
  }

let mk_ref_assign (l r:expr) =
  Expr_assign {
    expr_assignment_l = Expr_unary { expr_unary_op = Deref; expr_unary_expr = l };
    expr_assignment_r = r;
  }

let mk_ref_read (l:expr) = Expr_unary { expr_unary_op = Deref; expr_unary_expr = l }

let mk_expr_index (expr_index_base:expr) (expr_index_index:expr) : expr =
  Expr_index { expr_index_base; expr_index_index }

let mk_call (head:expr) (args:list expr) =
  Expr_call { expr_call_fn = head; expr_call_args = args }

let mk_if (expr_if_cond:expr) (expr_if_then:list stmt) (expr_if_else:option expr) : expr =
  Expr_if { expr_if_cond; expr_if_then; expr_if_else }

let mk_while (expr_while_cond:expr) (expr_while_body:list stmt) : expr =
  Expr_while { expr_while_cond; expr_while_body }

let mk_repeat (expr_repeat_elem expr_repeat_len:expr) : expr =
  Expr_repeat { expr_repeat_elem; expr_repeat_len }

let mk_reference_expr (expr_reference_is_mut:bool) (expr_reference_expr:expr) : expr =
  Expr_reference { expr_reference_is_mut; expr_reference_expr }

let mk_pat_ident (path:string) : pat =
  Pat_ident { pat_name = path; by_ref = false; is_mut = true }

let mk_pat_ts (path:list string) (s:string) (pat_ts_elems:list pat) : pat =
  if L.length pat_ts_elems = 0
  then if L.length path = 0
       then Pat_ident { pat_name = s; by_ref = false; is_mut = false }
       else Pat_path (L.map (fun s -> {
              path_segment_name = s;
              path_segment_generic_args = []
            }) (path @ [s]))
  else Pat_tuple_struct {
    pat_ts_path = L.map (fun s -> {
      path_segment_name = s;
      path_segment_generic_args = []
    }) (path @ [s]);
    pat_ts_elems
  }

let mk_pat_struct (pat_struct_path:string) (pats:list (string & pat)) : pat =
  Pat_struct { pat_struct_path;
    pat_struct_fields = L.map (fun (s, p) -> {
      field_pat_name = s;
      field_pat_pat = p;
    }) pats;
  }

let mk_pat_tuple (l:list pat) : pat = Pat_tuple l

let mk_arm (arm_pat:pat) (arm_body:expr) : arm = { arm_pat; arm_body }

let mk_match (expr_match_expr:expr) (expr_match_arms:list arm) : expr =
  Expr_match { expr_match_expr; expr_match_arms }

let mk_expr_field (base:expr) (f:string) : expr =
  Expr_field { expr_field_base = base; expr_field_member = f; expr_field_named = true }

let mk_expr_field_unnamed (base:expr) (i:int) : expr =
  Expr_field { expr_field_base = base; expr_field_member = string_of_int i; expr_field_named = false }

let mk_expr_struct (path:list string) (fields:list (string & expr)) : expr =
  Expr_struct {
    expr_struct_path = path;
    expr_struct_fields = L.map (fun (f, e) -> {
      field_val_name = f;
      field_val_expr = e;
    }) fields;
  }

let mk_expr_tuple (l:list expr) : expr = Expr_tuple l

let mk_mem_replace (t:typ) (e:expr) (new_v:expr) : expr =
  mk_call
    (Expr_path [{ path_segment_name = "std"; path_segment_generic_args = [] };
                { path_segment_name = "mem"; path_segment_generic_args = [] };
                { path_segment_name = "replace"; path_segment_generic_args = [t] }])
    [e; new_v]

let mk_method_call (receiver:expr) (name:string) (args:list expr) : expr =
  Expr_method_call {
    expr_method_call_receiver = receiver;
    expr_method_call_name = name;
    expr_method_call_args = args;
  }

let mk_cast (e:expr) (ty:typ) : expr =
  Expr_cast {
    expr_cast_expr = e;
    expr_cast_type = ty;
  }

let mk_new_mutex (e:expr) =
  mk_call
    (mk_expr_path ["std"; "sync"; "Mutex"; "new"])
    [e]

let mk_lock_mutex (e:expr) : expr =
  let e_lock = mk_method_call e "lock" [] in
  mk_method_call e_lock "unwrap" []
  // let is_mut = true in
  // mk_reference_expr is_mut e_lock_unwrap

let mk_unlock_mutex (e:expr) : expr =
  mk_call
    (mk_expr_path ["std"; "mem"; "drop"])
    [e]

let mk_scalar_fn_arg (name:string) (is_mut:bool) (t:typ) =
  Fn_arg_pat {
    pat_typ_pat = Pat_ident {
      pat_name = name;
      by_ref = false;
      is_mut;
    };
    pat_typ_typ = t;
  }

let mk_ref_fn_arg (name:string) (is_mut:bool) (t:typ) =
  Fn_arg_pat {
    pat_typ_pat = Pat_ident {
      pat_name = name;
      by_ref = true;
      is_mut;
    };
    pat_typ_typ = t;
  }

let mk_generic_type_param
  (generic_type_param_name:string)
  (generic_type_param_trait_bounds:list (list string)) : generic_type_param =
  { generic_type_param_name; generic_type_param_trait_bounds }

let mk_fn_signature (fn_const:bool) (fn_name:string) (fn_generics:list generic_type_param) (fn_args:list fn_arg) (fn_ret_t:typ) =
  let fn_generics = L.map Generic_type_param fn_generics in
  { fn_const; fn_name; fn_generics; fn_args; fn_ret_t }

let mk_local_stmt (name:option string) (t:option typ) (is_mut:bool) (init:expr) =
  Stmt_local {
    local_stmt_pat =
      (match name with
       | None -> None
       | Some name ->
         let p = Pat_ident { pat_name = name; by_ref = false; is_mut } in
         match t with
         | None -> Some p
         | Some t -> Some (Pat_typ { pat_typ_pat = p; pat_typ_typ = t }));
    local_stmt_init = Some init
  }

let mk_fn (fn_sig:fn_signature) (fn_body:list stmt) =
  { fn_sig; fn_body; }

let mk_derive_attr (s:string) : attribute = Attr_derive s

let mk_item_struct (attrs:list attribute) (name:string) (generics:list generic_type_param) (fields:list (string & typ))
  : item =

  Item_struct {
    item_struct_attrs = attrs;
    item_struct_name = name;
    item_struct_generics = L.map Generic_type_param generics;
    item_struct_fields = L.map (fun (f, t) -> {
      field_typ_name = f;
      field_typ_typ = t;
    }) fields;
  }

let mk_item_type (name:string) (generics:list generic_type_param) (t:typ) : item =
  Item_type {
    item_type_name = name;
    item_type_generics = L.map Generic_type_param generics;
    item_type_typ = t;
  }

let mk_item_enum (attrs:list attribute) (name:string) (generics:list generic_type_param) (variants:list (string & list typ))
  : item =

  Item_enum {
    item_enum_attrs = attrs;
    item_enum_name = name;
    item_enum_generics = L.map Generic_type_param generics;
    item_enum_variants = L.map (fun (v, typs) -> {
      enum_variant_name = v;
      enum_variant_fields = typs;
    }) variants;
  }

let mk_item_static (name:string) (t:typ) (init:expr) : item =
  Item_static {
    item_static_name = name;
    item_static_typ = t;
    item_static_init = init;
  }

let mk_file (file_name:string) (file_items:list item) : file = { file_name; file_items }
