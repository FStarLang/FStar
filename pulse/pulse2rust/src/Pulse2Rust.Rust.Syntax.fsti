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

open FStarC.Compiler.Effect

type lit_int_width =
  | I8
  | I16
  | I32
  | I64

type lit_int = {
  lit_int_val : string;
  lit_int_signed : option bool;
  lit_int_width : option lit_int_width;
}

type lit =
  | Lit_int of lit_int
  | Lit_bool of bool
  | Lit_unit
  | Lit_string of string

type binop =
  | Add
  | Sub
  | Ne
  | Eq
  | Lt
  | Le
  | Gt
  | Ge
  | Rem
  | And
  | Or
  | Mul
  | Shr
  | Shl
  | BitAnd
  | BitOr

type unop =
  | Deref

type pat_ident = {
  pat_name : string;
  by_ref : bool;
  is_mut : bool;
}

type pat_tuple_struct = {
  pat_ts_path : list path_segment;
  pat_ts_elems : list pat;
}

and field_pat = {
  field_pat_name : string;
  field_pat_pat : pat;
}

and pat_struct = {
  pat_struct_path : string;
  pat_struct_fields : list field_pat;
}

and pat_typ = {
  pat_typ_pat : pat;
  pat_typ_typ : typ
}

and pat =
  | Pat_ident of pat_ident
  | Pat_tuple_struct of pat_tuple_struct
  | Pat_wild
  | Pat_lit of lit
  | Pat_struct of pat_struct
  | Pat_tuple of list pat
  | Pat_typ of pat_typ
  | Pat_path of list path_segment

and expr =
  | Expr_binop of expr_bin
  | Expr_path of list path_segment
  | Expr_call of expr_call
  | Expr_unary of expr_unary
  | Expr_assign of expr_assignment
  | Expr_block of list stmt
  | Expr_lit of lit
  | Expr_if of expr_if
  | Expr_while of expr_while
  | Expr_index of expr_index
  | Expr_repeat of expr_repeat
  | Expr_reference of expr_reference
  | Expr_match of expr_match
  | Expr_field of expr_field
  | Expr_struct of expr_struct
  | Expr_tuple of list expr
  | Expr_method_call of expr_method_call
  | Expr_cast of expr_cast
  | Expr_range of expr_range

and expr_bin = {
  expr_bin_left : expr;
  expr_bin_op : binop;
  expr_bin_right : expr
}

and expr_unary = {
  expr_unary_op : unop;
  expr_unary_expr : expr
}

and expr_call = {
  expr_call_fn : expr;
  expr_call_args : list expr;
}

and expr_index = {
  expr_index_base : expr;
  expr_index_index : expr;
}

and expr_assignment = {
  expr_assignment_l : expr;
  expr_assignment_r : expr;
}

and expr_if = {
  expr_if_cond : expr;
  expr_if_then : list stmt;
  expr_if_else : option expr;  // only EBlock or Expr_if, if set
}

and expr_while = {
  expr_while_cond : expr;
  expr_while_body : list stmt;
}

and expr_repeat = {
  expr_repeat_elem : expr;
  expr_repeat_len : expr;
}

and expr_reference = {
  expr_reference_is_mut : bool;
  expr_reference_expr : expr
}

and arm = {
  arm_pat : pat;
  arm_body : expr
}

and expr_match = {
  expr_match_expr : expr;
  expr_match_arms : list arm;
}

and expr_field = {
  expr_field_base : expr;
  expr_field_member : string;
  expr_field_named : bool;
}

and expr_struct = {
  expr_struct_path : list string;
  expr_struct_fields : list field_val;
}

and field_val = {
  field_val_name : string;
  field_val_expr : expr;
}

and expr_method_call = {
  expr_method_call_receiver : expr;
  expr_method_call_name : string;
  expr_method_call_args : list expr;
}

and expr_cast = {
  expr_cast_expr : expr;
  expr_cast_type : typ;
}

and expr_range = {
  expr_range_start: option expr;
  expr_range_limits: range_limits;
  expr_range_end: option expr;
}

and range_limits =
  | RangeLimitsHalfOpen
  | RangeLimitsClosed

and local_stmt = {
  local_stmt_pat : option pat;
  local_stmt_init : option expr;
}

and stmt =
  | Stmt_local of local_stmt
  | Stmt_expr of expr

and typ =
  | Typ_path of list path_segment
  | Typ_reference of typ_reference
  | Typ_slice of typ
  | Typ_array of typ_array
  | Typ_unit
  | Typ_infer
  | Typ_fn of typ_fn
  | Typ_tuple of list typ

and typ_reference = {
  typ_ref_mut : bool;
  typ_ref_typ : typ;
}

//
// TODO: THIS NEEDS FIXING
// we are using path_segment for exprs, pats as well
// whereas generic args are only for typ
//
and path_segment = {
  path_segment_name : string;
  path_segment_generic_args : list typ;
}

and typ_array = {
  typ_array_elem : typ;
  typ_array_len : expr;
}

and typ_fn = {
  typ_fn_args : list typ;
  typ_fn_ret : typ;
}

type fn_arg =
  | Fn_arg_pat of pat_typ

type generic_type_param = {
  generic_type_param_name : string;
  generic_type_param_trait_bounds : list (list string);  // list of paths
}

type generic_param =
  | Generic_type_param of generic_type_param

type fn_signature = {
  fn_const : bool;
  fn_name : string;
  fn_generics : list generic_param;
  fn_args : list fn_arg;
  fn_ret_t : typ;
}

type fn = {
  fn_sig : fn_signature;
  fn_body : list stmt;
}

type field_typ = {
  field_typ_name : string;
  field_typ_typ : typ;
}

type attribute =
  | Attr_derive : string -> attribute

type item_struct = {
  item_struct_attrs : list attribute;
  item_struct_name : string;
  item_struct_generics : list generic_param;
  item_struct_fields : list field_typ;
}

type item_type = {
  item_type_name : string;
  item_type_generics : list generic_param;
  item_type_typ : typ;
}

type enum_variant = {
  enum_variant_name : string;
  enum_variant_fields : list typ;
}

type item_enum = {
  item_enum_attrs : list attribute;
  item_enum_name : string;
  item_enum_generics : list generic_param;
  item_enum_variants : list enum_variant
}

type item_static = {
  item_static_name : string;
  item_static_typ  : typ;
  item_static_init : expr;
}

type item =
  | Item_fn of fn
  | Item_struct of item_struct
  | Item_type of item_type
  | Item_enum of item_enum
  | Item_static of item_static

type file = {
  file_name : string;
  file_items : list item;
}

val vec_new_fn : string
val panic_fn : string

val mk_scalar_typ (name:string) : typ
val mk_ref_typ (is_mut:bool) (t:typ) : typ
val mk_box_typ (t:typ) : typ
val mk_slice_typ (t:typ) : typ
val mk_vec_typ (t:typ) : typ
val mk_mutex_typ (t:typ) : typ
val mk_option_typ (t:typ) : typ
val mk_array_typ (t:typ) (len:expr) : typ
val mk_named_typ (path:list string) (s:string) (generic_args:list typ) : typ
val mk_fn_typ (arg_typs:list typ) (ret_typ:typ) : typ
val mk_tuple_typ (l:list typ) : typ

val mk_expr_path_singl (s:string) : expr
val mk_expr_path (l:list string) : expr
val mk_lit_bool (b:bool) : expr
val mk_binop (e1:expr) (op:binop) (e2:expr) : expr
val mk_block_expr (l:list stmt) : expr
val mk_ref_read (r:expr) : expr
val mk_expr_index (base:expr) (index:expr) : expr
val mk_assign (l r:expr) : expr
val mk_ref_assign (l r:expr) : expr
val mk_call (head:expr) (args:list expr) : expr
val mk_if (cond:expr) (then_:list stmt) (else_:option expr) : expr  // else is Block or ExprIf
val mk_while (cond:expr) (body:list stmt) : expr
val mk_repeat (elem len:expr) : expr
val mk_reference_expr (is_mut:bool) (e:expr) : expr
val mk_pat_ident (path:string) : pat
val mk_pat_ts (path:list string) (s:string) (elems:list pat) : pat
val mk_pat_struct (path:string) (fields:list (string & pat)) : pat
val mk_pat_tuple (l:list pat) : pat
val mk_arm (arm_pat:pat) (arm_body:expr) : arm
val mk_match (scrutinee:expr) (arms:list arm) : expr
val mk_expr_field (base:expr) (f:string) : expr
val mk_expr_field_unnamed (base:expr) (i:int) : expr
val mk_expr_struct (path:list string) (fields:list (string & expr)) : expr
val mk_expr_tuple (l:list expr) : expr
val mk_mem_replace (t:typ) (e:expr) (new_v:expr) : expr
val mk_method_call (receiver:expr) (name:string) (args:list expr) : expr
val mk_cast (e:expr) (ty:typ) : expr
val mk_range (s:option expr) (l:range_limits) (e:option expr) : expr

val mk_new_mutex (e:expr) : expr
val mk_lock_mutex (e:expr) : expr
val mk_unlock_mutex (e:expr) : expr

val mk_local_stmt (name:option string) (t:option typ) (is_mut:bool) (init:expr) : stmt
val mk_scalar_fn_arg (name:string) (is_mut:bool) (t:typ) : fn_arg
val mk_ref_fn_arg (name:string) (is_mut:bool) (t:typ) : fn_arg
val mk_generic_type_param (generic_name:string) (trait_bounds:list (list string)) : generic_type_param
val mk_fn_signature (fn_const:bool) (fn_name:string) (fn_generics:list generic_type_param) (fn_args:list fn_arg) (fn_ret_t:typ) : fn_signature
val mk_fn (fn_sig:fn_signature) (fn_body:list stmt) : fn

val mk_derive_attr (s:string) : attribute

val mk_item_struct (attrs:list attribute) (name:string) (generics:list generic_type_param) (fields:list (string & typ))
  : item

val mk_item_type (name:string) (generics:list generic_type_param) (t:typ) : item

val mk_item_enum (attrs:list attribute) (name:string) (generics:list generic_type_param) (variants:list (string & list typ))
  : item

val mk_item_static (name:string) (t:typ) (init:expr) : item

val mk_file (name:string) (items:list item) : file
