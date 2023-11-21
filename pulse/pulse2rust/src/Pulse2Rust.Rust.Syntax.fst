module Pulse2Rust.Rust.Syntax

open FStar.Compiler.Effect

module L = FStar.Compiler.List

let vec_new_fn = "vec_new"
let panic_fn = "panic"

let mk_scalar_typ (name:string) : typ =
  Typ_path [ {typ_path_segment_name = name; typ_path_segment_generic_args = [] } ]

let mk_ref_typ (is_mut:bool) (t:typ) : typ =
  Typ_reference { typ_ref_mut = is_mut; typ_ref_typ = t }

let mk_box_typ (t:typ) : typ =
  Typ_path [
    { typ_path_segment_name = "std"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "boxed"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "Box"; typ_path_segment_generic_args = [t] };
  ]

let mk_slice_typ (t:typ) : typ = Typ_slice t

let mk_vec_typ (t:typ) : typ =
  Typ_path [
    { typ_path_segment_name = "std"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "vec"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "Vec"; typ_path_segment_generic_args = [t] };
  ]

let mk_option_typ (t:typ) : typ =
  Typ_path [
    { typ_path_segment_name = "std"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "option"; typ_path_segment_generic_args = [] };
    { typ_path_segment_name = "Option"; typ_path_segment_generic_args = [t] };
  ]

let mk_array_typ (t:typ) (len:expr) : typ =
  Typ_array { typ_array_elem = t; typ_array_len = len }

let mk_named_typ (s:string) (generic_args:list typ) : typ =
  Typ_path [
    { typ_path_segment_name = s; typ_path_segment_generic_args = generic_args };
  ]

let mk_expr_path_singl s = Expr_path [s]
let mk_expr_path l = Expr_path l

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
  Pat_ident { pat_name = path; by_ref = false; is_mut = false }

let mk_pat_ts (pat_ts_path:string) (pat_ts_elems:list pat) : pat =
  if L.length pat_ts_elems = 0
  then Pat_ident { pat_name = pat_ts_path; by_ref = false; is_mut = false }
  else Pat_tuple_struct { pat_ts_path; pat_ts_elems}

let mk_arm (arm_pat:pat) (arm_body:expr) : arm = { arm_pat; arm_body }

let mk_match (expr_match_expr:expr) (expr_match_arms:list arm) : expr =
  Expr_match { expr_match_expr; expr_match_arms }

let mk_expr_field (base:expr) (f:string) : expr =
  Expr_field { expr_field_base = base; expr_field_member = f }

let mk_expr_struct (path:list string) (fields:list (string & expr)) : expr =
  Expr_struct {
    expr_struct_path = path;
    expr_struct_fields = L.map (fun (f, e) -> {
      field_val_name = f;
      field_val_expr = e;
    }) fields;
  }

let mk_scalar_fn_arg (name:string) (t:typ) =
  Fn_arg_pat {
    pat_typ_pat = Pat_ident {
      pat_name = name;
      by_ref = false;
      is_mut = false;
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

let mk_fn_signature (fn_name:string) (fn_generics:list string) (fn_args:list fn_arg) (fn_ret_t:typ) =
  let fn_generics = L.map Generic_type_param fn_generics in
  { fn_name; fn_generics; fn_args; fn_ret_t }

let mk_local_stmt (name:string) (is_mut:bool) (init:expr) =
  Stmt_local {
    local_stmt_pat = Pat_ident { pat_name = name; by_ref = false; is_mut };
    local_stmt_init = Some init
  }

let mk_fn (fn_sig:fn_signature) (fn_body:list stmt) =
  { fn_sig; fn_body; }

let mk_item_struct (name:string) (generics:list string) (fields:list (string & typ))
  : item =

  Item_struct {
    item_struct_name = name;
    item_struct_generics = L.map Generic_type_param generics;
    item_struct_fields = L.map (fun (f, t) -> {
      field_typ_name = f;
      field_typ_typ = t;
    }) fields;
  }

let mk_file (file_name:string) (file_items:list item) : file = { file_name; file_items }
