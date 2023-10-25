module Pulse2Rust.Rust.Syntax

open FStar.Compiler.Effect

module L = FStar.Compiler.List

let mk_ref_typ (is_mut:bool) (t:typ) : typ =
  Typ_reference { typ_ref_mut = is_mut; typ_ref_typ = t }

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

let mk_call (head:expr) (args:list expr) =
  Expr_call { expr_call_fn = head; expr_call_args = args }

let mk_if (expr_if_cond:expr) (expr_if_then:list stmt) (expr_if_else:option expr) : expr =
  Expr_if { expr_if_cond; expr_if_then; expr_if_else }

let mk_while (expr_while_cond:expr) (expr_while_body:list stmt) : expr =
  Expr_while { expr_while_cond; expr_while_body }

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