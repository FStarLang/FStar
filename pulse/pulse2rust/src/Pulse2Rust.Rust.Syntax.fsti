module Pulse2Rust.Rust.Syntax

open FStar.Compiler.Effect

type typ =
  | Typ_path of list typ_path_segment
  | Typ_reference of typ_reference

and typ_reference = {
  typ_ref_mut : bool;
  typ_ref_typ : typ;
}

and typ_path_segment = {
  typ_path_segment_name : string;
  typ_path_segment_generic_args : list typ;
}

type pat_ident = {
  pat_name : string;
  by_ref : bool;
  is_mut : bool;
}

type pat =
  | Pat_ident of pat_ident

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

type binop =
  | Add
  | Sub
  | Ne
  | Eq
  | Lt
  | Le
  | Gt
  | Ge

type unop =
  | Deref

type expr =
  | Expr_binop of expr_bin
  | Expr_path of string
  | Expr_call of expr_call
  | Expr_unary of expr_unary
  | Expr_assign of expr_assignment
  | Expr_block of list stmt
  | Expr_lit of lit
  | Expr_if of expr_if
  | Expr_while of expr_while

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

and local_stmt = {
  local_stmt_pat : pat;
  local_stmt_init : option expr;
}

and stmt =
  | Stmt_local of local_stmt
  | Stmt_expr of expr

type pat_typ = {
  pat_typ_pat : pat;
  pat_typ_typ : typ
}

type fn_arg =
  | Fn_arg_pat of pat_typ

type generic_param =
  | Generic_type_param of string

type fn_signature = {
  fn_name : string;
  fn_generics : list generic_param;
  fn_args : list fn_arg;
  fn_ret_t : typ;
}

type fn = {
  fn_sig : fn_signature;
  fn_body : list stmt;
}

val mk_scalar_typ (name:string) : typ
val mk_ref_typ (is_mut:bool) (t:typ) : typ
val mk_binop (e1:expr) (op:binop) (e2:expr) : expr
val mk_block_expr (l:list stmt) : expr
val mk_ref_read (r:expr) : expr
val mk_assign (l r:expr) : expr
val mk_ref_assign (l r:expr) : expr
val mk_call (head:expr) (args:list expr) : expr
val mk_if (cond:expr) (then_:list stmt) (else_:option expr) : expr  // else is Block or ExprIf
val mk_while (cond:expr) (body:list stmt) : expr
val mk_local_stmt (name:string) (is_mut:bool) (init:expr) : stmt
val mk_scalar_fn_arg (name:string) (t:typ) : fn_arg
val mk_ref_fn_arg (name:string) (is_mut:bool) (t:typ) : fn_arg
val mk_fn_signature (fn_name:string) (fn_generics:list string) (fn_args:list fn_arg) (fn_ret_t:typ) : fn_signature
val mk_fn (fn_sig:fn_signature) (fn_body:list stmt) : fn
