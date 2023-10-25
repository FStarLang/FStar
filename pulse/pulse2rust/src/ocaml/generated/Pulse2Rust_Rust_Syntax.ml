open Prims
type typ =
  | Typ_name of Prims.string 
  | Typ_reference of typ_reference 
and typ_reference = {
  typ_ref_mut: Prims.bool ;
  typ_ref_typ: typ }
let (uu___is_Typ_name : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_name _0 -> true | uu___ -> false
let (__proj__Typ_name__item___0 : typ -> Prims.string) =
  fun projectee -> match projectee with | Typ_name _0 -> _0
let (uu___is_Typ_reference : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_reference _0 -> true | uu___ -> false
let (__proj__Typ_reference__item___0 : typ -> typ_reference) =
  fun projectee -> match projectee with | Typ_reference _0 -> _0
let (__proj__Mktyp_reference__item__typ_ref_mut :
  typ_reference -> Prims.bool) =
  fun projectee ->
    match projectee with | { typ_ref_mut; typ_ref_typ;_} -> typ_ref_mut
let (__proj__Mktyp_reference__item__typ_ref_typ : typ_reference -> typ) =
  fun projectee ->
    match projectee with | { typ_ref_mut; typ_ref_typ;_} -> typ_ref_typ
type pat_ident =
  {
  pat_name: Prims.string ;
  by_ref: Prims.bool ;
  is_mut: Prims.bool }
let (__proj__Mkpat_ident__item__pat_name : pat_ident -> Prims.string) =
  fun projectee ->
    match projectee with | { pat_name; by_ref; is_mut;_} -> pat_name
let (__proj__Mkpat_ident__item__by_ref : pat_ident -> Prims.bool) =
  fun projectee ->
    match projectee with | { pat_name; by_ref; is_mut;_} -> by_ref
let (__proj__Mkpat_ident__item__is_mut : pat_ident -> Prims.bool) =
  fun projectee ->
    match projectee with | { pat_name; by_ref; is_mut;_} -> is_mut
type pat =
  | Pat_ident of pat_ident 
let (uu___is_Pat_ident : pat -> Prims.bool) = fun projectee -> true
let (__proj__Pat_ident__item___0 : pat -> pat_ident) =
  fun projectee -> match projectee with | Pat_ident _0 -> _0
type lit_int_width =
  | I8 
  | I16 
  | I32 
  | I64 
let (uu___is_I8 : lit_int_width -> Prims.bool) =
  fun projectee -> match projectee with | I8 -> true | uu___ -> false
let (uu___is_I16 : lit_int_width -> Prims.bool) =
  fun projectee -> match projectee with | I16 -> true | uu___ -> false
let (uu___is_I32 : lit_int_width -> Prims.bool) =
  fun projectee -> match projectee with | I32 -> true | uu___ -> false
let (uu___is_I64 : lit_int_width -> Prims.bool) =
  fun projectee -> match projectee with | I64 -> true | uu___ -> false
type lit_int =
  {
  lit_int_val: Prims.string ;
  lit_int_signed: Prims.bool FStar_Pervasives_Native.option ;
  lit_int_width: lit_int_width FStar_Pervasives_Native.option }
let (__proj__Mklit_int__item__lit_int_val : lit_int -> Prims.string) =
  fun projectee ->
    match projectee with
    | { lit_int_val; lit_int_signed; lit_int_width = lit_int_width1;_} ->
        lit_int_val
let (__proj__Mklit_int__item__lit_int_signed :
  lit_int -> Prims.bool FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { lit_int_val; lit_int_signed; lit_int_width = lit_int_width1;_} ->
        lit_int_signed
let (__proj__Mklit_int__item__lit_int_width :
  lit_int -> lit_int_width FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { lit_int_val; lit_int_signed; lit_int_width = lit_int_width1;_} ->
        lit_int_width1
type lit =
  | Lit_int of lit_int 
let (uu___is_Lit_int : lit -> Prims.bool) = fun projectee -> true
let (__proj__Lit_int__item___0 : lit -> lit_int) =
  fun projectee -> match projectee with | Lit_int _0 -> _0
type binop =
  | Add 
  | Sub 
let (uu___is_Add : binop -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Sub : binop -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu___ -> false
type unop =
  | Deref 
let (uu___is_Deref : unop -> Prims.bool) = fun projectee -> true
type expr =
  | Expr_binop of expr_bin 
  | Expr_path of Prims.string 
  | Expr_call of expr_call 
  | Expr_unary of expr_unary 
  | Expr_assign of expr_assignment 
  | Expr_block of stmt Prims.list 
  | Expr_lit of lit 
  | Expr_if of expr_if 
  | Expr_while of expr_while 
and expr_bin =
  {
  expr_bin_left: expr ;
  expr_bin_op: binop ;
  expr_bin_right: expr }
and expr_unary = {
  expr_unary_op: unop ;
  expr_unary_expr: expr }
and expr_call = {
  expr_call_fn: expr ;
  expr_call_args: expr Prims.list }
and expr_assignment = {
  expr_assignment_l: expr ;
  expr_assignment_r: expr }
and expr_if =
  {
  expr_if_cond: expr ;
  expr_if_then: stmt Prims.list ;
  expr_if_else: expr FStar_Pervasives_Native.option }
and expr_while = {
  expr_while_cond: expr ;
  expr_while_body: stmt Prims.list }
and local_stmt =
  {
  local_stmt_pat: pat ;
  local_stmt_init: expr FStar_Pervasives_Native.option }
and stmt =
  | Stmt_local of local_stmt 
  | Stmt_expr of expr 
let (uu___is_Expr_binop : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_binop _0 -> true | uu___ -> false
let (__proj__Expr_binop__item___0 : expr -> expr_bin) =
  fun projectee -> match projectee with | Expr_binop _0 -> _0
let (uu___is_Expr_path : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_path _0 -> true | uu___ -> false
let (__proj__Expr_path__item___0 : expr -> Prims.string) =
  fun projectee -> match projectee with | Expr_path _0 -> _0
let (uu___is_Expr_call : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_call _0 -> true | uu___ -> false
let (__proj__Expr_call__item___0 : expr -> expr_call) =
  fun projectee -> match projectee with | Expr_call _0 -> _0
let (uu___is_Expr_unary : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_unary _0 -> true | uu___ -> false
let (__proj__Expr_unary__item___0 : expr -> expr_unary) =
  fun projectee -> match projectee with | Expr_unary _0 -> _0
let (uu___is_Expr_assign : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_assign _0 -> true | uu___ -> false
let (__proj__Expr_assign__item___0 : expr -> expr_assignment) =
  fun projectee -> match projectee with | Expr_assign _0 -> _0
let (uu___is_Expr_block : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_block _0 -> true | uu___ -> false
let (__proj__Expr_block__item___0 : expr -> stmt Prims.list) =
  fun projectee -> match projectee with | Expr_block _0 -> _0
let (uu___is_Expr_lit : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_lit _0 -> true | uu___ -> false
let (__proj__Expr_lit__item___0 : expr -> lit) =
  fun projectee -> match projectee with | Expr_lit _0 -> _0
let (uu___is_Expr_if : expr -> Prims.bool) =
  fun projectee -> match projectee with | Expr_if _0 -> true | uu___ -> false
let (__proj__Expr_if__item___0 : expr -> expr_if) =
  fun projectee -> match projectee with | Expr_if _0 -> _0
let (uu___is_Expr_while : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_while _0 -> true | uu___ -> false
let (__proj__Expr_while__item___0 : expr -> expr_while) =
  fun projectee -> match projectee with | Expr_while _0 -> _0
let (__proj__Mkexpr_bin__item__expr_bin_left : expr_bin -> expr) =
  fun projectee ->
    match projectee with
    | { expr_bin_left; expr_bin_op; expr_bin_right;_} -> expr_bin_left
let (__proj__Mkexpr_bin__item__expr_bin_op : expr_bin -> binop) =
  fun projectee ->
    match projectee with
    | { expr_bin_left; expr_bin_op; expr_bin_right;_} -> expr_bin_op
let (__proj__Mkexpr_bin__item__expr_bin_right : expr_bin -> expr) =
  fun projectee ->
    match projectee with
    | { expr_bin_left; expr_bin_op; expr_bin_right;_} -> expr_bin_right
let (__proj__Mkexpr_unary__item__expr_unary_op : expr_unary -> unop) =
  fun projectee ->
    match projectee with
    | { expr_unary_op; expr_unary_expr;_} -> expr_unary_op
let (__proj__Mkexpr_unary__item__expr_unary_expr : expr_unary -> expr) =
  fun projectee ->
    match projectee with
    | { expr_unary_op; expr_unary_expr;_} -> expr_unary_expr
let (__proj__Mkexpr_call__item__expr_call_fn : expr_call -> expr) =
  fun projectee ->
    match projectee with | { expr_call_fn; expr_call_args;_} -> expr_call_fn
let (__proj__Mkexpr_call__item__expr_call_args :
  expr_call -> expr Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_call_fn; expr_call_args;_} -> expr_call_args
let (__proj__Mkexpr_assignment__item__expr_assignment_l :
  expr_assignment -> expr) =
  fun projectee ->
    match projectee with
    | { expr_assignment_l; expr_assignment_r;_} -> expr_assignment_l
let (__proj__Mkexpr_assignment__item__expr_assignment_r :
  expr_assignment -> expr) =
  fun projectee ->
    match projectee with
    | { expr_assignment_l; expr_assignment_r;_} -> expr_assignment_r
let (__proj__Mkexpr_if__item__expr_if_cond : expr_if -> expr) =
  fun projectee ->
    match projectee with
    | { expr_if_cond; expr_if_then; expr_if_else;_} -> expr_if_cond
let (__proj__Mkexpr_if__item__expr_if_then : expr_if -> stmt Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_if_cond; expr_if_then; expr_if_else;_} -> expr_if_then
let (__proj__Mkexpr_if__item__expr_if_else :
  expr_if -> expr FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { expr_if_cond; expr_if_then; expr_if_else;_} -> expr_if_else
let (__proj__Mkexpr_while__item__expr_while_cond : expr_while -> expr) =
  fun projectee ->
    match projectee with
    | { expr_while_cond; expr_while_body;_} -> expr_while_cond
let (__proj__Mkexpr_while__item__expr_while_body :
  expr_while -> stmt Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_while_cond; expr_while_body;_} -> expr_while_body
let (__proj__Mklocal_stmt__item__local_stmt_pat : local_stmt -> pat) =
  fun projectee ->
    match projectee with
    | { local_stmt_pat; local_stmt_init;_} -> local_stmt_pat
let (__proj__Mklocal_stmt__item__local_stmt_init :
  local_stmt -> expr FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { local_stmt_pat; local_stmt_init;_} -> local_stmt_init
let (uu___is_Stmt_local : stmt -> Prims.bool) =
  fun projectee ->
    match projectee with | Stmt_local _0 -> true | uu___ -> false
let (__proj__Stmt_local__item___0 : stmt -> local_stmt) =
  fun projectee -> match projectee with | Stmt_local _0 -> _0
let (uu___is_Stmt_expr : stmt -> Prims.bool) =
  fun projectee ->
    match projectee with | Stmt_expr _0 -> true | uu___ -> false
let (__proj__Stmt_expr__item___0 : stmt -> expr) =
  fun projectee -> match projectee with | Stmt_expr _0 -> _0
type pat_typ = {
  pat_typ_pat: pat ;
  pat_typ_typ: typ }
let (__proj__Mkpat_typ__item__pat_typ_pat : pat_typ -> pat) =
  fun projectee ->
    match projectee with | { pat_typ_pat; pat_typ_typ;_} -> pat_typ_pat
let (__proj__Mkpat_typ__item__pat_typ_typ : pat_typ -> typ) =
  fun projectee ->
    match projectee with | { pat_typ_pat; pat_typ_typ;_} -> pat_typ_typ
type fn_arg =
  | Fn_arg_pat of pat_typ 
let (uu___is_Fn_arg_pat : fn_arg -> Prims.bool) = fun projectee -> true
let (__proj__Fn_arg_pat__item___0 : fn_arg -> pat_typ) =
  fun projectee -> match projectee with | Fn_arg_pat _0 -> _0
type generic_param =
  | Generic_type_param of Prims.string 
let (uu___is_Generic_type_param : generic_param -> Prims.bool) =
  fun projectee -> true
let (__proj__Generic_type_param__item___0 : generic_param -> Prims.string) =
  fun projectee -> match projectee with | Generic_type_param _0 -> _0
type fn_signature =
  {
  fn_name: Prims.string ;
  fn_generics: generic_param Prims.list ;
  fn_args: fn_arg Prims.list ;
  fn_ret_t: typ }
let (__proj__Mkfn_signature__item__fn_name : fn_signature -> Prims.string) =
  fun projectee ->
    match projectee with
    | { fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_name
let (__proj__Mkfn_signature__item__fn_generics :
  fn_signature -> generic_param Prims.list) =
  fun projectee ->
    match projectee with
    | { fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_generics
let (__proj__Mkfn_signature__item__fn_args :
  fn_signature -> fn_arg Prims.list) =
  fun projectee ->
    match projectee with
    | { fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_args
let (__proj__Mkfn_signature__item__fn_ret_t : fn_signature -> typ) =
  fun projectee ->
    match projectee with
    | { fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_ret_t
type fn = {
  fn_sig: fn_signature ;
  fn_body: stmt Prims.list }
let (__proj__Mkfn__item__fn_sig : fn -> fn_signature) =
  fun projectee -> match projectee with | { fn_sig; fn_body;_} -> fn_sig
let (__proj__Mkfn__item__fn_body : fn -> stmt Prims.list) =
  fun projectee -> match projectee with | { fn_sig; fn_body;_} -> fn_body
let (mk_ref_typ : Prims.bool -> typ -> typ) =
  fun is_mut ->
    fun t -> Typ_reference { typ_ref_mut = is_mut; typ_ref_typ = t }
let (mk_block_expr : stmt Prims.list -> expr) = fun l -> Expr_block l
let (mk_assign : expr -> expr -> expr) =
  fun l ->
    fun r -> Expr_assign { expr_assignment_l = l; expr_assignment_r = r }
let (mk_ref_assign : expr -> expr -> expr) =
  fun l ->
    fun r ->
      Expr_assign
        {
          expr_assignment_l =
            (Expr_unary { expr_unary_op = Deref; expr_unary_expr = l });
          expr_assignment_r = r
        }
let (mk_ref_read : expr -> expr) =
  fun l -> Expr_unary { expr_unary_op = Deref; expr_unary_expr = l }
let (mk_call : expr -> expr Prims.list -> expr) =
  fun head ->
    fun args -> Expr_call { expr_call_fn = head; expr_call_args = args }
let (mk_if :
  expr -> stmt Prims.list -> expr FStar_Pervasives_Native.option -> expr) =
  fun expr_if_cond ->
    fun expr_if_then ->
      fun expr_if_else ->
        Expr_if { expr_if_cond; expr_if_then; expr_if_else }
let (mk_while : expr -> stmt Prims.list -> expr) =
  fun expr_while_cond ->
    fun expr_while_body -> Expr_while { expr_while_cond; expr_while_body }
let (mk_scalar_fn_arg : Prims.string -> typ -> fn_arg) =
  fun name ->
    fun t ->
      Fn_arg_pat
        {
          pat_typ_pat =
            (Pat_ident { pat_name = name; by_ref = false; is_mut = false });
          pat_typ_typ = t
        }
let (mk_ref_fn_arg : Prims.string -> Prims.bool -> typ -> fn_arg) =
  fun name ->
    fun is_mut ->
      fun t ->
        Fn_arg_pat
          {
            pat_typ_pat =
              (Pat_ident { pat_name = name; by_ref = true; is_mut });
            pat_typ_typ = t
          }
let (mk_fn_signature :
  Prims.string ->
    Prims.string Prims.list -> fn_arg Prims.list -> typ -> fn_signature)
  =
  fun fn_name ->
    fun fn_generics ->
      fun fn_args ->
        fun fn_ret_t ->
          let fn_generics1 =
            FStar_Compiler_List.map (fun uu___ -> Generic_type_param uu___)
              fn_generics in
          { fn_name; fn_generics = fn_generics1; fn_args; fn_ret_t }
let (mk_local_stmt : Prims.string -> Prims.bool -> expr -> stmt) =
  fun name ->
    fun is_mut ->
      fun init ->
        Stmt_local
          {
            local_stmt_pat =
              (Pat_ident { pat_name = name; by_ref = false; is_mut });
            local_stmt_init = (FStar_Pervasives_Native.Some init)
          }
let (mk_fn : fn_signature -> stmt Prims.list -> fn) =
  fun fn_sig -> fun fn_body -> { fn_sig; fn_body }