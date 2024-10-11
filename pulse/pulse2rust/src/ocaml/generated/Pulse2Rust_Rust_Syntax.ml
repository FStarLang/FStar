open Prims
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
  | Lit_bool of Prims.bool 
  | Lit_unit 
  | Lit_string of Prims.string 
let (uu___is_Lit_int : lit -> Prims.bool) =
  fun projectee -> match projectee with | Lit_int _0 -> true | uu___ -> false
let (__proj__Lit_int__item___0 : lit -> lit_int) =
  fun projectee -> match projectee with | Lit_int _0 -> _0
let (uu___is_Lit_bool : lit -> Prims.bool) =
  fun projectee ->
    match projectee with | Lit_bool _0 -> true | uu___ -> false
let (__proj__Lit_bool__item___0 : lit -> Prims.bool) =
  fun projectee -> match projectee with | Lit_bool _0 -> _0
let (uu___is_Lit_unit : lit -> Prims.bool) =
  fun projectee -> match projectee with | Lit_unit -> true | uu___ -> false
let (uu___is_Lit_string : lit -> Prims.bool) =
  fun projectee ->
    match projectee with | Lit_string _0 -> true | uu___ -> false
let (__proj__Lit_string__item___0 : lit -> Prims.string) =
  fun projectee -> match projectee with | Lit_string _0 -> _0
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
let (uu___is_Add : binop -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Sub : binop -> Prims.bool) =
  fun projectee -> match projectee with | Sub -> true | uu___ -> false
let (uu___is_Ne : binop -> Prims.bool) =
  fun projectee -> match projectee with | Ne -> true | uu___ -> false
let (uu___is_Eq : binop -> Prims.bool) =
  fun projectee -> match projectee with | Eq -> true | uu___ -> false
let (uu___is_Lt : binop -> Prims.bool) =
  fun projectee -> match projectee with | Lt -> true | uu___ -> false
let (uu___is_Le : binop -> Prims.bool) =
  fun projectee -> match projectee with | Le -> true | uu___ -> false
let (uu___is_Gt : binop -> Prims.bool) =
  fun projectee -> match projectee with | Gt -> true | uu___ -> false
let (uu___is_Ge : binop -> Prims.bool) =
  fun projectee -> match projectee with | Ge -> true | uu___ -> false
let (uu___is_Rem : binop -> Prims.bool) =
  fun projectee -> match projectee with | Rem -> true | uu___ -> false
let (uu___is_And : binop -> Prims.bool) =
  fun projectee -> match projectee with | And -> true | uu___ -> false
let (uu___is_Or : binop -> Prims.bool) =
  fun projectee -> match projectee with | Or -> true | uu___ -> false
let (uu___is_Mul : binop -> Prims.bool) =
  fun projectee -> match projectee with | Mul -> true | uu___ -> false
let (uu___is_Shr : binop -> Prims.bool) =
  fun projectee -> match projectee with | Shr -> true | uu___ -> false
let (uu___is_Shl : binop -> Prims.bool) =
  fun projectee -> match projectee with | Shl -> true | uu___ -> false
let (uu___is_BitAnd : binop -> Prims.bool) =
  fun projectee -> match projectee with | BitAnd -> true | uu___ -> false
let (uu___is_BitOr : binop -> Prims.bool) =
  fun projectee -> match projectee with | BitOr -> true | uu___ -> false
type unop =
  | Deref 
let (uu___is_Deref : unop -> Prims.bool) = fun projectee -> true
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
type pat_tuple_struct =
  {
  pat_ts_path: path_segment Prims.list ;
  pat_ts_elems: pat Prims.list }
and field_pat = {
  field_pat_name: Prims.string ;
  field_pat_pat: pat }
and pat_struct =
  {
  pat_struct_path: Prims.string ;
  pat_struct_fields: field_pat Prims.list }
and pat_typ = {
  pat_typ_pat: pat ;
  pat_typ_typ: typ }
and pat =
  | Pat_ident of pat_ident 
  | Pat_tuple_struct of pat_tuple_struct 
  | Pat_wild 
  | Pat_lit of lit 
  | Pat_struct of pat_struct 
  | Pat_tuple of pat Prims.list 
  | Pat_typ of pat_typ 
  | Pat_path of path_segment Prims.list 
and expr =
  | Expr_binop of expr_bin 
  | Expr_path of path_segment Prims.list 
  | Expr_call of expr_call 
  | Expr_unary of expr_unary 
  | Expr_assign of expr_assignment 
  | Expr_block of stmt Prims.list 
  | Expr_lit of lit 
  | Expr_if of expr_if 
  | Expr_while of expr_while 
  | Expr_index of expr_index 
  | Expr_repeat of expr_repeat 
  | Expr_reference of expr_reference 
  | Expr_match of expr_match 
  | Expr_field of expr_field 
  | Expr_struct of expr_struct 
  | Expr_tuple of expr Prims.list 
  | Expr_method_call of expr_method_call 
  | Expr_cast of expr_cast 
  | Expr_range of expr_range 
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
and expr_index = {
  expr_index_base: expr ;
  expr_index_index: expr }
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
and expr_repeat = {
  expr_repeat_elem: expr ;
  expr_repeat_len: expr }
and expr_reference =
  {
  expr_reference_is_mut: Prims.bool ;
  expr_reference_expr: expr }
and arm = {
  arm_pat: pat ;
  arm_body: expr }
and expr_match = {
  expr_match_expr: expr ;
  expr_match_arms: arm Prims.list }
and expr_field =
  {
  expr_field_base: expr ;
  expr_field_member: Prims.string ;
  expr_field_named: Prims.bool }
and expr_struct =
  {
  expr_struct_path: Prims.string Prims.list ;
  expr_struct_fields: field_val Prims.list }
and field_val = {
  field_val_name: Prims.string ;
  field_val_expr: expr }
and expr_method_call =
  {
  expr_method_call_receiver: expr ;
  expr_method_call_name: Prims.string ;
  expr_method_call_args: expr Prims.list }
and expr_cast = {
  expr_cast_expr: expr ;
  expr_cast_type: typ }
and expr_range =
  {
  expr_range_start: expr FStar_Pervasives_Native.option ;
  expr_range_limits: range_limits ;
  expr_range_end: expr FStar_Pervasives_Native.option }
and range_limits =
  | RangeLimitsHalfOpen 
  | RangeLimitsClosed 
and local_stmt =
  {
  local_stmt_pat: pat FStar_Pervasives_Native.option ;
  local_stmt_init: expr FStar_Pervasives_Native.option }
and stmt =
  | Stmt_local of local_stmt 
  | Stmt_expr of expr 
and typ =
  | Typ_path of path_segment Prims.list 
  | Typ_reference of typ_reference 
  | Typ_slice of typ 
  | Typ_array of typ_array 
  | Typ_unit 
  | Typ_infer 
  | Typ_fn of typ_fn 
  | Typ_tuple of typ Prims.list 
and typ_reference = {
  typ_ref_mut: Prims.bool ;
  typ_ref_typ: typ }
and path_segment =
  {
  path_segment_name: Prims.string ;
  path_segment_generic_args: typ Prims.list }
and typ_array = {
  typ_array_elem: typ ;
  typ_array_len: expr }
and typ_fn = {
  typ_fn_args: typ Prims.list ;
  typ_fn_ret: typ }
let (__proj__Mkpat_tuple_struct__item__pat_ts_path :
  pat_tuple_struct -> path_segment Prims.list) =
  fun projectee ->
    match projectee with | { pat_ts_path; pat_ts_elems;_} -> pat_ts_path
let (__proj__Mkpat_tuple_struct__item__pat_ts_elems :
  pat_tuple_struct -> pat Prims.list) =
  fun projectee ->
    match projectee with | { pat_ts_path; pat_ts_elems;_} -> pat_ts_elems
let (__proj__Mkfield_pat__item__field_pat_name : field_pat -> Prims.string) =
  fun projectee ->
    match projectee with
    | { field_pat_name; field_pat_pat;_} -> field_pat_name
let (__proj__Mkfield_pat__item__field_pat_pat : field_pat -> pat) =
  fun projectee ->
    match projectee with
    | { field_pat_name; field_pat_pat;_} -> field_pat_pat
let (__proj__Mkpat_struct__item__pat_struct_path :
  pat_struct -> Prims.string) =
  fun projectee ->
    match projectee with
    | { pat_struct_path; pat_struct_fields;_} -> pat_struct_path
let (__proj__Mkpat_struct__item__pat_struct_fields :
  pat_struct -> field_pat Prims.list) =
  fun projectee ->
    match projectee with
    | { pat_struct_path; pat_struct_fields;_} -> pat_struct_fields
let (__proj__Mkpat_typ__item__pat_typ_pat : pat_typ -> pat) =
  fun projectee ->
    match projectee with | { pat_typ_pat; pat_typ_typ;_} -> pat_typ_pat
let (__proj__Mkpat_typ__item__pat_typ_typ : pat_typ -> typ) =
  fun projectee ->
    match projectee with | { pat_typ_pat; pat_typ_typ;_} -> pat_typ_typ
let (uu___is_Pat_ident : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_ident _0 -> true | uu___ -> false
let (__proj__Pat_ident__item___0 : pat -> pat_ident) =
  fun projectee -> match projectee with | Pat_ident _0 -> _0
let (uu___is_Pat_tuple_struct : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_tuple_struct _0 -> true | uu___ -> false
let (__proj__Pat_tuple_struct__item___0 : pat -> pat_tuple_struct) =
  fun projectee -> match projectee with | Pat_tuple_struct _0 -> _0
let (uu___is_Pat_wild : pat -> Prims.bool) =
  fun projectee -> match projectee with | Pat_wild -> true | uu___ -> false
let (uu___is_Pat_lit : pat -> Prims.bool) =
  fun projectee -> match projectee with | Pat_lit _0 -> true | uu___ -> false
let (__proj__Pat_lit__item___0 : pat -> lit) =
  fun projectee -> match projectee with | Pat_lit _0 -> _0
let (uu___is_Pat_struct : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_struct _0 -> true | uu___ -> false
let (__proj__Pat_struct__item___0 : pat -> pat_struct) =
  fun projectee -> match projectee with | Pat_struct _0 -> _0
let (uu___is_Pat_tuple : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_tuple _0 -> true | uu___ -> false
let (__proj__Pat_tuple__item___0 : pat -> pat Prims.list) =
  fun projectee -> match projectee with | Pat_tuple _0 -> _0
let (uu___is_Pat_typ : pat -> Prims.bool) =
  fun projectee -> match projectee with | Pat_typ _0 -> true | uu___ -> false
let (__proj__Pat_typ__item___0 : pat -> pat_typ) =
  fun projectee -> match projectee with | Pat_typ _0 -> _0
let (uu___is_Pat_path : pat -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_path _0 -> true | uu___ -> false
let (__proj__Pat_path__item___0 : pat -> path_segment Prims.list) =
  fun projectee -> match projectee with | Pat_path _0 -> _0
let (uu___is_Expr_binop : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_binop _0 -> true | uu___ -> false
let (__proj__Expr_binop__item___0 : expr -> expr_bin) =
  fun projectee -> match projectee with | Expr_binop _0 -> _0
let (uu___is_Expr_path : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_path _0 -> true | uu___ -> false
let (__proj__Expr_path__item___0 : expr -> path_segment Prims.list) =
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
let (uu___is_Expr_index : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_index _0 -> true | uu___ -> false
let (__proj__Expr_index__item___0 : expr -> expr_index) =
  fun projectee -> match projectee with | Expr_index _0 -> _0
let (uu___is_Expr_repeat : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_repeat _0 -> true | uu___ -> false
let (__proj__Expr_repeat__item___0 : expr -> expr_repeat) =
  fun projectee -> match projectee with | Expr_repeat _0 -> _0
let (uu___is_Expr_reference : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_reference _0 -> true | uu___ -> false
let (__proj__Expr_reference__item___0 : expr -> expr_reference) =
  fun projectee -> match projectee with | Expr_reference _0 -> _0
let (uu___is_Expr_match : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_match _0 -> true | uu___ -> false
let (__proj__Expr_match__item___0 : expr -> expr_match) =
  fun projectee -> match projectee with | Expr_match _0 -> _0
let (uu___is_Expr_field : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_field _0 -> true | uu___ -> false
let (__proj__Expr_field__item___0 : expr -> expr_field) =
  fun projectee -> match projectee with | Expr_field _0 -> _0
let (uu___is_Expr_struct : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_struct _0 -> true | uu___ -> false
let (__proj__Expr_struct__item___0 : expr -> expr_struct) =
  fun projectee -> match projectee with | Expr_struct _0 -> _0
let (uu___is_Expr_tuple : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_tuple _0 -> true | uu___ -> false
let (__proj__Expr_tuple__item___0 : expr -> expr Prims.list) =
  fun projectee -> match projectee with | Expr_tuple _0 -> _0
let (uu___is_Expr_method_call : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_method_call _0 -> true | uu___ -> false
let (__proj__Expr_method_call__item___0 : expr -> expr_method_call) =
  fun projectee -> match projectee with | Expr_method_call _0 -> _0
let (uu___is_Expr_cast : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_cast _0 -> true | uu___ -> false
let (__proj__Expr_cast__item___0 : expr -> expr_cast) =
  fun projectee -> match projectee with | Expr_cast _0 -> _0
let (uu___is_Expr_range : expr -> Prims.bool) =
  fun projectee ->
    match projectee with | Expr_range _0 -> true | uu___ -> false
let (__proj__Expr_range__item___0 : expr -> expr_range) =
  fun projectee -> match projectee with | Expr_range _0 -> _0
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
let (__proj__Mkexpr_index__item__expr_index_base : expr_index -> expr) =
  fun projectee ->
    match projectee with
    | { expr_index_base; expr_index_index;_} -> expr_index_base
let (__proj__Mkexpr_index__item__expr_index_index : expr_index -> expr) =
  fun projectee ->
    match projectee with
    | { expr_index_base; expr_index_index;_} -> expr_index_index
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
let (__proj__Mkexpr_repeat__item__expr_repeat_elem : expr_repeat -> expr) =
  fun projectee ->
    match projectee with
    | { expr_repeat_elem; expr_repeat_len;_} -> expr_repeat_elem
let (__proj__Mkexpr_repeat__item__expr_repeat_len : expr_repeat -> expr) =
  fun projectee ->
    match projectee with
    | { expr_repeat_elem; expr_repeat_len;_} -> expr_repeat_len
let (__proj__Mkexpr_reference__item__expr_reference_is_mut :
  expr_reference -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { expr_reference_is_mut; expr_reference_expr;_} ->
        expr_reference_is_mut
let (__proj__Mkexpr_reference__item__expr_reference_expr :
  expr_reference -> expr) =
  fun projectee ->
    match projectee with
    | { expr_reference_is_mut; expr_reference_expr;_} -> expr_reference_expr
let (__proj__Mkarm__item__arm_pat : arm -> pat) =
  fun projectee -> match projectee with | { arm_pat; arm_body;_} -> arm_pat
let (__proj__Mkarm__item__arm_body : arm -> expr) =
  fun projectee -> match projectee with | { arm_pat; arm_body;_} -> arm_body
let (__proj__Mkexpr_match__item__expr_match_expr : expr_match -> expr) =
  fun projectee ->
    match projectee with
    | { expr_match_expr; expr_match_arms;_} -> expr_match_expr
let (__proj__Mkexpr_match__item__expr_match_arms :
  expr_match -> arm Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_match_expr; expr_match_arms;_} -> expr_match_arms
let (__proj__Mkexpr_field__item__expr_field_base : expr_field -> expr) =
  fun projectee ->
    match projectee with
    | { expr_field_base; expr_field_member; expr_field_named;_} ->
        expr_field_base
let (__proj__Mkexpr_field__item__expr_field_member :
  expr_field -> Prims.string) =
  fun projectee ->
    match projectee with
    | { expr_field_base; expr_field_member; expr_field_named;_} ->
        expr_field_member
let (__proj__Mkexpr_field__item__expr_field_named : expr_field -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { expr_field_base; expr_field_member; expr_field_named;_} ->
        expr_field_named
let (__proj__Mkexpr_struct__item__expr_struct_path :
  expr_struct -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_struct_path; expr_struct_fields;_} -> expr_struct_path
let (__proj__Mkexpr_struct__item__expr_struct_fields :
  expr_struct -> field_val Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_struct_path; expr_struct_fields;_} -> expr_struct_fields
let (__proj__Mkfield_val__item__field_val_name : field_val -> Prims.string) =
  fun projectee ->
    match projectee with
    | { field_val_name; field_val_expr;_} -> field_val_name
let (__proj__Mkfield_val__item__field_val_expr : field_val -> expr) =
  fun projectee ->
    match projectee with
    | { field_val_name; field_val_expr;_} -> field_val_expr
let (__proj__Mkexpr_method_call__item__expr_method_call_receiver :
  expr_method_call -> expr) =
  fun projectee ->
    match projectee with
    | { expr_method_call_receiver; expr_method_call_name;
        expr_method_call_args;_} -> expr_method_call_receiver
let (__proj__Mkexpr_method_call__item__expr_method_call_name :
  expr_method_call -> Prims.string) =
  fun projectee ->
    match projectee with
    | { expr_method_call_receiver; expr_method_call_name;
        expr_method_call_args;_} -> expr_method_call_name
let (__proj__Mkexpr_method_call__item__expr_method_call_args :
  expr_method_call -> expr Prims.list) =
  fun projectee ->
    match projectee with
    | { expr_method_call_receiver; expr_method_call_name;
        expr_method_call_args;_} -> expr_method_call_args
let (__proj__Mkexpr_cast__item__expr_cast_expr : expr_cast -> expr) =
  fun projectee ->
    match projectee with
    | { expr_cast_expr; expr_cast_type;_} -> expr_cast_expr
let (__proj__Mkexpr_cast__item__expr_cast_type : expr_cast -> typ) =
  fun projectee ->
    match projectee with
    | { expr_cast_expr; expr_cast_type;_} -> expr_cast_type
let (__proj__Mkexpr_range__item__expr_range_start :
  expr_range -> expr FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { expr_range_start; expr_range_limits; expr_range_end;_} ->
        expr_range_start
let (__proj__Mkexpr_range__item__expr_range_limits :
  expr_range -> range_limits) =
  fun projectee ->
    match projectee with
    | { expr_range_start; expr_range_limits; expr_range_end;_} ->
        expr_range_limits
let (__proj__Mkexpr_range__item__expr_range_end :
  expr_range -> expr FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { expr_range_start; expr_range_limits; expr_range_end;_} ->
        expr_range_end
let (uu___is_RangeLimitsHalfOpen : range_limits -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeLimitsHalfOpen -> true | uu___ -> false
let (uu___is_RangeLimitsClosed : range_limits -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeLimitsClosed -> true | uu___ -> false
let (__proj__Mklocal_stmt__item__local_stmt_pat :
  local_stmt -> pat FStar_Pervasives_Native.option) =
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
let (uu___is_Typ_path : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_path _0 -> true | uu___ -> false
let (__proj__Typ_path__item___0 : typ -> path_segment Prims.list) =
  fun projectee -> match projectee with | Typ_path _0 -> _0
let (uu___is_Typ_reference : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_reference _0 -> true | uu___ -> false
let (__proj__Typ_reference__item___0 : typ -> typ_reference) =
  fun projectee -> match projectee with | Typ_reference _0 -> _0
let (uu___is_Typ_slice : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_slice _0 -> true | uu___ -> false
let (__proj__Typ_slice__item___0 : typ -> typ) =
  fun projectee -> match projectee with | Typ_slice _0 -> _0
let (uu___is_Typ_array : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_array _0 -> true | uu___ -> false
let (__proj__Typ_array__item___0 : typ -> typ_array) =
  fun projectee -> match projectee with | Typ_array _0 -> _0
let (uu___is_Typ_unit : typ -> Prims.bool) =
  fun projectee -> match projectee with | Typ_unit -> true | uu___ -> false
let (uu___is_Typ_infer : typ -> Prims.bool) =
  fun projectee -> match projectee with | Typ_infer -> true | uu___ -> false
let (uu___is_Typ_fn : typ -> Prims.bool) =
  fun projectee -> match projectee with | Typ_fn _0 -> true | uu___ -> false
let (__proj__Typ_fn__item___0 : typ -> typ_fn) =
  fun projectee -> match projectee with | Typ_fn _0 -> _0
let (uu___is_Typ_tuple : typ -> Prims.bool) =
  fun projectee ->
    match projectee with | Typ_tuple _0 -> true | uu___ -> false
let (__proj__Typ_tuple__item___0 : typ -> typ Prims.list) =
  fun projectee -> match projectee with | Typ_tuple _0 -> _0
let (__proj__Mktyp_reference__item__typ_ref_mut :
  typ_reference -> Prims.bool) =
  fun projectee ->
    match projectee with | { typ_ref_mut; typ_ref_typ;_} -> typ_ref_mut
let (__proj__Mktyp_reference__item__typ_ref_typ : typ_reference -> typ) =
  fun projectee ->
    match projectee with | { typ_ref_mut; typ_ref_typ;_} -> typ_ref_typ
let (__proj__Mkpath_segment__item__path_segment_name :
  path_segment -> Prims.string) =
  fun projectee ->
    match projectee with
    | { path_segment_name; path_segment_generic_args;_} -> path_segment_name
let (__proj__Mkpath_segment__item__path_segment_generic_args :
  path_segment -> typ Prims.list) =
  fun projectee ->
    match projectee with
    | { path_segment_name; path_segment_generic_args;_} ->
        path_segment_generic_args
let (__proj__Mktyp_array__item__typ_array_elem : typ_array -> typ) =
  fun projectee ->
    match projectee with
    | { typ_array_elem; typ_array_len;_} -> typ_array_elem
let (__proj__Mktyp_array__item__typ_array_len : typ_array -> expr) =
  fun projectee ->
    match projectee with
    | { typ_array_elem; typ_array_len;_} -> typ_array_len
let (__proj__Mktyp_fn__item__typ_fn_args : typ_fn -> typ Prims.list) =
  fun projectee ->
    match projectee with | { typ_fn_args; typ_fn_ret;_} -> typ_fn_args
let (__proj__Mktyp_fn__item__typ_fn_ret : typ_fn -> typ) =
  fun projectee ->
    match projectee with | { typ_fn_args; typ_fn_ret;_} -> typ_fn_ret
type fn_arg =
  | Fn_arg_pat of pat_typ 
let (uu___is_Fn_arg_pat : fn_arg -> Prims.bool) = fun projectee -> true
let (__proj__Fn_arg_pat__item___0 : fn_arg -> pat_typ) =
  fun projectee -> match projectee with | Fn_arg_pat _0 -> _0
type generic_type_param =
  {
  generic_type_param_name: Prims.string ;
  generic_type_param_trait_bounds: Prims.string Prims.list Prims.list }
let (__proj__Mkgeneric_type_param__item__generic_type_param_name :
  generic_type_param -> Prims.string) =
  fun projectee ->
    match projectee with
    | { generic_type_param_name; generic_type_param_trait_bounds;_} ->
        generic_type_param_name
let (__proj__Mkgeneric_type_param__item__generic_type_param_trait_bounds :
  generic_type_param -> Prims.string Prims.list Prims.list) =
  fun projectee ->
    match projectee with
    | { generic_type_param_name; generic_type_param_trait_bounds;_} ->
        generic_type_param_trait_bounds
type generic_param =
  | Generic_type_param of generic_type_param 
let (uu___is_Generic_type_param : generic_param -> Prims.bool) =
  fun projectee -> true
let (__proj__Generic_type_param__item___0 :
  generic_param -> generic_type_param) =
  fun projectee -> match projectee with | Generic_type_param _0 -> _0
type fn_signature =
  {
  fn_const: Prims.bool ;
  fn_name: Prims.string ;
  fn_generics: generic_param Prims.list ;
  fn_args: fn_arg Prims.list ;
  fn_ret_t: typ }
let (__proj__Mkfn_signature__item__fn_const : fn_signature -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { fn_const; fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_const
let (__proj__Mkfn_signature__item__fn_name : fn_signature -> Prims.string) =
  fun projectee ->
    match projectee with
    | { fn_const; fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_name
let (__proj__Mkfn_signature__item__fn_generics :
  fn_signature -> generic_param Prims.list) =
  fun projectee ->
    match projectee with
    | { fn_const; fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_generics
let (__proj__Mkfn_signature__item__fn_args :
  fn_signature -> fn_arg Prims.list) =
  fun projectee ->
    match projectee with
    | { fn_const; fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_args
let (__proj__Mkfn_signature__item__fn_ret_t : fn_signature -> typ) =
  fun projectee ->
    match projectee with
    | { fn_const; fn_name; fn_generics; fn_args; fn_ret_t;_} -> fn_ret_t
type fn = {
  fn_sig: fn_signature ;
  fn_body: stmt Prims.list }
let (__proj__Mkfn__item__fn_sig : fn -> fn_signature) =
  fun projectee -> match projectee with | { fn_sig; fn_body;_} -> fn_sig
let (__proj__Mkfn__item__fn_body : fn -> stmt Prims.list) =
  fun projectee -> match projectee with | { fn_sig; fn_body;_} -> fn_body
type field_typ = {
  field_typ_name: Prims.string ;
  field_typ_typ: typ }
let (__proj__Mkfield_typ__item__field_typ_name : field_typ -> Prims.string) =
  fun projectee ->
    match projectee with
    | { field_typ_name; field_typ_typ;_} -> field_typ_name
let (__proj__Mkfield_typ__item__field_typ_typ : field_typ -> typ) =
  fun projectee ->
    match projectee with
    | { field_typ_name; field_typ_typ;_} -> field_typ_typ
type attribute =
  | Attr_derive of Prims.string 
let (uu___is_Attr_derive : attribute -> Prims.bool) = fun projectee -> true
let (__proj__Attr_derive__item___0 : attribute -> Prims.string) =
  fun projectee -> match projectee with | Attr_derive _0 -> _0
type item_struct =
  {
  item_struct_attrs: attribute Prims.list ;
  item_struct_name: Prims.string ;
  item_struct_generics: generic_param Prims.list ;
  item_struct_fields: field_typ Prims.list }
let (__proj__Mkitem_struct__item__item_struct_attrs :
  item_struct -> attribute Prims.list) =
  fun projectee ->
    match projectee with
    | { item_struct_attrs; item_struct_name; item_struct_generics;
        item_struct_fields;_} -> item_struct_attrs
let (__proj__Mkitem_struct__item__item_struct_name :
  item_struct -> Prims.string) =
  fun projectee ->
    match projectee with
    | { item_struct_attrs; item_struct_name; item_struct_generics;
        item_struct_fields;_} -> item_struct_name
let (__proj__Mkitem_struct__item__item_struct_generics :
  item_struct -> generic_param Prims.list) =
  fun projectee ->
    match projectee with
    | { item_struct_attrs; item_struct_name; item_struct_generics;
        item_struct_fields;_} -> item_struct_generics
let (__proj__Mkitem_struct__item__item_struct_fields :
  item_struct -> field_typ Prims.list) =
  fun projectee ->
    match projectee with
    | { item_struct_attrs; item_struct_name; item_struct_generics;
        item_struct_fields;_} -> item_struct_fields
type item_type =
  {
  item_type_name: Prims.string ;
  item_type_generics: generic_param Prims.list ;
  item_type_typ: typ }
let (__proj__Mkitem_type__item__item_type_name : item_type -> Prims.string) =
  fun projectee ->
    match projectee with
    | { item_type_name; item_type_generics; item_type_typ;_} ->
        item_type_name
let (__proj__Mkitem_type__item__item_type_generics :
  item_type -> generic_param Prims.list) =
  fun projectee ->
    match projectee with
    | { item_type_name; item_type_generics; item_type_typ;_} ->
        item_type_generics
let (__proj__Mkitem_type__item__item_type_typ : item_type -> typ) =
  fun projectee ->
    match projectee with
    | { item_type_name; item_type_generics; item_type_typ;_} -> item_type_typ
type enum_variant =
  {
  enum_variant_name: Prims.string ;
  enum_variant_fields: typ Prims.list }
let (__proj__Mkenum_variant__item__enum_variant_name :
  enum_variant -> Prims.string) =
  fun projectee ->
    match projectee with
    | { enum_variant_name; enum_variant_fields;_} -> enum_variant_name
let (__proj__Mkenum_variant__item__enum_variant_fields :
  enum_variant -> typ Prims.list) =
  fun projectee ->
    match projectee with
    | { enum_variant_name; enum_variant_fields;_} -> enum_variant_fields
type item_enum =
  {
  item_enum_attrs: attribute Prims.list ;
  item_enum_name: Prims.string ;
  item_enum_generics: generic_param Prims.list ;
  item_enum_variants: enum_variant Prims.list }
let (__proj__Mkitem_enum__item__item_enum_attrs :
  item_enum -> attribute Prims.list) =
  fun projectee ->
    match projectee with
    | { item_enum_attrs; item_enum_name; item_enum_generics;
        item_enum_variants;_} -> item_enum_attrs
let (__proj__Mkitem_enum__item__item_enum_name : item_enum -> Prims.string) =
  fun projectee ->
    match projectee with
    | { item_enum_attrs; item_enum_name; item_enum_generics;
        item_enum_variants;_} -> item_enum_name
let (__proj__Mkitem_enum__item__item_enum_generics :
  item_enum -> generic_param Prims.list) =
  fun projectee ->
    match projectee with
    | { item_enum_attrs; item_enum_name; item_enum_generics;
        item_enum_variants;_} -> item_enum_generics
let (__proj__Mkitem_enum__item__item_enum_variants :
  item_enum -> enum_variant Prims.list) =
  fun projectee ->
    match projectee with
    | { item_enum_attrs; item_enum_name; item_enum_generics;
        item_enum_variants;_} -> item_enum_variants
type item_static =
  {
  item_static_name: Prims.string ;
  item_static_typ: typ ;
  item_static_init: expr }
let (__proj__Mkitem_static__item__item_static_name :
  item_static -> Prims.string) =
  fun projectee ->
    match projectee with
    | { item_static_name; item_static_typ; item_static_init;_} ->
        item_static_name
let (__proj__Mkitem_static__item__item_static_typ : item_static -> typ) =
  fun projectee ->
    match projectee with
    | { item_static_name; item_static_typ; item_static_init;_} ->
        item_static_typ
let (__proj__Mkitem_static__item__item_static_init : item_static -> expr) =
  fun projectee ->
    match projectee with
    | { item_static_name; item_static_typ; item_static_init;_} ->
        item_static_init
type item =
  | Item_fn of fn 
  | Item_struct of item_struct 
  | Item_type of item_type 
  | Item_enum of item_enum 
  | Item_static of item_static 
let (uu___is_Item_fn : item -> Prims.bool) =
  fun projectee -> match projectee with | Item_fn _0 -> true | uu___ -> false
let (__proj__Item_fn__item___0 : item -> fn) =
  fun projectee -> match projectee with | Item_fn _0 -> _0
let (uu___is_Item_struct : item -> Prims.bool) =
  fun projectee ->
    match projectee with | Item_struct _0 -> true | uu___ -> false
let (__proj__Item_struct__item___0 : item -> item_struct) =
  fun projectee -> match projectee with | Item_struct _0 -> _0
let (uu___is_Item_type : item -> Prims.bool) =
  fun projectee ->
    match projectee with | Item_type _0 -> true | uu___ -> false
let (__proj__Item_type__item___0 : item -> item_type) =
  fun projectee -> match projectee with | Item_type _0 -> _0
let (uu___is_Item_enum : item -> Prims.bool) =
  fun projectee ->
    match projectee with | Item_enum _0 -> true | uu___ -> false
let (__proj__Item_enum__item___0 : item -> item_enum) =
  fun projectee -> match projectee with | Item_enum _0 -> _0
let (uu___is_Item_static : item -> Prims.bool) =
  fun projectee ->
    match projectee with | Item_static _0 -> true | uu___ -> false
let (__proj__Item_static__item___0 : item -> item_static) =
  fun projectee -> match projectee with | Item_static _0 -> _0
type file = {
  file_name: Prims.string ;
  file_items: item Prims.list }
let (__proj__Mkfile__item__file_name : file -> Prims.string) =
  fun projectee ->
    match projectee with | { file_name; file_items;_} -> file_name
let (__proj__Mkfile__item__file_items : file -> item Prims.list) =
  fun projectee ->
    match projectee with | { file_name; file_items;_} -> file_items
let (vec_new_fn : Prims.string) = "vec_new"
let (panic_fn : Prims.string) = "panic"
let (mk_scalar_typ : Prims.string -> typ) =
  fun name ->
    Typ_path [{ path_segment_name = name; path_segment_generic_args = [] }]
let (mk_ref_typ : Prims.bool -> typ -> typ) =
  fun is_mut ->
    fun t -> Typ_reference { typ_ref_mut = is_mut; typ_ref_typ = t }
let (mk_box_typ : typ -> typ) =
  fun t ->
    Typ_path
      [{ path_segment_name = "std"; path_segment_generic_args = [] };
      { path_segment_name = "boxed"; path_segment_generic_args = [] };
      { path_segment_name = "Box"; path_segment_generic_args = [t] }]
let (mk_slice_typ : typ -> typ) = fun t -> Typ_slice t
let (mk_vec_typ : typ -> typ) =
  fun t ->
    Typ_path
      [{ path_segment_name = "std"; path_segment_generic_args = [] };
      { path_segment_name = "vec"; path_segment_generic_args = [] };
      { path_segment_name = "Vec"; path_segment_generic_args = [t] }]
let (mk_mutex_typ : typ -> typ) =
  fun t ->
    Typ_path
      [{ path_segment_name = "std"; path_segment_generic_args = [] };
      { path_segment_name = "sync"; path_segment_generic_args = [] };
      { path_segment_name = "Mutex"; path_segment_generic_args = [t] }]
let (mk_option_typ : typ -> typ) =
  fun t ->
    Typ_path
      [{ path_segment_name = "std"; path_segment_generic_args = [] };
      { path_segment_name = "option"; path_segment_generic_args = [] };
      { path_segment_name = "Option"; path_segment_generic_args = [t] }]
let (mk_array_typ : typ -> expr -> typ) =
  fun t -> fun len -> Typ_array { typ_array_elem = t; typ_array_len = len }
let (mk_named_typ :
  Prims.string Prims.list -> Prims.string -> typ Prims.list -> typ) =
  fun path ->
    fun s ->
      fun generic_args ->
        let path1 =
          FStarC_Compiler_List.map
            (fun s1 ->
               { path_segment_name = s1; path_segment_generic_args = [] })
            path in
        let s1 =
          { path_segment_name = s; path_segment_generic_args = generic_args } in
        Typ_path (FStar_List_Tot_Base.append path1 [s1])
let (mk_fn_typ : typ Prims.list -> typ -> typ) =
  fun typ_fn_args -> fun typ_fn_ret -> Typ_fn { typ_fn_args; typ_fn_ret }
let (mk_tuple_typ : typ Prims.list -> typ) = fun l -> Typ_tuple l
let (mk_expr_path_singl : Prims.string -> expr) =
  fun s ->
    Expr_path [{ path_segment_name = s; path_segment_generic_args = [] }]
let (mk_expr_path : Prims.string Prims.list -> expr) =
  fun l ->
    let uu___ =
      FStarC_Compiler_List.map
        (fun s -> { path_segment_name = s; path_segment_generic_args = [] })
        l in
    Expr_path uu___
let (mk_lit_bool : Prims.bool -> expr) = fun b -> Expr_lit (Lit_bool b)
let (mk_binop : expr -> binop -> expr -> expr) =
  fun l ->
    fun op ->
      fun r ->
        Expr_binop
          { expr_bin_left = l; expr_bin_op = op; expr_bin_right = r }
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
let (mk_expr_index : expr -> expr -> expr) =
  fun expr_index_base ->
    fun expr_index_index -> Expr_index { expr_index_base; expr_index_index }
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
let (mk_repeat : expr -> expr -> expr) =
  fun expr_repeat_elem ->
    fun expr_repeat_len -> Expr_repeat { expr_repeat_elem; expr_repeat_len }
let (mk_reference_expr : Prims.bool -> expr -> expr) =
  fun expr_reference_is_mut ->
    fun expr_reference_expr ->
      Expr_reference { expr_reference_is_mut; expr_reference_expr }
let (mk_pat_ident : Prims.string -> pat) =
  fun path -> Pat_ident { pat_name = path; by_ref = false; is_mut = true }
let (mk_pat_ts :
  Prims.string Prims.list -> Prims.string -> pat Prims.list -> pat) =
  fun path ->
    fun s ->
      fun pat_ts_elems ->
        if (FStarC_Compiler_List.length pat_ts_elems) = Prims.int_zero
        then
          (if (FStarC_Compiler_List.length path) = Prims.int_zero
           then Pat_ident { pat_name = s; by_ref = false; is_mut = false }
           else
             (let uu___1 =
                FStarC_Compiler_List.map
                  (fun s1 ->
                     { path_segment_name = s1; path_segment_generic_args = []
                     }) (FStar_List_Tot_Base.append path [s]) in
              Pat_path uu___1))
        else
          (let uu___1 =
             let uu___2 =
               FStarC_Compiler_List.map
                 (fun s1 ->
                    { path_segment_name = s1; path_segment_generic_args = []
                    }) (FStar_List_Tot_Base.append path [s]) in
             { pat_ts_path = uu___2; pat_ts_elems } in
           Pat_tuple_struct uu___1)
let (mk_pat_struct : Prims.string -> (Prims.string * pat) Prims.list -> pat)
  =
  fun pat_struct_path ->
    fun pats ->
      let uu___ =
        let uu___1 =
          FStarC_Compiler_List.map
            (fun uu___2 ->
               match uu___2 with
               | (s, p) -> { field_pat_name = s; field_pat_pat = p }) pats in
        { pat_struct_path; pat_struct_fields = uu___1 } in
      Pat_struct uu___
let (mk_pat_tuple : pat Prims.list -> pat) = fun l -> Pat_tuple l
let (mk_arm : pat -> expr -> arm) =
  fun arm_pat -> fun arm_body -> { arm_pat; arm_body }
let (mk_match : expr -> arm Prims.list -> expr) =
  fun expr_match_expr ->
    fun expr_match_arms -> Expr_match { expr_match_expr; expr_match_arms }
let (mk_expr_field : expr -> Prims.string -> expr) =
  fun base ->
    fun f ->
      Expr_field
        {
          expr_field_base = base;
          expr_field_member = f;
          expr_field_named = true
        }
let (mk_expr_field_unnamed : expr -> Prims.int -> expr) =
  fun base ->
    fun i ->
      Expr_field
        {
          expr_field_base = base;
          expr_field_member = (Prims.string_of_int i);
          expr_field_named = false
        }
let (mk_expr_struct :
  Prims.string Prims.list -> (Prims.string * expr) Prims.list -> expr) =
  fun path ->
    fun fields ->
      let uu___ =
        let uu___1 =
          FStarC_Compiler_List.map
            (fun uu___2 ->
               match uu___2 with
               | (f, e) -> { field_val_name = f; field_val_expr = e }) fields in
        { expr_struct_path = path; expr_struct_fields = uu___1 } in
      Expr_struct uu___
let (mk_expr_tuple : expr Prims.list -> expr) = fun l -> Expr_tuple l
let (mk_mem_replace : typ -> expr -> expr -> expr) =
  fun t ->
    fun e ->
      fun new_v ->
        mk_call
          (Expr_path
             [{ path_segment_name = "std"; path_segment_generic_args = [] };
             { path_segment_name = "mem"; path_segment_generic_args = [] };
             { path_segment_name = "replace"; path_segment_generic_args = [t]
             }]) [e; new_v]
let (mk_method_call : expr -> Prims.string -> expr Prims.list -> expr) =
  fun receiver ->
    fun name ->
      fun args ->
        Expr_method_call
          {
            expr_method_call_receiver = receiver;
            expr_method_call_name = name;
            expr_method_call_args = args
          }
let (mk_cast : expr -> typ -> expr) =
  fun e -> fun ty -> Expr_cast { expr_cast_expr = e; expr_cast_type = ty }
let (mk_range :
  expr FStar_Pervasives_Native.option ->
    range_limits -> expr FStar_Pervasives_Native.option -> expr)
  =
  fun s ->
    fun l ->
      fun e ->
        Expr_range
          { expr_range_start = s; expr_range_limits = l; expr_range_end = e }
let (mk_new_mutex : expr -> expr) =
  fun e ->
    let uu___ = mk_expr_path ["std"; "sync"; "Mutex"; "new"] in
    mk_call uu___ [e]
let (mk_lock_mutex : expr -> expr) =
  fun e ->
    let e_lock = mk_method_call e "lock" [] in
    mk_method_call e_lock "unwrap" []
let (mk_unlock_mutex : expr -> expr) =
  fun e ->
    let uu___ = mk_expr_path ["std"; "mem"; "drop"] in mk_call uu___ [e]
let (mk_scalar_fn_arg : Prims.string -> Prims.bool -> typ -> fn_arg) =
  fun name ->
    fun is_mut ->
      fun t ->
        Fn_arg_pat
          {
            pat_typ_pat =
              (Pat_ident { pat_name = name; by_ref = false; is_mut });
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
let (mk_generic_type_param :
  Prims.string -> Prims.string Prims.list Prims.list -> generic_type_param) =
  fun generic_type_param_name ->
    fun generic_type_param_trait_bounds ->
      { generic_type_param_name; generic_type_param_trait_bounds }
let (mk_fn_signature :
  Prims.bool ->
    Prims.string ->
      generic_type_param Prims.list ->
        fn_arg Prims.list -> typ -> fn_signature)
  =
  fun fn_const ->
    fun fn_name ->
      fun fn_generics ->
        fun fn_args ->
          fun fn_ret_t ->
            let fn_generics1 =
              FStarC_Compiler_List.map
                (fun uu___ -> Generic_type_param uu___) fn_generics in
            {
              fn_const;
              fn_name;
              fn_generics = fn_generics1;
              fn_args;
              fn_ret_t
            }
let (mk_local_stmt :
  Prims.string FStar_Pervasives_Native.option ->
    typ FStar_Pervasives_Native.option -> Prims.bool -> expr -> stmt)
  =
  fun name ->
    fun t ->
      fun is_mut ->
        fun init ->
          Stmt_local
            {
              local_stmt_pat =
                (match name with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some name1 ->
                     let p =
                       Pat_ident { pat_name = name1; by_ref = false; is_mut } in
                     (match t with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.Some p
                      | FStar_Pervasives_Native.Some t1 ->
                          FStar_Pervasives_Native.Some
                            (Pat_typ { pat_typ_pat = p; pat_typ_typ = t1 })));
              local_stmt_init = (FStar_Pervasives_Native.Some init)
            }
let (mk_fn : fn_signature -> stmt Prims.list -> fn) =
  fun fn_sig -> fun fn_body -> { fn_sig; fn_body }
let (mk_derive_attr : Prims.string -> attribute) = fun s -> Attr_derive s
let (mk_item_struct :
  attribute Prims.list ->
    Prims.string ->
      generic_type_param Prims.list ->
        (Prims.string * typ) Prims.list -> item)
  =
  fun attrs ->
    fun name ->
      fun generics ->
        fun fields ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_List.map
                (fun uu___2 -> Generic_type_param uu___2) generics in
            let uu___2 =
              FStarC_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (f, t) -> { field_typ_name = f; field_typ_typ = t })
                fields in
            {
              item_struct_attrs = attrs;
              item_struct_name = name;
              item_struct_generics = uu___1;
              item_struct_fields = uu___2
            } in
          Item_struct uu___
let (mk_item_type :
  Prims.string -> generic_type_param Prims.list -> typ -> item) =
  fun name ->
    fun generics ->
      fun t ->
        let uu___ =
          let uu___1 =
            FStarC_Compiler_List.map
              (fun uu___2 -> Generic_type_param uu___2) generics in
          {
            item_type_name = name;
            item_type_generics = uu___1;
            item_type_typ = t
          } in
        Item_type uu___
let (mk_item_enum :
  attribute Prims.list ->
    Prims.string ->
      generic_type_param Prims.list ->
        (Prims.string * typ Prims.list) Prims.list -> item)
  =
  fun attrs ->
    fun name ->
      fun generics ->
        fun variants ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_List.map
                (fun uu___2 -> Generic_type_param uu___2) generics in
            let uu___2 =
              FStarC_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (v, typs) ->
                       { enum_variant_name = v; enum_variant_fields = typs })
                variants in
            {
              item_enum_attrs = attrs;
              item_enum_name = name;
              item_enum_generics = uu___1;
              item_enum_variants = uu___2
            } in
          Item_enum uu___
let (mk_item_static : Prims.string -> typ -> expr -> item) =
  fun name ->
    fun t ->
      fun init ->
        Item_static
          {
            item_static_name = name;
            item_static_typ = t;
            item_static_init = init
          }
let (mk_file : Prims.string -> item Prims.list -> file) =
  fun file_name -> fun file_items -> { file_name; file_items }