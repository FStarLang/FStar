open Prims
type version = Prims.int
let current_version : version= Prims.of_int 32
type program = FStarC_Extraction_KrmlAst.decl Prims.list
type file = (Prims.string * program)
type binary_format = (version * file Prims.list)
let translate_decl_accum :
  FStarC_Extraction_KrmlAst.decl Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let krml_current_decl :
  FStarC_Extraction_ML_Syntax.mlident FStar_Pervasives_Native.option
    FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let fst3 (uu___ : ('uuuuu * 'uuuuu1 * 'uuuuu2)) : 'uuuuu=
  match uu___ with | (x, uu___1, uu___2) -> x
let snd3 (uu___ : ('uuuuu * 'uuuuu1 * 'uuuuu2)) : 'uuuuu1=
  match uu___ with | (uu___1, x, uu___2) -> x
let thd3 (uu___ : ('uuuuu * 'uuuuu1 * 'uuuuu2)) : 'uuuuu2=
  match uu___ with | (uu___1, uu___2, x) -> x
let mk_width (uu___ : Prims.string) :
  FStarC_Extraction_KrmlAst.width FStar_Pervasives_Native.option=
  match uu___ with
  | "UInt8" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.UInt8
  | "UInt16" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.UInt16
  | "UInt32" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.UInt32
  | "UInt64" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.UInt64
  | "Int8" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Int8
  | "Int16" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Int16
  | "Int32" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Int32
  | "Int64" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Int64
  | "SizeT" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.SizeT
  | "PtrdiffT" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.PtrdiffT
  | "Float32" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Float32
  | "Float64" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Float64
  | uu___1 -> FStar_Pervasives_Native.None
let is_float_width
  (uu___ : FStarC_Extraction_KrmlAst.width FStar_Pervasives_Native.option) :
  Prims.bool=
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Extraction_KrmlAst.Float32) -> true
  | FStar_Pervasives_Native.Some (FStarC_Extraction_KrmlAst.Float64) -> true
  | uu___1 -> false
let valid_float_literal (s : Prims.string) : Prims.bool=
  let is_digit c =
    let i = FStarC_Util.int_of_char c in
    (i >= (Prims.of_int 48)) && (i <= (Prims.of_int 57)) in
  let rec consume_digits cs =
    match cs with
    | c::cs' when is_digit c -> consume_digits cs'
    | uu___ -> cs in
  let has_digits cs = (consume_digits cs) <> cs in
  let cs =
    match FStar_String.list_of_string s with
    | 43::cs1 -> cs1
    | 45::cs1 -> cs1
    | cs1 -> cs1 in
  let before_dot = consume_digits cs in
  let uu___ =
    match before_dot with
    | 46::cs' ->
        let after_dot = consume_digits cs' in
        (after_dot, ((before_dot <> cs) || (after_dot <> cs')))
    | uu___1 -> (before_dot, (before_dot <> cs)) in
  match uu___ with
  | (after_mantissa, has_mantissa_digit) ->
      if Prims.not has_mantissa_digit
      then false
      else
        (match after_mantissa with
         | [] -> true
         | 101::exp ->
             let exp1 =
               match exp with
               | 43::exp2 -> exp2
               | 45::exp2 -> exp2
               | exp2 -> exp2 in
             (has_digits exp1) && ((consume_digits exp1) = [])
         | 69::exp ->
             let exp1 =
               match exp with
               | 43::exp2 -> exp2
               | 45::exp2 -> exp2
               | exp2 -> exp2 in
             (has_digits exp1) && ((consume_digits exp1) = [])
         | uu___1 -> false)
let mk_bool_op (uu___ : Prims.string) :
  FStarC_Extraction_KrmlAst.op FStar_Pervasives_Native.option=
  match uu___ with
  | "not" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Not
  | "op_Amp_Amp" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.And
  | "op_Bar_Bar" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Or
  | "op_Equals" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Eq
  | "op_Less_Greater" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Neq
  | uu___1 -> FStar_Pervasives_Native.None
let is_bool_op (op : Prims.string) : Prims.bool=
  (mk_bool_op op) <> FStar_Pervasives_Native.None
let krml_compat_name (n : (Prims.string Prims.list * Prims.string)) :
  (Prims.string Prims.list * Prims.string)=
  match n with
  | ("Prims"::[], op) ->
      let op1 =
        match op with
        | "op_Plus" -> "op_Addition"
        | "op_Minus" -> "op_Subtraction"
        | "op_Tilde_Minus" -> "op_Minus"
        | "op_Star" -> "op_Multiply"
        | "op_Slash" -> "op_Division"
        | "op_Percent" -> "op_Modulus"
        | "op_Less" -> "op_LessThan"
        | "op_Less_Equals" -> "op_LessThanOrEqual"
        | "op_Greater" -> "op_GreaterThan"
        | "op_Greater_Equals" -> "op_GreaterThanOrEqual"
        | op2 -> op2 in
      (["Prims"], op1)
  | ("Pulse"::"Lib"::"Slice"::[], op) ->
      let op1 =
        match op with
        | "op_Dot_Lparen_Rparen" -> "op_Array_Access"
        | "op_Dot_Lparen_Rparen_Less_Minus" -> "op_Array_Assignment"
        | op2 -> op2 in
      (["Pulse"; "Lib"; "Slice"], op1)
  | n1 -> n1
let krml_decl_name (module_name : Prims.string Prims.list) (n : Prims.string)
  : (Prims.string Prims.list * Prims.string)=
  krml_compat_name (module_name, n)
let mk_op (uu___ : Prims.string) :
  FStarC_Extraction_KrmlAst.op FStar_Pervasives_Native.option=
  match uu___ with
  | "add" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Add
  | "add_underspec" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Add
  | "add_mod" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.AddW
  | "sub" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Sub
  | "sub_underspec" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Sub
  | "sub_mod" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.SubW
  | "mul" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Mult
  | "mul_underspec" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Mult
  | "mul_mod" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.MultW
  | "div" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Div
  | "div_mod" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.DivW
  | "rem" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Mod
  | "logor" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BOr
  | "logxor" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BXor
  | "logand" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BAnd
  | "lognot" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BNot
  | "shift_right" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BShiftR
  | "shift_left" ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.BShiftL
  | "eq" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Eq
  | "ieee_eq" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Eq
  | "gt" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Gt
  | "gte" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Gte
  | "lt" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Lt
  | "lte" -> FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Lte
  | uu___1 -> FStar_Pervasives_Native.None
let is_op (op : Prims.string) : Prims.bool=
  (mk_op op) <> FStar_Pervasives_Native.None
let is_machine_int (m : Prims.string) : Prims.bool=
  (mk_width m) <> FStar_Pervasives_Native.None
type env =
  {
  uenv: FStarC_Extraction_ML_UEnv.uenv ;
  names: name Prims.list ;
  names_t: Prims.string Prims.list ;
  module_name: Prims.string Prims.list }
and name = {
  pretty: Prims.string }
let __proj__Mkenv__item__uenv (projectee : env) :
  FStarC_Extraction_ML_UEnv.uenv=
  match projectee with | { uenv; names; names_t; module_name;_} -> uenv
let __proj__Mkenv__item__names (projectee : env) : name Prims.list=
  match projectee with | { uenv; names; names_t; module_name;_} -> names
let __proj__Mkenv__item__names_t (projectee : env) : Prims.string Prims.list=
  match projectee with | { uenv; names; names_t; module_name;_} -> names_t
let __proj__Mkenv__item__module_name (projectee : env) :
  Prims.string Prims.list=
  match projectee with
  | { uenv; names; names_t; module_name;_} -> module_name
let __proj__Mkname__item__pretty (projectee : name) : Prims.string=
  match projectee with | { pretty;_} -> pretty
let empty (uenv : FStarC_Extraction_ML_UEnv.uenv)
  (module_name : Prims.string Prims.list) : env=
  { uenv; names = []; names_t = []; module_name }
let extend (env1 : env) (x : Prims.string) : env=
  {
    uenv = (env1.uenv);
    names = ({ pretty = x } :: (env1.names));
    names_t = (env1.names_t);
    module_name = (env1.module_name)
  }
let extend_t (env1 : env) (x : Prims.string) : env=
  {
    uenv = (env1.uenv);
    names = (env1.names);
    names_t = (x :: (env1.names_t));
    module_name = (env1.module_name)
  }
let find_name (env1 : env) (x : Prims.string) : name=
  let uu___ = FStarC_List.tryFind (fun name1 -> name1.pretty = x) env1.names in
  match uu___ with
  | FStar_Pervasives_Native.Some name1 -> name1
  | FStar_Pervasives_Native.None ->
      FStarC_Effect.failwith "internal error: name not found"
let find (env1 : env) (x : Prims.string) : Prims.int=
  try
    (fun uu___ ->
       match () with
       | () -> FStarC_List.index (fun name1 -> name1.pretty = x) env1.names)
      ()
  with
  | uu___ ->
      FStarC_Effect.failwith
        (FStarC_Format.fmt1 "Internal error: name not found %s\n" x)
let find_t (env1 : env) (x : Prims.string) : Prims.int=
  try
    (fun uu___ ->
       match () with
       | () -> FStarC_List.index (fun name1 -> name1 = x) env1.names_t) ()
  with
  | uu___ ->
      FStarC_Effect.failwith
        (FStarC_Format.fmt1 "Internal error: name not found %s\n" x)
let add_binders (env1 : env)
  (bs : FStarC_Extraction_ML_Syntax.mlbinder Prims.list) : env=
  FStarC_List.fold_left
    (fun env2 uu___ ->
       match uu___ with
       | { FStarC_Extraction_ML_Syntax.mlbinder_name = mlbinder_name;
           FStarC_Extraction_ML_Syntax.mlbinder_ty = uu___1;
           FStarC_Extraction_ML_Syntax.mlbinder_attrs = uu___2;_} ->
           extend env2 mlbinder_name) env1 bs
let list_elements (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_ML_Syntax.mlexpr Prims.list=
  let lopt = FStarC_Extraction_ML_Util.list_elements e in
  match lopt with
  | FStar_Pervasives_Native.None ->
      FStarC_Effect.failwith
        "Argument of FStar.Buffer.createL is not a list literal!"
  | FStar_Pervasives_Native.Some l -> l
let translate_flags (flags : FStarC_Extraction_ML_Syntax.meta Prims.list) :
  FStarC_Extraction_KrmlAst.flag Prims.list=
  FStarC_List.choose
    (fun uu___ ->
       match uu___ with
       | FStarC_Extraction_ML_Syntax.Private ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Private
       | FStarC_Extraction_ML_Syntax.NoExtract ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.WipeBody
       | FStarC_Extraction_ML_Syntax.CInline ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.CInline
       | FStarC_Extraction_ML_Syntax.CNoInline ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.CNoInline
       | FStarC_Extraction_ML_Syntax.Substitute ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Substitute
       | FStarC_Extraction_ML_Syntax.GCType ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.GCType
       | FStarC_Extraction_ML_Syntax.Comment s ->
           FStar_Pervasives_Native.Some (FStarC_Extraction_KrmlAst.Comment s)
       | FStarC_Extraction_ML_Syntax.StackInline ->
           FStar_Pervasives_Native.Some
             FStarC_Extraction_KrmlAst.MustDisappear
       | FStarC_Extraction_ML_Syntax.CConst s ->
           FStar_Pervasives_Native.Some (FStarC_Extraction_KrmlAst.Const s)
       | FStarC_Extraction_ML_Syntax.CPrologue s ->
           FStar_Pervasives_Native.Some
             (FStarC_Extraction_KrmlAst.Prologue s)
       | FStarC_Extraction_ML_Syntax.CEpilogue s ->
           FStar_Pervasives_Native.Some
             (FStarC_Extraction_KrmlAst.Epilogue s)
       | FStarC_Extraction_ML_Syntax.CAbstract ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Abstract
       | FStarC_Extraction_ML_Syntax.CIfDef ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.IfDef
       | FStarC_Extraction_ML_Syntax.CMacro ->
           FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.Macro
       | FStarC_Extraction_ML_Syntax.Deprecated s ->
           FStar_Pervasives_Native.Some
             (FStarC_Extraction_KrmlAst.Deprecated s)
       | uu___1 -> FStar_Pervasives_Native.None) flags
let translate_cc (flags : FStarC_Extraction_ML_Syntax.meta Prims.list) :
  FStarC_Extraction_KrmlAst.cc FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.choose
      (fun uu___1 ->
         match uu___1 with
         | FStarC_Extraction_ML_Syntax.CCConv s ->
             FStar_Pervasives_Native.Some s
         | uu___2 -> FStar_Pervasives_Native.None) flags in
  match uu___ with
  | "stdcall"::[] ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.StdCall
  | "fastcall"::[] ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.FastCall
  | "cdecl"::[] ->
      FStar_Pervasives_Native.Some FStarC_Extraction_KrmlAst.CDecl
  | uu___1 -> FStar_Pervasives_Native.None
let generate_is_null (t : FStarC_Extraction_KrmlAst.typ)
  (x : FStarC_Extraction_KrmlAst.expr) : FStarC_Extraction_KrmlAst.expr=
  let dummy = FStarC_Extraction_KrmlAst.UInt64 in
  FStarC_Extraction_KrmlAst.EApp
    ((FStarC_Extraction_KrmlAst.ETypApp
        ((FStarC_Extraction_KrmlAst.EOp (FStarC_Extraction_KrmlAst.Eq, dummy)),
          [FStarC_Extraction_KrmlAst.TBuf t])),
      [x; FStarC_Extraction_KrmlAst.EBufNull t])
exception NotSupportedByKrmlExtension 
let uu___is_NotSupportedByKrmlExtension (projectee : Prims.exn) : Prims.bool=
  true
type translate_type_without_decay_t =
  env -> FStarC_Extraction_ML_Syntax.mlty -> FStarC_Extraction_KrmlAst.typ
let ref_translate_type_without_decay :
  translate_type_without_decay_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref
    (fun uu___ uu___1 -> FStarC_Effect.raise NotSupportedByKrmlExtension)
let register_pre_translate_type_without_decay
  (f : translate_type_without_decay_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type_without_decay in
  let after e t =
    try (fun uu___ -> match () with | () -> f e t) ()
    with | NotSupportedByKrmlExtension -> before e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type_without_decay after
let register_post_translate_type_without_decay
  (f : translate_type_without_decay_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type_without_decay in
  let after e t =
    try (fun uu___ -> match () with | () -> before e t) ()
    with | NotSupportedByKrmlExtension -> f e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type_without_decay after
let translate_type_without_decay (env1 : env)
  (t : FStarC_Extraction_ML_Syntax.mlty) : FStarC_Extraction_KrmlAst.typ=
  let uu___ = FStarC_Effect.op_Bang ref_translate_type_without_decay in
  uu___ env1 t
type translate_type_t =
  env -> FStarC_Extraction_ML_Syntax.mlty -> FStarC_Extraction_KrmlAst.typ
let ref_translate_type : translate_type_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref
    (fun uu___ uu___1 -> FStarC_Effect.raise NotSupportedByKrmlExtension)
let register_pre_translate_type (f : translate_type_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type in
  let after e t =
    try (fun uu___ -> match () with | () -> f e t) ()
    with | NotSupportedByKrmlExtension -> before e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type after
let register_post_translate_type (f : translate_type_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type in
  let after e t =
    try (fun uu___ -> match () with | () -> before e t) ()
    with | NotSupportedByKrmlExtension -> f e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type after
let translate_type (env1 : env) (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_KrmlAst.typ=
  let uu___ = FStarC_Effect.op_Bang ref_translate_type in uu___ env1 t
type translate_expr_t =
  env -> FStarC_Extraction_ML_Syntax.mlexpr -> FStarC_Extraction_KrmlAst.expr
let ref_translate_expr : translate_expr_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref
    (fun uu___ uu___1 -> FStarC_Effect.raise NotSupportedByKrmlExtension)
let register_pre_translate_expr (f : translate_expr_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_expr in
  let after e t =
    try (fun uu___ -> match () with | () -> f e t) ()
    with | NotSupportedByKrmlExtension -> before e t in
  FStarC_Effect.op_Colon_Equals ref_translate_expr after
let register_post_translate_expr (f : translate_expr_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_expr in
  let after e t =
    try (fun uu___ -> match () with | () -> before e t) ()
    with | NotSupportedByKrmlExtension -> f e t in
  FStarC_Effect.op_Colon_Equals ref_translate_expr after
let translate_expr (env1 : env) (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_KrmlAst.expr=
  let uu___ = FStarC_Effect.op_Bang ref_translate_expr in uu___ env1 e
type translate_type_decl_t =
  env ->
    FStarC_Extraction_ML_Syntax.one_mltydecl ->
      FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option
let ref_translate_type_decl : translate_type_decl_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref
    (fun uu___ uu___1 -> FStarC_Effect.raise NotSupportedByKrmlExtension)
let register_pre_translate_type_decl (f : translate_type_decl_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type_decl in
  let after e t =
    try (fun uu___ -> match () with | () -> f e t) ()
    with | NotSupportedByKrmlExtension -> before e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type_decl after
let register_post_translate_type_decl (f : translate_type_decl_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_type_decl in
  let after e t =
    try (fun uu___ -> match () with | () -> before e t) ()
    with | NotSupportedByKrmlExtension -> f e t in
  FStarC_Effect.op_Colon_Equals ref_translate_type_decl after
let translate_type_decl (env1 : env)
  (ty : FStarC_Extraction_ML_Syntax.one_mltydecl) :
  FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option=
  if
    FStarC_List.mem FStarC_Extraction_ML_Syntax.NoExtract
      ty.FStarC_Extraction_ML_Syntax.tydecl_meta
  then FStar_Pervasives_Native.None
  else
    (let uu___ = FStarC_Effect.op_Bang ref_translate_type_decl in
     uu___ env1 ty)
type env_and_pat = (env * FStarC_Extraction_KrmlAst.pattern)
let rec translate_type_without_decay' (env1 : env)
  (t : FStarC_Extraction_ML_Syntax.mlty) : FStarC_Extraction_KrmlAst.typ=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Tuple [] ->
      FStarC_Extraction_KrmlAst.TAny
  | FStarC_Extraction_ML_Syntax.MLTY_Top -> FStarC_Extraction_KrmlAst.TAny
  | FStarC_Extraction_ML_Syntax.MLTY_Var name1 ->
      let uu___ = find_t env1 name1 in FStarC_Extraction_KrmlAst.TBound uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
      let uu___1 =
        let uu___2 = translate_type_without_decay env1 t1 in
        let uu___3 = translate_type_without_decay env1 t2 in (uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.TArrow uu___1
  | FStarC_Extraction_ML_Syntax.MLTY_Erased ->
      FStarC_Extraction_KrmlAst.TUnit
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit" ->
      FStarC_Extraction_KrmlAst.TUnit
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool" ->
      FStarC_Extraction_KrmlAst.TBool
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t")) when
      is_machine_int m ->
      let uu___ = FStarC_Option.must (mk_width m) in
      FStarC_Extraction_KrmlAst.TInt uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], ("FStar"::m::[], "t'")) when
      is_machine_int m ->
      let uu___ = FStarC_Option.must (mk_width m) in
      FStarC_Extraction_KrmlAst.TInt uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.Monotonic.HyperStack.mem"
      -> FStarC_Extraction_KrmlAst.TUnit
  | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::arg::uu___1::[], p) when
      ((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.Monotonic.HyperStack.s_mref")
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "FStar.Monotonic.HyperHeap.mrref"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.HyperStack.ST.m_rref"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.s_mref")
      ->
      let uu___2 = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TBuf uu___2
  | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::uu___::[], p) when
      (((((((((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                  "FStar.Monotonic.HyperStack.mreference")
                 ||
                 ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                    "FStar.Monotonic.HyperStack.mstackref"))
                ||
                ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                   "FStar.Monotonic.HyperStack.mref"))
               ||
               ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                  "FStar.Monotonic.HyperStack.mmmstackref"))
              ||
              ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                 "FStar.Monotonic.HyperStack.mmmref"))
             ||
             ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                "FStar.All.ref"))
            ||
            ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
               "FStar.HyperStack.ST.mreference"))
           ||
           ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
              "FStar.HyperStack.ST.mstackref"))
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "FStar.HyperStack.ST.mref"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.HyperStack.ST.mmmstackref"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.mmmref")
      ->
      let uu___1 = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TBuf uu___1
  | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::uu___::uu___1::[], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.Monotonic.Buffer.mbuffer"
      ->
      let uu___2 = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TBuf uu___2
  | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "LowStar.ConstBuffer.const_buffer")
        || false
      ->
      let uu___ = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TConstBuf uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
      (((((((((((((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                      "FStar.Buffer.buffer")
                     ||
                     ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                        "LowStar.Buffer.buffer"))
                    ||
                    ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                       "LowStar.ImmutableBuffer.ibuffer"))
                   ||
                   ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                      "LowStar.UninitializedBuffer.ubuffer"))
                  ||
                  ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                     "FStar.HyperStack.reference"))
                 ||
                 ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                    "FStar.HyperStack.stackref"))
                ||
                ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                   "FStar.HyperStack.ref"))
               ||
               ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                  "FStar.HyperStack.mmstackref"))
              ||
              ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                 "FStar.HyperStack.mmref"))
             ||
             ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
                "FStar.HyperStack.ST.reference"))
            ||
            ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
               "FStar.HyperStack.ST.stackref"))
           ||
           ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
              "FStar.HyperStack.ST.ref"))
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "FStar.HyperStack.ST.mmstackref"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.HyperStack.ST.mmref"))
        || false
      ->
      let uu___ = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TBuf uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::arg::[], p) when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.s_ref")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.s_ref")
      ->
      let uu___1 = translate_type_without_decay env1 arg in
      FStarC_Extraction_KrmlAst.TBuf uu___1
  | FStarC_Extraction_ML_Syntax.MLTY_Named (arg::[], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.Universe.raise_t"
      -> translate_type_without_decay env1 arg
  | FStarC_Extraction_ML_Syntax.MLTY_Named (uu___::[], p) when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased"
      -> FStarC_Extraction_KrmlAst.TAny
  | FStarC_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) ->
      FStarC_Extraction_KrmlAst.TQualified (path, type_name)
  | FStarC_Extraction_ML_Syntax.MLTY_Named (args, p) when
      (FStarC_Parser_Const_Tuples.get_tuple_tycon_arity
         (FStarC_Extraction_ML_Syntax.string_of_mlpath p))
        = (FStar_Pervasives_Native.Some (FStarC_List.length args))
      ->
      let uu___ = FStarC_List.map (translate_type_without_decay env1) args in
      FStarC_Extraction_KrmlAst.TTuple uu___
  | FStarC_Extraction_ML_Syntax.MLTY_Named (args, lid) ->
      if (match args with | hd::tl -> true | uu___ -> false)
      then
        let uu___ =
          let uu___1 =
            FStarC_List.map (translate_type_without_decay env1) args in
          (lid, uu___1) in
        FStarC_Extraction_KrmlAst.TApp uu___
      else FStarC_Extraction_KrmlAst.TQualified lid
  | FStarC_Extraction_ML_Syntax.MLTY_Tuple ts ->
      let uu___ = FStarC_List.map (translate_type_without_decay env1) ts in
      FStarC_Extraction_KrmlAst.TTuple uu___
and translate_type' (env1 : env) (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_KrmlAst.typ= translate_type_without_decay env1 t
and translate_binders (env1 : env)
  (bs : FStarC_Extraction_ML_Syntax.mlbinder Prims.list) :
  FStarC_Extraction_KrmlAst.binder Prims.list=
  FStarC_List.map (translate_binder env1) bs
and translate_binder (env1 : env) (b : FStarC_Extraction_ML_Syntax.mlbinder)
  : FStarC_Extraction_KrmlAst.binder=
  let uu___ = b in
  match uu___ with
  | { FStarC_Extraction_ML_Syntax.mlbinder_name = mlbinder_name;
      FStarC_Extraction_ML_Syntax.mlbinder_ty = mlbinder_ty;
      FStarC_Extraction_ML_Syntax.mlbinder_attrs = mlbinder_attrs;_} ->
      let uu___1 = translate_type env1 mlbinder_ty in
      {
        FStarC_Extraction_KrmlAst.name = mlbinder_name;
        FStarC_Extraction_KrmlAst.typ = uu___1;
        FStarC_Extraction_KrmlAst.mut = false;
        FStarC_Extraction_KrmlAst.meta = []
      }
and translate_expr' (env1 : env) (e : FStarC_Extraction_ML_Syntax.mlexpr) :
  FStarC_Extraction_KrmlAst.expr=
  match e.FStarC_Extraction_ML_Syntax.expr with
  | FStarC_Extraction_ML_Syntax.MLE_Tuple [] ->
      FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Extraction_ML_Syntax.MLE_Const c -> translate_constant c
  | FStarC_Extraction_ML_Syntax.MLE_Var name1 ->
      let uu___ = find env1 name1 in FStarC_Extraction_KrmlAst.EBound uu___
  | FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op) when
      (is_machine_int m) && (is_op op) ->
      let uu___ =
        let uu___1 = FStarC_Option.must (mk_op op) in
        let uu___2 = FStarC_Option.must (mk_width m) in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EOp uu___
  | FStarC_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op) when is_bool_op op
      ->
      let uu___ =
        let uu___1 = FStarC_Option.must (mk_bool_op op) in
        (uu___1, FStarC_Extraction_KrmlAst.Bool) in
      FStarC_Extraction_KrmlAst.EOp uu___
  | FStarC_Extraction_ML_Syntax.MLE_Name n ->
      FStarC_Extraction_KrmlAst.EQualified (krml_compat_name n)
  | FStarC_Extraction_ML_Syntax.MLE_Let
      ((flavor,
        { FStarC_Extraction_ML_Syntax.mllb_name = name1;
          FStarC_Extraction_ML_Syntax.mllb_tysc =
            FStar_Pervasives_Native.Some ([], typ);
          FStarC_Extraction_ML_Syntax.mllb_add_unit = add_unit;
          FStarC_Extraction_ML_Syntax.mllb_def = body;
          FStarC_Extraction_ML_Syntax.mllb_attrs = uu___;
          FStarC_Extraction_ML_Syntax.mllb_meta = flags;
          FStarC_Extraction_ML_Syntax.print_typ = print;_}::[]),
       continuation)
      ->
      let binder =
        let uu___1 = translate_type env1 typ in
        let uu___2 = translate_flags flags in
        {
          FStarC_Extraction_KrmlAst.name = name1;
          FStarC_Extraction_KrmlAst.typ = uu___1;
          FStarC_Extraction_KrmlAst.mut = false;
          FStarC_Extraction_KrmlAst.meta = uu___2
        } in
      let body1 = translate_expr env1 body in
      let env2 = extend env1 name1 in
      let continuation1 = translate_expr env2 continuation in
      FStarC_Extraction_KrmlAst.ELet (binder, body1, continuation1)
  | FStarC_Extraction_ML_Syntax.MLE_Match (expr, branches) ->
      let uu___ =
        let uu___1 = translate_expr env1 expr in
        let uu___2 = translate_branches env1 branches in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EMatch uu___
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            t::[]);
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_},
       arg::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Dyn.undyn" ->
      let uu___4 =
        let uu___5 = translate_expr env1 arg in
        let uu___6 = translate_type env1 t in (uu___5, uu___6) in
      FStarC_Extraction_KrmlAst.ECast uu___4
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       uu___5)
      when (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.admit"
      -> FStarC_Extraction_KrmlAst.EAbort
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            t::[]);
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_},
       {
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s);
         FStarC_Extraction_ML_Syntax.mlty = uu___4;
         FStarC_Extraction_ML_Syntax.loc = uu___5;_}::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.Failure.failwith"
      ->
      let uu___6 = let uu___7 = translate_type env1 t in (s, uu___7) in
      FStarC_Extraction_KrmlAst.EAbortT uu___6
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       arg::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "FStar.HyperStack.All.failwith")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.Error.unexpected"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.Error.unreachable")
      ->
      (match arg with
       | {
           FStarC_Extraction_ML_Syntax.expr =
             FStarC_Extraction_ML_Syntax.MLE_Const
             (FStarC_Extraction_ML_Syntax.MLC_String msg);
           FStarC_Extraction_ML_Syntax.mlty = uu___5;
           FStarC_Extraction_ML_Syntax.loc = uu___6;_} ->
           FStarC_Extraction_KrmlAst.EAbortS msg
       | uu___5 ->
           let print_nm = (["FStar"; "HyperStack"; "IO"], "print_string") in
           let print =
             FStarC_Extraction_ML_Syntax.with_ty
               FStarC_Extraction_ML_Syntax.MLTY_Top
               (FStarC_Extraction_ML_Syntax.MLE_Name print_nm) in
           let print1 =
             FStarC_Extraction_ML_Syntax.with_ty
               FStarC_Extraction_ML_Syntax.MLTY_Top
               (FStarC_Extraction_ML_Syntax.MLE_App (print, [arg])) in
           let t = translate_expr env1 print1 in
           FStarC_Extraction_KrmlAst.ESequence
             [t; FStarC_Extraction_KrmlAst.EAbort])
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "LowStar.ToFStarBuffer.new_to_old_st")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ToFStarBuffer.old_to_new_st")
      -> translate_expr env1 e1
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.Buffer.index")
           ||
           ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
              "FStar.Buffer.op_Dot_Lparen_Rparen"))
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "LowStar.Monotonic.Buffer.index"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.UninitializedBuffer.uindex"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ConstBuffer.index")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufRead uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.HyperStack.ST.op_Bang"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        (uu___6,
          (FStarC_Extraction_KrmlAst.EQualified (["C"], "_zero_for_deref"))) in
      FStarC_Extraction_KrmlAst.EBufRead uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       arg::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.Universe.raise_val"
      -> translate_expr env1 arg
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       arg::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.Universe.downgrade_val"
      -> translate_expr env1 arg
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "FStar.Buffer.create")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.malloca"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.ialloca")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        (FStarC_Extraction_KrmlAst.Stack, uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       elen::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.UninitializedBuffer.ualloca"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 elen in
        (FStarC_Extraction_KrmlAst.Stack, uu___6) in
      FStarC_Extraction_KrmlAst.EBufCreateNoInit uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       init::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.salloc")
        || false
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 init in
        (FStarC_Extraction_KrmlAst.Stack, uu___6,
          (FStarC_Extraction_KrmlAst.EConstant
             (FStarC_Extraction_KrmlAst.UInt32, "1"))) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e2::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "FStar.Buffer.createL")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.malloca_of_list"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.ialloca_of_list")
      ->
      let uu___5 =
        let uu___6 =
          let uu___7 = list_elements e2 in
          FStarC_List.map (translate_expr env1) uu___7 in
        (FStarC_Extraction_KrmlAst.Stack, uu___6) in
      FStarC_Extraction_KrmlAst.EBufCreateL uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _erid::e2::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "LowStar.Monotonic.Buffer.mgcmalloc_of_list")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.igcmalloc_of_list")
      ->
      let uu___5 =
        let uu___6 =
          let uu___7 = list_elements e2 in
          FStarC_List.map (translate_expr env1) uu___7 in
        (FStarC_Extraction_KrmlAst.Eternal, uu___6) in
      FStarC_Extraction_KrmlAst.EBufCreateL uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _rid::init::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.ralloc")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.ralloc_drgn")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 init in
        (FStarC_Extraction_KrmlAst.Eternal, uu___6,
          (FStarC_Extraction_KrmlAst.EConstant
             (FStarC_Extraction_KrmlAst.UInt32, "1"))) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _e0::e1::e2::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "FStar.Buffer.rcreate")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.mgcmalloc"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.igcmalloc")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        (FStarC_Extraction_KrmlAst.Eternal, uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       uu___5)
      when
      ((((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "LowStar.Monotonic.Buffer.mgcmalloc_and_blit")
            ||
            ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
               "LowStar.Monotonic.Buffer.mmalloc_and_blit"))
           ||
           ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
              "LowStar.Monotonic.Buffer.malloca_and_blit"))
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "LowStar.ImmutableBuffer.igcmalloc_and_blit"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.ImmutableBuffer.imalloc_and_blit"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.ialloca_and_blit")
      ->
      FStarC_Extraction_KrmlAst.EAbortS
        "alloc_and_blit family of functions are not yet supported downstream"
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _erid::elen::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.UninitializedBuffer.ugcmalloc"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 elen in
        (FStarC_Extraction_KrmlAst.Eternal, uu___6) in
      FStarC_Extraction_KrmlAst.EBufCreateNoInit uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _rid::init::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.ralloc_mm")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.ralloc_drgn_mm")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 init in
        (FStarC_Extraction_KrmlAst.ManuallyManaged, uu___6,
          (FStarC_Extraction_KrmlAst.EConstant
             (FStarC_Extraction_KrmlAst.UInt32, "1"))) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _e0::e1::e2::[])
      when
      ((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.Buffer.rcreate_mm")
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "LowStar.Monotonic.Buffer.mmalloc"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.mmalloc"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.imalloc")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        (FStarC_Extraction_KrmlAst.ManuallyManaged, uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufCreate uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _erid::elen::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.UninitializedBuffer.umalloc"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 elen in
        (FStarC_Extraction_KrmlAst.ManuallyManaged, uu___6) in
      FStarC_Extraction_KrmlAst.EBufCreateNoInit uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e2::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.rfree")
        || false
      ->
      let uu___5 = translate_expr env1 e2 in
      FStarC_Extraction_KrmlAst.EBufFree uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e2::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.Buffer.rfree")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.Monotonic.Buffer.free")
      ->
      let uu___5 = translate_expr env1 e2 in
      FStarC_Extraction_KrmlAst.EBufFree uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::_e3::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufSub uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::_e3::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "LowStar.Monotonic.Buffer.msub")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ConstBuffer.sub")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufSub uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.join"
      -> translate_expr env1 e1
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.Buffer.offset"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufSub uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.Monotonic.Buffer.moffset"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in (uu___6, uu___7) in
      FStarC_Extraction_KrmlAst.EBufSub uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::e3::[])
      when
      ((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.Buffer.upd")
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "FStar.Buffer.op_Dot_Lparen_Rparen_Less_Minus"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.upd'"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.UninitializedBuffer.uupd")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
      FStarC_Extraction_KrmlAst.EBufWrite uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.HyperStack.ST.op_Colon_Equals"
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        (uu___6,
          (FStarC_Extraction_KrmlAst.EQualified (["C"], "_zero_for_deref")),
          uu___7) in
      FStarC_Extraction_KrmlAst.EBufWrite uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       uu___2::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.push_frame")
        || false
      -> FStarC_Extraction_KrmlAst.EPushFrame
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       uu___2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.HyperStack.ST.pop_frame"
      -> FStarC_Extraction_KrmlAst.EPopFrame
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::e3::e4::e5::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "FStar.Buffer.blit")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.Monotonic.Buffer.blit"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.UninitializedBuffer.ublit")
      ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        let uu___8 = translate_expr env1 e3 in
        let uu___9 = translate_expr env1 e4 in
        let uu___10 = translate_expr env1 e5 in
        (uu___6, uu___7, uu___8, uu___9, uu___10) in
      FStarC_Extraction_KrmlAst.EBufBlit uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::e2::e3::[])
      when
      let s = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
      (s = "FStar.Buffer.fill") || (s = "LowStar.Monotonic.Buffer.fill") ->
      let uu___5 =
        let uu___6 = translate_expr env1 e1 in
        let uu___7 = translate_expr env1 e2 in
        let uu___8 = translate_expr env1 e3 in (uu___6, uu___7, uu___8) in
      FStarC_Extraction_KrmlAst.EBufFill uu___5
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       uu___2::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.HyperStack.ST.get"
      -> FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _rid::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "FStar.HyperStack.ST.free_drgn")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.HyperStack.ST.new_drgn")
      -> FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       _ebuf::_eseq::[])
      when
      ((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.Monotonic.Buffer.witness_p")
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "LowStar.Monotonic.Buffer.recall_p"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.ImmutableBuffer.witness_contents"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ImmutableBuffer.recall_contents")
      -> FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       e1::[])
      when
      ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
         "LowStar.ConstBuffer.of_buffer")
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ConstBuffer.of_ibuffer")
      -> translate_expr env1 e1
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            t::[]);
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_},
       _eqal::e1::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.ConstBuffer.of_qbuf"
      ->
      let uu___4 =
        let uu___5 = translate_expr env1 e1 in
        let uu___6 =
          let uu___7 = translate_type env1 t in
          FStarC_Extraction_KrmlAst.TConstBuf uu___7 in
        (uu___5, uu___6) in
      FStarC_Extraction_KrmlAst.ECast uu___4
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            t::[]);
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_},
       e1::[])
      when
      (((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
          "LowStar.ConstBuffer.cast")
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "LowStar.ConstBuffer.to_buffer"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "LowStar.ConstBuffer.to_ibuffer")
      ->
      let uu___4 =
        let uu___5 = translate_expr env1 e1 in
        let uu___6 =
          let uu___7 = translate_type env1 t in
          FStarC_Extraction_KrmlAst.TBuf uu___7 in
        (uu___5, uu___6) in
      FStarC_Extraction_KrmlAst.ECast uu___4
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       e1::[])
      when (FStarC_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr" ->
      let uu___2 =
        let uu___3 = translate_expr env1 e1 in
        (uu___3, FStarC_Extraction_KrmlAst.TAny) in
      FStarC_Extraction_KrmlAst.ECast uu___2
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], "of_int");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       e1::[])
      when is_float_width (mk_width m) ->
      let uu___2 =
        let uu___3 = translate_expr env1 e1 in
        let uu___4 =
          let uu___5 = FStarC_Option.must (mk_width m) in
          FStarC_Extraction_KrmlAst.TInt uu___5 in
        (uu___3, uu___4) in
      FStarC_Extraction_KrmlAst.ECast uu___2
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("FStar"::m::[], "of_literal");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       {
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s);
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      when is_float_width (mk_width m) ->
      (if Prims.not (valid_float_literal s)
       then
         FStarC_Effect.failwith
           (FStarC_Format.fmt2
              "Refusing to extract invalid %s.of_literal argument as a C floating-point constant: %s"
              m s)
       else ();
       (let uu___5 =
          let uu___6 = FStarC_Option.must (mk_width m) in (uu___6, s) in
        FStarC_Extraction_KrmlAst.EConstant uu___5))
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], op);
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       args)
      when (is_machine_int m) && (is_op op) ->
      let uu___2 = FStarC_Option.must (mk_width m) in
      let uu___3 = FStarC_Option.must (mk_op op) in
      mk_op_app env1 uu___2 uu___3 args
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name ("Prims"::[], op);
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       args)
      when is_bool_op op ->
      let uu___2 = FStarC_Option.must (mk_bool_op op) in
      mk_op_app env1 FStarC_Extraction_KrmlAst.Bool uu___2 args
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], "int_to_t");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       {
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_Int
           (c, FStar_Pervasives_Native.None));
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      when is_machine_int m ->
      let uu___4 =
        let uu___5 = FStarC_Option.must (mk_width m) in (uu___5, c) in
      FStarC_Extraction_KrmlAst.EConstant uu___4
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name ("FStar"::m::[], "uint_to_t");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       {
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_Int
           (c, FStar_Pervasives_Native.None));
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      when is_machine_int m ->
      let uu___4 =
        let uu___5 = FStarC_Option.must (mk_width m) in (uu___5, c) in
      FStarC_Extraction_KrmlAst.EConstant uu___4
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("C"::[], "string_of_literal");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       { FStarC_Extraction_ML_Syntax.expr = e1;
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      ->
      (match e1 with
       | FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s) ->
           FStarC_Extraction_KrmlAst.EString s
       | uu___4 ->
           FStarC_Effect.failwith
             "Cannot extract string_of_literal applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("C"::"Compat"::"String"::[], "of_literal");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       { FStarC_Extraction_ML_Syntax.expr = e1;
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      ->
      (match e1 with
       | FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s) ->
           FStarC_Extraction_KrmlAst.EString s
       | uu___4 ->
           FStarC_Effect.failwith
             "Cannot extract string_of_literal applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("C"::"String"::[], "of_literal");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       { FStarC_Extraction_ML_Syntax.expr = e1;
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      ->
      (match e1 with
       | FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s) ->
           FStarC_Extraction_KrmlAst.EString s
       | uu___4 ->
           FStarC_Effect.failwith
             "Cannot extract string_of_literal applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_TApp
           ({
              FStarC_Extraction_ML_Syntax.expr =
                FStarC_Extraction_ML_Syntax.MLE_Name p;
              FStarC_Extraction_ML_Syntax.mlty = uu___;
              FStarC_Extraction_ML_Syntax.loc = uu___1;_},
            uu___2);
         FStarC_Extraction_ML_Syntax.mlty = uu___3;
         FStarC_Extraction_ML_Syntax.loc = uu___4;_},
       { FStarC_Extraction_ML_Syntax.expr = ebefore;
         FStarC_Extraction_ML_Syntax.mlty = uu___5;
         FStarC_Extraction_ML_Syntax.loc = uu___6;_}::e1::{
                                                            FStarC_Extraction_ML_Syntax.expr
                                                              = eafter;
                                                            FStarC_Extraction_ML_Syntax.mlty
                                                              = uu___7;
                                                            FStarC_Extraction_ML_Syntax.loc
                                                              = uu___8;_}::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.Comment.comment_gen"
      ->
      (match (ebefore, eafter) with
       | (FStarC_Extraction_ML_Syntax.MLE_Const
          (FStarC_Extraction_ML_Syntax.MLC_String sbefore),
          FStarC_Extraction_ML_Syntax.MLE_Const
          (FStarC_Extraction_ML_Syntax.MLC_String safter)) ->
           (if FStarC_Util.contains sbefore "*/"
            then
              FStarC_Effect.failwith
                "Before Comment contains end-of-comment marker"
            else ();
            if FStarC_Util.contains safter "*/"
            then
              FStarC_Effect.failwith
                "After Comment contains end-of-comment marker"
            else ();
            (let uu___11 =
               let uu___12 = translate_expr env1 e1 in
               (sbefore, uu___12, safter) in
             FStarC_Extraction_KrmlAst.EComment uu___11))
       | uu___9 ->
           FStarC_Effect.failwith
             "Cannot extract comment applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       { FStarC_Extraction_ML_Syntax.expr = e1;
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "LowStar.Comment.comment"
      ->
      (match e1 with
       | FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s) ->
           (if FStarC_Util.contains s "*/"
            then
              FStarC_Effect.failwith
                "Standalone Comment contains end-of-comment marker"
            else ();
            FStarC_Extraction_KrmlAst.EStandaloneComment s)
       | uu___4 ->
           FStarC_Effect.failwith
             "Cannot extract comment applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("LowStar"::"Literal"::[], "buffer_of_literal");
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       { FStarC_Extraction_ML_Syntax.expr = e1;
         FStarC_Extraction_ML_Syntax.mlty = uu___2;
         FStarC_Extraction_ML_Syntax.loc = uu___3;_}::[])
      ->
      (match e1 with
       | FStarC_Extraction_ML_Syntax.MLE_Const
           (FStarC_Extraction_ML_Syntax.MLC_String s) ->
           FStarC_Extraction_KrmlAst.ECast
             ((FStarC_Extraction_KrmlAst.EString s),
               (FStarC_Extraction_KrmlAst.TBuf
                  (FStarC_Extraction_KrmlAst.TInt
                     FStarC_Extraction_KrmlAst.UInt8)))
       | uu___4 ->
           FStarC_Effect.failwith
             "Cannot extract buffer_of_literal applied to a non-literal")
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name
           ("FStar"::"Int"::"Cast"::[], c);
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       arg::[])
      ->
      let is_known_type =
        (((((((FStarC_Util.starts_with c "uint8") ||
                (FStarC_Util.starts_with c "uint16"))
               || (FStarC_Util.starts_with c "uint32"))
              || (FStarC_Util.starts_with c "uint64"))
             || (FStarC_Util.starts_with c "int8"))
            || (FStarC_Util.starts_with c "int16"))
           || (FStarC_Util.starts_with c "int32"))
          || (FStarC_Util.starts_with c "int64") in
      if (FStarC_Util.ends_with c "uint64") && is_known_type
      then
        let uu___2 =
          let uu___3 = translate_expr env1 arg in
          (uu___3,
            (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.UInt64)) in
        FStarC_Extraction_KrmlAst.ECast uu___2
      else
        if (FStarC_Util.ends_with c "uint32") && is_known_type
        then
          (let uu___2 =
             let uu___3 = translate_expr env1 arg in
             (uu___3,
               (FStarC_Extraction_KrmlAst.TInt
                  FStarC_Extraction_KrmlAst.UInt32)) in
           FStarC_Extraction_KrmlAst.ECast uu___2)
        else
          if (FStarC_Util.ends_with c "uint16") && is_known_type
          then
            (let uu___2 =
               let uu___3 = translate_expr env1 arg in
               (uu___3,
                 (FStarC_Extraction_KrmlAst.TInt
                    FStarC_Extraction_KrmlAst.UInt16)) in
             FStarC_Extraction_KrmlAst.ECast uu___2)
          else
            if (FStarC_Util.ends_with c "uint8") && is_known_type
            then
              (let uu___2 =
                 let uu___3 = translate_expr env1 arg in
                 (uu___3,
                   (FStarC_Extraction_KrmlAst.TInt
                      FStarC_Extraction_KrmlAst.UInt8)) in
               FStarC_Extraction_KrmlAst.ECast uu___2)
            else
              if (FStarC_Util.ends_with c "int64") && is_known_type
              then
                (let uu___2 =
                   let uu___3 = translate_expr env1 arg in
                   (uu___3,
                     (FStarC_Extraction_KrmlAst.TInt
                        FStarC_Extraction_KrmlAst.Int64)) in
                 FStarC_Extraction_KrmlAst.ECast uu___2)
              else
                if (FStarC_Util.ends_with c "int32") && is_known_type
                then
                  (let uu___2 =
                     let uu___3 = translate_expr env1 arg in
                     (uu___3,
                       (FStarC_Extraction_KrmlAst.TInt
                          FStarC_Extraction_KrmlAst.Int32)) in
                   FStarC_Extraction_KrmlAst.ECast uu___2)
                else
                  if (FStarC_Util.ends_with c "int16") && is_known_type
                  then
                    (let uu___2 =
                       let uu___3 = translate_expr env1 arg in
                       (uu___3,
                         (FStarC_Extraction_KrmlAst.TInt
                            FStarC_Extraction_KrmlAst.Int16)) in
                     FStarC_Extraction_KrmlAst.ECast uu___2)
                  else
                    if (FStarC_Util.ends_with c "int8") && is_known_type
                    then
                      (let uu___2 =
                         let uu___3 = translate_expr env1 arg in
                         (uu___3,
                           (FStarC_Extraction_KrmlAst.TInt
                              FStarC_Extraction_KrmlAst.Int8)) in
                       FStarC_Extraction_KrmlAst.ECast uu___2)
                    else
                      (let uu___2 =
                         let uu___3 =
                           let uu___4 = translate_expr env1 arg in [uu___4] in
                         ((FStarC_Extraction_KrmlAst.EQualified
                             (["FStar"; "Int"; "Cast"], c)), uu___3) in
                       FStarC_Extraction_KrmlAst.EApp uu___2)
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       arg::[])
      when
      ((((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.SizeT.uint16_to_sizet")
          ||
          ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
             "FStar.SizeT.uint32_to_sizet"))
         ||
         ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
            "FStar.SizeT.uint64_to_sizet"))
        ||
        ((FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
           "FStar.PtrdiffT.ptrdifft_to_sizet")
      ->
      let uu___2 =
        let uu___3 = translate_expr env1 arg in
        (uu___3,
          (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.SizeT)) in
      FStarC_Extraction_KrmlAst.ECast uu___2
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       arg::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.SizeT.sizet_to_uint32"
      ->
      let uu___2 =
        let uu___3 = translate_expr env1 arg in
        (uu___3,
          (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.UInt32)) in
      FStarC_Extraction_KrmlAst.ECast uu___2
  | FStarC_Extraction_ML_Syntax.MLE_App
      ({
         FStarC_Extraction_ML_Syntax.expr =
           FStarC_Extraction_ML_Syntax.MLE_Name p;
         FStarC_Extraction_ML_Syntax.mlty = uu___;
         FStarC_Extraction_ML_Syntax.loc = uu___1;_},
       arg::[])
      when
      (FStarC_Extraction_ML_Syntax.string_of_mlpath p) =
        "FStar.SizeT.sizet_to_uint64"
      ->
      let uu___2 =
        let uu___3 = translate_expr env1 arg in
        (uu___3,
          (FStarC_Extraction_KrmlAst.TInt FStarC_Extraction_KrmlAst.UInt64)) in
      FStarC_Extraction_KrmlAst.ECast uu___2
  | FStarC_Extraction_ML_Syntax.MLE_App (head, args) ->
      let uu___ =
        let uu___1 = translate_expr env1 head in
        let uu___2 = FStarC_List.map (translate_expr env1) args in
        (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EApp uu___
  | FStarC_Extraction_ML_Syntax.MLE_TApp (head, ty_args) ->
      let uu___ =
        let uu___1 = translate_expr env1 head in
        let uu___2 = FStarC_List.map (translate_type env1) ty_args in
        (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ETypApp uu___
  | FStarC_Extraction_ML_Syntax.MLE_Coerce (e1, t_from, t_to) ->
      let uu___ =
        let uu___1 = translate_expr env1 e1 in
        let uu___2 = translate_type env1 t_to in (uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.ECast uu___
  | FStarC_Extraction_ML_Syntax.MLE_Record (uu___, uu___1, fields) ->
      let uu___2 =
        let uu___3 = assert_lid env1 e.FStarC_Extraction_ML_Syntax.mlty in
        let uu___4 =
          FStarC_List.map
            (fun uu___5 ->
               match uu___5 with
               | (field, expr) ->
                   let uu___6 = translate_expr env1 expr in (field, uu___6))
            fields in
        (uu___3, uu___4) in
      FStarC_Extraction_KrmlAst.EFlat uu___2
  | FStarC_Extraction_ML_Syntax.MLE_Proj (e1, path) ->
      let uu___ =
        let uu___1 = assert_lid env1 e1.FStarC_Extraction_ML_Syntax.mlty in
        let uu___2 = translate_expr env1 e1 in
        (uu___1, uu___2, (FStar_Pervasives_Native.snd path)) in
      FStarC_Extraction_KrmlAst.EField uu___
  | FStarC_Extraction_ML_Syntax.MLE_Let uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Extraction_ML_Code.string_of_mlexpr ([], "") e in
        FStarC_Format.fmt1 "todo: translate_expr [MLE_Let] (expr is: %s)"
          uu___2 in
      FStarC_Effect.failwith uu___1
  | FStarC_Extraction_ML_Syntax.MLE_App (head, uu___) ->
      let uu___1 =
        let uu___2 = FStarC_Extraction_ML_Code.string_of_mlexpr ([], "") head in
        FStarC_Format.fmt1 "todo: translate_expr [MLE_App] (head is: %s)"
          uu___2 in
      FStarC_Effect.failwith uu___1
  | FStarC_Extraction_ML_Syntax.MLE_Seq seqs ->
      let uu___ = FStarC_List.map (translate_expr env1) seqs in
      FStarC_Extraction_KrmlAst.ESequence uu___
  | FStarC_Extraction_ML_Syntax.MLE_Tuple es ->
      let uu___ = FStarC_List.map (translate_expr env1) es in
      FStarC_Extraction_KrmlAst.ETuple uu___
  | FStarC_Extraction_ML_Syntax.MLE_CTor ((uu___, cons), es) ->
      let uu___1 =
        let uu___2 = assert_lid env1 e.FStarC_Extraction_ML_Syntax.mlty in
        let uu___3 = FStarC_List.map (translate_expr env1) es in
        (uu___2, cons, uu___3) in
      FStarC_Extraction_KrmlAst.ECons uu___1
  | FStarC_Extraction_ML_Syntax.MLE_Fun (bs, body) ->
      let binders = translate_binders env1 bs in
      let env2 = add_binders env1 bs in
      let uu___ =
        let uu___1 = translate_expr env2 body in
        let uu___2 =
          translate_type env2 body.FStarC_Extraction_ML_Syntax.mlty in
        (binders, uu___1, uu___2) in
      FStarC_Extraction_KrmlAst.EFun uu___
  | FStarC_Extraction_ML_Syntax.MLE_If (e1, e2, e3) ->
      let uu___ =
        let uu___1 = translate_expr env1 e1 in
        let uu___2 = translate_expr env1 e2 in
        let uu___3 =
          match e3 with
          | FStar_Pervasives_Native.None -> FStarC_Extraction_KrmlAst.EUnit
          | FStar_Pervasives_Native.Some e31 -> translate_expr env1 e31 in
        (uu___1, uu___2, uu___3) in
      FStarC_Extraction_KrmlAst.EIfThenElse uu___
  | FStarC_Extraction_ML_Syntax.MLE_Raise uu___ ->
      FStarC_Effect.failwith "todo: translate_expr [MLE_Raise]"
  | FStarC_Extraction_ML_Syntax.MLE_Try uu___ ->
      FStarC_Effect.failwith "todo: translate_expr [MLE_Try]"
  | FStarC_Extraction_ML_Syntax.MLE_Coerce uu___ ->
      FStarC_Effect.failwith "todo: translate_expr [MLE_Coerce]"
and assert_lid (env1 : env) (t : FStarC_Extraction_ML_Syntax.mlty) :
  FStarC_Extraction_KrmlAst.typ=
  match t with
  | FStarC_Extraction_ML_Syntax.MLTY_Named (ts, lid) ->
      if (match ts with | hd::tl -> true | uu___ -> false)
      then
        let uu___ =
          let uu___1 = FStarC_List.map (translate_type env1) ts in
          (lid, uu___1) in
        FStarC_Extraction_KrmlAst.TApp uu___
      else FStarC_Extraction_KrmlAst.TQualified lid
  | uu___ ->
      let uu___1 =
        let uu___2 = FStarC_Extraction_ML_Code.string_of_mlty ([], "") t in
        FStarC_Format.fmt1 "invalid argument: expected MLTY_Named, got %s"
          uu___2 in
      FStarC_Effect.failwith uu___1
and translate_branches (env1 : env)
  (branches : FStarC_Extraction_ML_Syntax.mlbranch Prims.list) :
  FStarC_Extraction_KrmlAst.branch Prims.list=
  match branches with
  | [] -> []
  | b::rest ->
      let uu___ = translate_branch env1 b in
      let uu___1 = translate_branches env1 rest in uu___ :: uu___1
and translate_branch (env1 : env) (b : FStarC_Extraction_ML_Syntax.mlbranch)
  : FStarC_Extraction_KrmlAst.branch=
  let uu___ = b in
  match uu___ with
  | (pat, guard, expr) ->
      if guard = FStar_Pervasives_Native.None
      then
        let uu___1 = translate_pat env1 pat in
        (match uu___1 with
         | (env2, pat1) ->
             let uu___2 = translate_expr env2 expr in (pat1, uu___2))
      else FStarC_Effect.failwith "todo: translate_branch"
and translate_width
  (w :
    (FStarC_Const.signedness * FStarC_Const.width)
      FStar_Pervasives_Native.option)
  : FStarC_Extraction_KrmlAst.width=
  match w with
  | FStar_Pervasives_Native.None -> FStarC_Extraction_KrmlAst.CInt
  | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int8) ->
      FStarC_Extraction_KrmlAst.Int8
  | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int16) ->
      FStarC_Extraction_KrmlAst.Int16
  | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int32) ->
      FStarC_Extraction_KrmlAst.Int32
  | FStar_Pervasives_Native.Some (FStarC_Const.Signed, FStarC_Const.Int64) ->
      FStarC_Extraction_KrmlAst.Int64
  | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Int8)
      -> FStarC_Extraction_KrmlAst.UInt8
  | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Int16)
      -> FStarC_Extraction_KrmlAst.UInt16
  | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Int32)
      -> FStarC_Extraction_KrmlAst.UInt32
  | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Int64)
      -> FStarC_Extraction_KrmlAst.UInt64
  | FStar_Pervasives_Native.Some (FStarC_Const.Unsigned, FStarC_Const.Sizet)
      -> FStarC_Extraction_KrmlAst.SizeT
and translate_pat (env1 : env) (p : FStarC_Extraction_ML_Syntax.mlpattern) :
  env_and_pat=
  match p with
  | FStarC_Extraction_ML_Syntax.MLP_Const
      (FStarC_Extraction_ML_Syntax.MLC_Unit) ->
      (env1, FStarC_Extraction_KrmlAst.PUnit)
  | FStarC_Extraction_ML_Syntax.MLP_Const
      (FStarC_Extraction_ML_Syntax.MLC_Bool b) ->
      (env1, (FStarC_Extraction_KrmlAst.PBool b))
  | FStarC_Extraction_ML_Syntax.MLP_Const
      (FStarC_Extraction_ML_Syntax.MLC_Int (s, sw)) ->
      let uu___ =
        let uu___1 = let uu___2 = translate_width sw in (uu___2, s) in
        FStarC_Extraction_KrmlAst.PConstant uu___1 in
      (env1, uu___)
  | FStarC_Extraction_ML_Syntax.MLP_Var name1 ->
      let env2 = extend env1 name1 in
      (env2,
        (FStarC_Extraction_KrmlAst.PVar
           {
             FStarC_Extraction_KrmlAst.name = name1;
             FStarC_Extraction_KrmlAst.typ = FStarC_Extraction_KrmlAst.TAny;
             FStarC_Extraction_KrmlAst.mut = false;
             FStarC_Extraction_KrmlAst.meta = []
           }))
  | FStarC_Extraction_ML_Syntax.MLP_Wild ->
      let env2 = extend env1 "_" in
      (env2,
        (FStarC_Extraction_KrmlAst.PVar
           {
             FStarC_Extraction_KrmlAst.name = "_";
             FStarC_Extraction_KrmlAst.typ = FStarC_Extraction_KrmlAst.TAny;
             FStarC_Extraction_KrmlAst.mut = false;
             FStarC_Extraction_KrmlAst.meta = []
           }))
  | FStarC_Extraction_ML_Syntax.MLP_CTor ((uu___, cons), ps) ->
      let uu___1 =
        FStarC_List.fold_left
          (fun uu___2 p1 ->
             match uu___2 with
             | (env2, acc) ->
                 let uu___3 = translate_pat env2 p1 in
                 (match uu___3 with | (env3, p2) -> (env3, (p2 :: acc))))
          (env1, []) ps in
      (match uu___1 with
       | (env2, ps1) ->
           (env2,
             (FStarC_Extraction_KrmlAst.PCons (cons, (FStarC_List.rev ps1)))))
  | FStarC_Extraction_ML_Syntax.MLP_Record (uu___, ps) ->
      let uu___1 =
        FStarC_List.fold_left
          (fun uu___2 uu___3 ->
             match (uu___2, uu___3) with
             | ((env2, acc), (field, p1)) ->
                 let uu___4 = translate_pat env2 p1 in
                 (match uu___4 with
                  | (env3, p2) -> (env3, ((field, p2) :: acc)))) (env1, [])
          ps in
      (match uu___1 with
       | (env2, ps1) ->
           (env2, (FStarC_Extraction_KrmlAst.PRecord (FStarC_List.rev ps1))))
  | FStarC_Extraction_ML_Syntax.MLP_Tuple ps ->
      let uu___ =
        FStarC_List.fold_left
          (fun uu___1 p1 ->
             match uu___1 with
             | (env2, acc) ->
                 let uu___2 = translate_pat env2 p1 in
                 (match uu___2 with | (env3, p2) -> (env3, (p2 :: acc))))
          (env1, []) ps in
      (match uu___ with
       | (env2, ps1) ->
           (env2, (FStarC_Extraction_KrmlAst.PTuple (FStarC_List.rev ps1))))
  | FStarC_Extraction_ML_Syntax.MLP_Const uu___ ->
      FStarC_Effect.failwith "todo: translate_pat [MLP_Const]"
  | FStarC_Extraction_ML_Syntax.MLP_Branch uu___ ->
      FStarC_Effect.failwith "todo: translate_pat [MLP_Branch]"
and translate_constant (c : FStarC_Extraction_ML_Syntax.mlconstant) :
  FStarC_Extraction_KrmlAst.expr=
  match c with
  | FStarC_Extraction_ML_Syntax.MLC_Unit -> FStarC_Extraction_KrmlAst.EUnit
  | FStarC_Extraction_ML_Syntax.MLC_Bool b ->
      FStarC_Extraction_KrmlAst.EBool b
  | FStarC_Extraction_ML_Syntax.MLC_String s ->
      ((let uu___1 =
          FStarC_Util.for_some
            (fun c1 -> c1 = (FStar_Char.char_of_int Prims.int_zero))
            (FStar_String.list_of_string s) in
        if uu___1
        then
          FStarC_Effect.failwith
            (FStarC_Format.fmt1
               "Refusing to translate a string literal that contains a null character: %s"
               s)
        else ());
       FStarC_Extraction_KrmlAst.EString s)
  | FStarC_Extraction_ML_Syntax.MLC_Char c1 ->
      let i = FStarC_Util.int_of_char c1 in
      let s = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      let c2 =
        FStarC_Extraction_KrmlAst.EConstant
          (FStarC_Extraction_KrmlAst.CInt, s) in
      let char_of_int =
        FStarC_Extraction_KrmlAst.EQualified
          (["FStar"; "Char"], "char_of_int") in
      FStarC_Extraction_KrmlAst.EApp (char_of_int, [c2])
  | FStarC_Extraction_ML_Syntax.MLC_Int
      (s, FStar_Pervasives_Native.Some (sg, wd)) ->
      let uu___ =
        let uu___1 = translate_width (FStar_Pervasives_Native.Some (sg, wd)) in
        (uu___1, s) in
      FStarC_Extraction_KrmlAst.EConstant uu___
  | FStarC_Extraction_ML_Syntax.MLC_Float uu___ ->
      FStarC_Effect.failwith "todo: translate_expr [MLC_Float]"
  | FStarC_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) ->
      FStarC_Extraction_KrmlAst.EConstant (FStarC_Extraction_KrmlAst.CInt, s)
and mk_op_app (env1 : env) (w : FStarC_Extraction_KrmlAst.width)
  (op : FStarC_Extraction_KrmlAst.op)
  (args : FStarC_Extraction_ML_Syntax.mlexpr Prims.list) :
  FStarC_Extraction_KrmlAst.expr=
  let uu___ =
    let uu___1 = FStarC_List.map (translate_expr env1) args in
    ((FStarC_Extraction_KrmlAst.EOp (op, w)), uu___1) in
  FStarC_Extraction_KrmlAst.EApp uu___
let translate_type_decl' (env1 : env)
  (ty : FStarC_Extraction_ML_Syntax.one_mltydecl) :
  FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option=
  match ty with
  | { FStarC_Extraction_ML_Syntax.tydecl_assumed = assumed;
      FStarC_Extraction_ML_Syntax.tydecl_name = name1;
      FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___;
      FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
      FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
      FStarC_Extraction_ML_Syntax.tydecl_defn = FStar_Pervasives_Native.Some
        (FStarC_Extraction_ML_Syntax.MLTD_Abbrev t);_}
      ->
      let name2 = krml_decl_name env1.module_name name1 in
      let env2 =
        FStarC_List.fold_left
          (fun env3 uu___1 ->
             match uu___1 with
             | { FStarC_Extraction_ML_Syntax.ty_param_name = ty_param_name;
                 FStarC_Extraction_ML_Syntax.ty_param_attrs = uu___2;_} ->
                 extend_t env3 ty_param_name) env1 args in
      if
        assumed &&
          (FStarC_List.mem FStarC_Extraction_ML_Syntax.CAbstract flags)
      then
        FStar_Pervasives_Native.Some
          (FStarC_Extraction_KrmlAst.DTypeAbstractStruct name2)
      else
        if assumed
        then
          (let name3 = FStarC_Extraction_ML_Syntax.string_of_mlpath name2 in
           (let uu___2 =
              let uu___3 = FStarC_Options.silent () in Prims.not uu___3 in
            if uu___2
            then
              FStarC_Format.print1_warning
                "Not extracting type definition %s to KaRaMeL (assumed type)\n"
                name3
            else ());
           FStar_Pervasives_Native.None)
        else
          (let uu___1 =
             let uu___2 =
               let uu___3 = translate_flags flags in
               let uu___4 = translate_type env2 t in
               (name2, uu___3, (FStarC_List.length args), uu___4) in
             FStarC_Extraction_KrmlAst.DTypeAlias uu___2 in
           FStar_Pervasives_Native.Some uu___1)
  | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
      FStarC_Extraction_ML_Syntax.tydecl_name = name1;
      FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
      FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
      FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
      FStarC_Extraction_ML_Syntax.tydecl_defn = FStar_Pervasives_Native.Some
        (FStarC_Extraction_ML_Syntax.MLTD_Record fields);_}
      ->
      let name2 = krml_decl_name env1.module_name name1 in
      let env2 =
        FStarC_List.fold_left
          (fun env3 uu___2 ->
             match uu___2 with
             | { FStarC_Extraction_ML_Syntax.ty_param_name = ty_param_name;
                 FStarC_Extraction_ML_Syntax.ty_param_attrs = uu___3;_} ->
                 extend_t env3 ty_param_name) env1 args in
      let uu___2 =
        let uu___3 =
          let uu___4 = translate_flags flags in
          let uu___5 =
            FStarC_List.map
              (fun uu___6 ->
                 match uu___6 with
                 | (f, t) ->
                     let uu___7 =
                       let uu___8 = translate_type_without_decay env2 t in
                       (uu___8, false) in
                     (f, uu___7)) fields in
          (name2, uu___4, (FStarC_List.length args), uu___5) in
        FStarC_Extraction_KrmlAst.DTypeFlat uu___3 in
      FStar_Pervasives_Native.Some uu___2
  | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
      FStarC_Extraction_ML_Syntax.tydecl_name = name1;
      FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
      FStarC_Extraction_ML_Syntax.tydecl_parameters = args;
      FStarC_Extraction_ML_Syntax.tydecl_meta = flags;
      FStarC_Extraction_ML_Syntax.tydecl_defn = FStar_Pervasives_Native.Some
        (FStarC_Extraction_ML_Syntax.MLTD_DType branches);_}
      ->
      let name2 = krml_decl_name env1.module_name name1 in
      let flags1 = translate_flags flags in
      let env2 =
        let uu___2 = FStarC_Extraction_ML_Syntax.ty_param_names args in
        FStarC_List.fold_left extend_t env1 uu___2 in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_List.map
              (fun uu___5 ->
                 match uu___5 with
                 | (cons, ts) ->
                     let uu___6 =
                       FStarC_List.map
                         (fun uu___7 ->
                            match uu___7 with
                            | (name3, t) ->
                                let uu___8 =
                                  let uu___9 =
                                    translate_type_without_decay env2 t in
                                  (uu___9, false) in
                                (name3, uu___8)) ts in
                     (cons, uu___6)) branches in
          (name2, flags1, (FStarC_List.length args), uu___4) in
        FStarC_Extraction_KrmlAst.DTypeVariant uu___3 in
      FStar_Pervasives_Native.Some uu___2
  | { FStarC_Extraction_ML_Syntax.tydecl_assumed = uu___;
      FStarC_Extraction_ML_Syntax.tydecl_name = name1;
      FStarC_Extraction_ML_Syntax.tydecl_ignored = uu___1;
      FStarC_Extraction_ML_Syntax.tydecl_parameters = uu___2;
      FStarC_Extraction_ML_Syntax.tydecl_meta = uu___3;
      FStarC_Extraction_ML_Syntax.tydecl_defn = uu___4;_} ->
      (FStarC_Errors.log_issue0
         FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic
            [FStarC_Errors_Msg.text
               (FStarC_Format.fmt1
                  "Error extracting type definition %s to KaRaMeL." name1)]);
       FStar_Pervasives_Native.None)
let translate_let' (env1 : env)
  (flavor : FStarC_Extraction_ML_Syntax.mlletflavor)
  (lb : FStarC_Extraction_ML_Syntax.mllb) :
  FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option=
  match lb with
  | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
      FStarC_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some
        (tvars, t0);
      FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
      FStarC_Extraction_ML_Syntax.mllb_def = e;
      FStarC_Extraction_ML_Syntax.mllb_attrs = uu___1;
      FStarC_Extraction_ML_Syntax.mllb_meta = meta;
      FStarC_Extraction_ML_Syntax.print_typ = uu___2;_} when
      FStarC_Util.for_some
        (fun uu___3 ->
           match uu___3 with
           | FStarC_Extraction_ML_Syntax.Assumed -> true
           | uu___4 -> false) meta
      ->
      let name2 = krml_decl_name env1.module_name name1 in
      let arg_names =
        match e.FStarC_Extraction_ML_Syntax.expr with
        | FStarC_Extraction_ML_Syntax.MLE_Fun (bs, uu___3) ->
            FStarC_List.map
              (fun uu___4 ->
                 match uu___4 with
                 | {
                     FStarC_Extraction_ML_Syntax.mlbinder_name =
                       mlbinder_name;
                     FStarC_Extraction_ML_Syntax.mlbinder_ty = uu___5;
                     FStarC_Extraction_ML_Syntax.mlbinder_attrs = uu___6;_}
                     -> mlbinder_name) bs
        | uu___3 -> [] in
      if (match tvars with | [] -> true | uu___3 -> false)
      then
        let uu___3 =
          let uu___4 =
            let uu___5 = translate_cc meta in
            let uu___6 = translate_flags meta in
            let uu___7 = translate_type env1 t0 in
            (uu___5, uu___6, name2, uu___7, arg_names) in
          FStarC_Extraction_KrmlAst.DExternal uu___4 in
        FStar_Pervasives_Native.Some uu___3
      else
        ((let uu___4 =
            let uu___5 = FStarC_Options.silent () in Prims.not uu___5 in
          if uu___4
          then
            FStarC_Format.print1_warning
              "Not extracting %s to KaRaMeL (polymorphic assumes are not supported)\n"
              (FStarC_Extraction_ML_Syntax.string_of_mlpath name2)
          else ());
         FStar_Pervasives_Native.None)
  | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
      FStarC_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some
        (tvars, t0);
      FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
      FStarC_Extraction_ML_Syntax.mllb_def =
        {
          FStarC_Extraction_ML_Syntax.expr =
            FStarC_Extraction_ML_Syntax.MLE_Fun (args, body);
          FStarC_Extraction_ML_Syntax.mlty = uu___1;
          FStarC_Extraction_ML_Syntax.loc = uu___2;_};
      FStarC_Extraction_ML_Syntax.mllb_attrs = uu___3;
      FStarC_Extraction_ML_Syntax.mllb_meta = meta;
      FStarC_Extraction_ML_Syntax.print_typ = uu___4;_} ->
      if FStarC_List.mem FStarC_Extraction_ML_Syntax.NoExtract meta
      then FStar_Pervasives_Native.None
      else
        (let env2 =
           if flavor = FStarC_Extraction_ML_Syntax.Rec
           then extend env1 name1
           else env1 in
         let env3 =
           let uu___5 = FStarC_Extraction_ML_Syntax.ty_param_names tvars in
           FStarC_List.fold_left (fun env4 name2 -> extend_t env4 name2) env2
             uu___5 in
         let rec find_return_type eff i uu___5 =
           match uu___5 with
           | FStarC_Extraction_ML_Syntax.MLTY_Fun (uu___6, eff1, t) when
               i > Prims.int_zero ->
               find_return_type eff1 (i - Prims.int_one) t
           | t -> (i, eff, t) in
         let name2 = krml_decl_name env3.module_name name1 in
         let uu___5 =
           find_return_type FStarC_Extraction_ML_Syntax.E_PURE
             (FStarC_List.length args) t0 in
         match uu___5 with
         | (i, eff, t) ->
             let uu___6 =
               if i > Prims.int_zero
               then let uu___7 = FStarC_Options.silent () in Prims.not uu___7
               else false in
             if uu___6
             then
               let msg =
                 "function type annotation has less arrows than the number of arguments; please mark the return type abbreviation as inline_for_extraction" in
               (FStarC_Format.print2_warning
                  "Not extracting %s to KaRaMeL (%s)\n"
                  (FStarC_Extraction_ML_Syntax.string_of_mlpath name2) msg;
                FStar_Pervasives_Native.None)
             else
               (let t1 = translate_type env3 t in
                let binders = translate_binders env3 args in
                let env4 = add_binders env3 args in
                let cc = translate_cc meta in
                let meta1 =
                  match (eff, t1) with
                  | (FStarC_Extraction_ML_Syntax.E_ERASABLE, uu___7) ->
                      let uu___8 = translate_flags meta in
                      FStarC_Extraction_KrmlAst.MustDisappear :: uu___8
                  | (FStarC_Extraction_ML_Syntax.E_PURE,
                     FStarC_Extraction_KrmlAst.TUnit) ->
                      let uu___7 = translate_flags meta in
                      FStarC_Extraction_KrmlAst.MustDisappear :: uu___7
                  | uu___7 -> translate_flags meta in
                try
                  (fun uu___7 ->
                     match () with
                     | () ->
                         let body1 = translate_expr env4 body in
                         FStar_Pervasives_Native.Some
                           (FStarC_Extraction_KrmlAst.DFunction
                              (cc, meta1, (FStarC_List.length tvars), t1,
                                name2, binders, body1))) ()
                with
                | uu___7 ->
                    let sub_msg =
                      match uu___7 with
                      | FStarC_Errors.Error (code, msg, pos, ctx) ->
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 = FStarC_Errors.errno code in
                                  FStarC_Class_Show.show
                                    FStarC_Class_Show.showable_int uu___12 in
                                let uu___12 =
                                  FStarC_Class_Show.show
                                    FStarC_Range_Ops.showable_range pos in
                                FStarC_Format.fmt2 "Got error %s at %s."
                                  uu___11 uu___12 in
                              FStarC_Errors_Msg.text uu___10 in
                            let uu___10 = FStarC_Errors_Msg.render_as_doc msg in
                            FStar_Pprint.prefix (Prims.of_int 2)
                              Prims.int_one uu___9 uu___10 in
                          [uu___8]
                      | e ->
                          let uu___8 =
                            let uu___9 =
                              let uu___10 = FStarC_Util.print_exn e in
                              FStar_Pprint.arbitrary_string uu___10 in
                            FStar_Pprint.op_Hat_Hat
                              (FStarC_Errors_Msg.text "Got an exception: ")
                              uu___9 in
                          [uu___8] in
                    ((let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                FStarC_Class_Show.show
                                  (FStarC_Class_Show.show_tuple2
                                     (FStarC_Class_Show.show_list
                                        FStarC_Class_Show.showable_string)
                                     FStarC_Class_Show.showable_string) name2 in
                              FStarC_Format.fmt1
                                "Error while extracting %s to KaRaMeL."
                                uu___13 in
                            FStarC_Errors_Msg.text uu___12 in
                          [uu___11] in
                        FStarC_List.op_At uu___10 sub_msg in
                      FStarC_Errors.log_issue0
                        FStarC_Errors_Codes.Warning_FunctionNotExtacted ()
                        (Obj.magic
                           FStarC_Errors_Msg.is_error_message_list_doc)
                        (Obj.magic uu___9));
                     (let msg =
                        let uu___9 =
                          FStarC_Class_Show.show
                            (FStarC_Class_Show.show_tuple2
                               (FStarC_Class_Show.show_list
                                  FStarC_Class_Show.showable_string)
                               FStarC_Class_Show.showable_string) name2 in
                        Prims.strcat "This function was not extracted:\n"
                          uu___9 in
                      FStar_Pervasives_Native.Some
                        (FStarC_Extraction_KrmlAst.DFunction
                           (cc, meta1, (FStarC_List.length tvars), t1, name2,
                             binders,
                             (FStarC_Extraction_KrmlAst.EAbortS msg)))))))
  | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
      FStarC_Extraction_ML_Syntax.mllb_tysc = FStar_Pervasives_Native.Some
        (tvars, t);
      FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
      FStarC_Extraction_ML_Syntax.mllb_def = expr;
      FStarC_Extraction_ML_Syntax.mllb_attrs = uu___1;
      FStarC_Extraction_ML_Syntax.mllb_meta = meta;
      FStarC_Extraction_ML_Syntax.print_typ = uu___2;_} ->
      if FStarC_List.mem FStarC_Extraction_ML_Syntax.NoExtract meta
      then FStar_Pervasives_Native.None
      else
        (let meta1 = translate_flags meta in
         let env2 =
           let uu___3 = FStarC_Extraction_ML_Syntax.ty_param_names tvars in
           FStarC_List.fold_left (fun env3 name2 -> extend_t env3 name2) env1
             uu___3 in
         let t1 = translate_type env2 t in
         let name2 = krml_decl_name env2.module_name name1 in
         try
           (fun uu___3 ->
              match () with
              | () ->
                  let expr1 = translate_expr env2 expr in
                  FStar_Pervasives_Native.Some
                    (FStarC_Extraction_KrmlAst.DGlobal
                       (meta1, name2, (FStarC_List.length tvars), t1, expr1)))
             ()
         with
         | uu___3 ->
             ((let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = FStarC_Util.print_exn uu___3 in
                     FStar_Pprint.arbitrary_string uu___8 in
                   [uu___7] in
                 (FStarC_Errors_Msg.text
                    (FStarC_Format.fmt1 "Error extracting %s to KaRaMeL."
                       (FStarC_Extraction_ML_Syntax.string_of_mlpath name2)))
                   :: uu___6 in
               FStarC_Errors.log_issue0
                 FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___5));
              FStar_Pervasives_Native.Some
                (FStarC_Extraction_KrmlAst.DGlobal
                   (meta1, name2, (FStarC_List.length tvars), t1,
                     FStarC_Extraction_KrmlAst.EAny))))
  | { FStarC_Extraction_ML_Syntax.mllb_name = name1;
      FStarC_Extraction_ML_Syntax.mllb_tysc = ts;
      FStarC_Extraction_ML_Syntax.mllb_add_unit = uu___;
      FStarC_Extraction_ML_Syntax.mllb_def = uu___1;
      FStarC_Extraction_ML_Syntax.mllb_attrs = uu___2;
      FStarC_Extraction_ML_Syntax.mllb_meta = uu___3;
      FStarC_Extraction_ML_Syntax.print_typ = uu___4;_} ->
      (FStarC_Errors.log_issue0
         FStarC_Errors_Codes.Warning_DefinitionNotTranslated ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic
            (FStarC_Format.fmt1 "Not extracting %s to KaRaMeL\n" name1));
       (match ts with
        | FStar_Pervasives_Native.Some (tps, t) ->
            let uu___7 =
              let uu___8 = FStarC_Extraction_ML_Syntax.ty_param_names tps in
              FStarC_String.concat ", " uu___8 in
            let uu___8 = FStarC_Extraction_ML_Code.string_of_mlty ([], "") t in
            FStarC_Format.print2 "Type scheme is: forall %s. %s\n" uu___7
              uu___8
        | FStar_Pervasives_Native.None -> ());
       FStar_Pervasives_Native.None)
type translate_let_t =
  env ->
    FStarC_Extraction_ML_Syntax.mlletflavor ->
      FStarC_Extraction_ML_Syntax.mllb ->
        FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option
let ref_translate_let : translate_let_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref translate_let'
let register_pre_translate_let (f : translate_let_t) : unit=
  let before = FStarC_Effect.op_Bang ref_translate_let in
  let after e fl lb =
    try (fun uu___ -> match () with | () -> f e fl lb) ()
    with | NotSupportedByKrmlExtension -> before e fl lb in
  FStarC_Effect.op_Colon_Equals ref_translate_let after
let translate_let (env1 : env)
  (flavor : FStarC_Extraction_ML_Syntax.mlletflavor)
  (lb : FStarC_Extraction_ML_Syntax.mllb) :
  FStarC_Extraction_KrmlAst.decl FStar_Pervasives_Native.option=
  let uu___ = FStarC_Effect.op_Bang ref_translate_let in uu___ env1 flavor lb
let translate_decl (env1 : env) (d : FStarC_Extraction_ML_Syntax.mlmodule1) :
  FStarC_Extraction_KrmlAst.decl Prims.list=
  FStarC_Effect.op_Colon_Equals krml_current_decl
    (match d.FStarC_Extraction_ML_Syntax.mlmodule1_m with
     | FStarC_Extraction_ML_Syntax.MLM_Let (uu___1, lb::uu___2) ->
         FStar_Pervasives_Native.Some
           (lb.FStarC_Extraction_ML_Syntax.mllb_name)
     | uu___1 -> FStar_Pervasives_Native.None);
  FStarC_Effect.op_Colon_Equals translate_decl_accum [];
  (let base =
     match d.FStarC_Extraction_ML_Syntax.mlmodule1_m with
     | FStarC_Extraction_ML_Syntax.MLM_Let (flavor, lbs) ->
         FStarC_List.choose (translate_let env1 flavor) lbs
     | FStarC_Extraction_ML_Syntax.MLM_Loc uu___2 -> []
     | FStarC_Extraction_ML_Syntax.MLM_Ty tys ->
         FStarC_List.choose (translate_type_decl env1) tys
     | FStarC_Extraction_ML_Syntax.MLM_Top uu___2 ->
         FStarC_Effect.failwith "todo: translate_decl [MLM_Top]"
     | FStarC_Extraction_ML_Syntax.MLM_Exn (m, uu___2) ->
         ((let uu___4 =
             let uu___5 = FStarC_Options.silent () in Prims.not uu___5 in
           if uu___4
           then
             FStarC_Format.print1_warning
               "Not extracting exception %s to KaRaMeL (exceptions unsupported)\n"
               m
           else ());
          []) in
   let uu___2 = FStarC_Effect.op_Bang translate_decl_accum in
   FStarC_List.op_At uu___2 base)
let translate_module (uenv : FStarC_Extraction_ML_UEnv.uenv)
  (m :
    (FStarC_Extraction_ML_Syntax.mlpath * (FStarC_Extraction_ML_Syntax.mlsig
      * FStarC_Extraction_ML_Syntax.mlmodulebody)
      FStar_Pervasives_Native.option))
  : file=
  let uu___ = m in
  match uu___ with
  | (module_name, modul) ->
      let module_name1 =
        FStarC_List.op_At (FStar_Pervasives_Native.fst module_name)
          [FStar_Pervasives_Native.snd module_name] in
      let program1 =
        match modul with
        | FStar_Pervasives_Native.Some (_signature, decls) ->
            FStarC_List.collect (translate_decl (empty uenv module_name1))
              decls
        | uu___1 ->
            FStarC_Effect.failwith
              "Unexpected standalone interface or nested modules" in
      ((FStarC_String.concat "_" module_name1), program1)
let translate (ue : FStarC_Extraction_ML_UEnv.uenv)
  (modules : FStarC_Extraction_ML_Syntax.mlmodule Prims.list) :
  file Prims.list=
  FStarC_List.filter_map
    (fun m ->
       let m_name =
         let uu___ = m in
         match uu___ with
         | (path, uu___1) ->
             FStarC_Extraction_ML_Syntax.string_of_mlpath path in
       try
         (fun uu___ ->
            match () with
            | () ->
                ((let uu___2 =
                    let uu___3 = FStarC_Options.silent () in Prims.not uu___3 in
                  if uu___2
                  then
                    FStarC_Format.print1
                      "Attempting to translate module %s\n" m_name
                  else ());
                 (let uu___2 = translate_module ue m in
                  FStar_Pervasives_Native.Some uu___2))) ()
       with
       | uu___ ->
           ((let uu___2 = FStarC_Util.print_exn uu___ in
             FStarC_Format.print2
               "Unable to translate module: %s because:\n  %s\n" m_name
               uu___2);
            FStar_Pervasives_Native.None)) modules
let _init_krml : unit=
  register_post_translate_type_without_decay translate_type_without_decay';
  register_post_translate_type translate_type';
  register_post_translate_type_decl translate_type_decl';
  register_post_translate_expr translate_expr'
