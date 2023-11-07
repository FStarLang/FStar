module Pulse2Rust

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax

open RustBindings

module S = FStar.Extraction.ML.Syntax

module UEnv = FStar.Extraction.ML.UEnv

type var = string
type binding = var & typ & bool // name, type, is_mut

type env = {
  fvs : list (string & fn_signature);
  gamma : list binding;
}

//
// 'a to A
//
let tyvar_of (s:string) : string =
  String.uppercase (String.substring s 1 (String.length s - 1))

//
// Pulse has variable _'n, which are not valid in Rust
//
let varname (s:string) : string = replace_char s '\'' '_'

let fail (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: %s" s)

let fail_nyi (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: no support yet for %s" s)

let empty_env () = { fvs = []; gamma = [] }

let lookup_global_fn (g:env) (s:string) : option fn_signature =
  map_option (fun (_, t) -> t) (tryFind (fun (f, _) -> f = s) g.fvs)

let lookup_local (g:env) (s:string) : option (typ & bool) =
  map_option (fun (_, t, b) -> t, b) (tryFind (fun (x, _, _) -> x = s) g.gamma)

let push_fv (g:env) (s:string) (t:fn_signature) : env =
  { g with fvs = (s, t)::g.fvs }

let push_local (g:env) (s:string) (t:typ) (is_mut:bool) : env =
  { g with gamma = (s, t, is_mut)::g.gamma }

let type_of (g:env) (e:expr) : typ & bool =  // is_mut
  match e with
  | Expr_path s ->
    (match lookup_local g s with
     | Some (t, b) -> t, b
     | None -> fail (format1 "lookup in env for %s" s))

  | _ -> fail_nyi (format1 "type_of %s" (expr_to_string e))

let rec uncurry_arrow (t:S.mlty) : (list S.mlty & S.mlty) =
  match t with
  | S.MLTY_Fun (t1, _, t2) ->
    let arg_ts, ret_t = uncurry_arrow t2 in
    t1::arg_ts, ret_t
  | _ -> ([], t)

let rec extract_mlty (g:env) (t:S.mlty) : typ =
  match t with
  | S.MLTY_Var s -> mk_scalar_typ (tyvar_of s)
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt32.t" -> mk_scalar_typ "u32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int32.t" -> mk_scalar_typ "i32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt64.t" -> mk_scalar_typ "u64"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int64.t" ||
         S.string_of_mlpath p = "Prims.int"     ||
         S.string_of_mlpath p = "Prims.nat" -> mk_scalar_typ "i64"  // TODO: int to int64, nat to int64, FIX
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.SizeT.t" -> mk_scalar_typ "usize"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "Prims.bool" -> mk_scalar_typ "bool"
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Reference.ref" ->
    let is_mut = true in
    arg |> extract_mlty g |> mk_ref_typ is_mut
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Rust.Slice.slice" ->
    let is_mut = true in
    arg |> extract_mlty g |> mk_slice_typ |> mk_ref_typ is_mut
  | S.MLTY_Erased -> mk_scalar_typ "unit"
  | _ -> fail_nyi (format1 "mlty %s" (S.mlty_to_string t))

let extract_top_level_fn_arg (g:env) (arg_name:string) (t:S.mlty) : fn_arg =
  t |> extract_mlty g |> mk_scalar_fn_arg arg_name
  // match t with
  // | S.MLTY_Var s -> mk_scalar_fn_arg arg_name (mk_scalar_typ (tyvar_of s))
  // | S.MLTY_Named ([], p)
  //   when S.string_of_mlpath p = "FStar.UInt32.t" ||
  //        S.string_of_mlpath p = "FStar.Int32.t"  ||
  //        S.string_of_mlpath p = "FStar.UInt64.t" ||
  //        S.string_of_mlpath p = "FStar.Int64.t"  ||
  //        S.string_of_mlpath p = "Prims.int"      ||
  //        S.string_of_mlpath p = "Prims.nat"      ||
  //        S.string_of_mlpath p = "Prims.bool" ->
  //   mk_scalar_fn_arg arg_name (extract_mlty g t)

  // | S.MLTY_Named ([arg], p)
  //   when S.string_of_mlpath p = "Pulse.Lib.Reference.ref" ->
  //   mk_scalar_fn_arg arg_name (extract_mlty g t)

  // | S.MLTY_Erased ->
  //   mk_scalar_fn_arg arg_name (extract_mlty g t)
  
  // | _ -> fail_nyi (format1 "top level fn arg %s" (S.mlty_to_string t))

let push_fn_arg (g:env) (arg_name:string) (arg:fn_arg) : env =
  match arg with
  | Fn_arg_pat { pat_typ_typ } ->
    let is_mut = false in
    push_local g arg_name pat_typ_typ false

let extract_top_level_sig
  (g:env)
  (fn_name:string)
  (tvars:S.mlidents)
  (arg_names:list string)
  (arg_ts:list S.mlty)
  (ret_t:S.mlty)
  
  : fn_signature & env =

  let fn_args =
    List.map2 (extract_top_level_fn_arg g) (List.map varname arg_names) arg_ts in
  let fn_ret_t = extract_mlty g ret_t in
  mk_fn_signature fn_name tvars fn_args fn_ret_t,
  fold_left (fun g (arg_name, arg) -> push_fn_arg g arg_name arg) g (zip arg_names fn_args)

let arg_ts_and_ret_t (t:S.mltyscheme) : S.mlidents & list S.mlty & S.mlty =
  let tvars, t = t in
  match t with
  | S.MLTY_Fun (_, S.E_PURE, _)
  | S.MLTY_Fun (_, S.E_IMPURE, _) ->
    let arg_ts, ret_t = uncurry_arrow t in
    tvars, arg_ts, ret_t
  | _ -> fail_nyi (format1 "top level arg_ts and ret_t %s" (S.mlty_to_string t))

let is_binop (s:string) : option binop =
  if s = "Prims.op_Addition"
  then Some Add
  else if s = "Prims.op_Subtraction"
  then Some Sub
  else if s = "Prims.op_disEquality"
  then Some Ne
  else if s = "Prims.op_LessThanOrEqual"
  then Some Le
  else if s = "Prims.op_LessThan"
  then Some Lt
  else if s = "Prims.op_GreaterThanOrEqual"
  then Some Ge
  else if s = "Prims.op_GreaterThan"
  then Some Gt
  else if s = "Prims.op_Equality"
  then Some Eq
  else None

let rec extract_mlexpr (g:env) (e:S.mlexpr) : expr =
  match e.expr with
  | S.MLE_Const (S.MLC_Unit) -> Expr_path "unitv"
  | S.MLE_Const (S.MLC_Int (lit_int_val, swopt)) ->
    let lit_int_signed =
      match swopt with
      | Some (FStar.Const.Unsigned, _) -> Some false
      | Some (FStar.Const.Signed, _) -> Some true
      | None -> None in
    let lit_int_width =
      match swopt with
      | Some (_, FStar.Const.Int8) -> Some I8
      | Some (_, FStar.Const.Int16) -> Some I16
      | Some (_, FStar.Const.Int32) -> Some I32
      | Some (_, FStar.Const.Int64) -> Some I64
      | None -> None in
    Expr_lit (Lit_int {lit_int_val; lit_int_signed; lit_int_width})

  | S.MLE_Var x -> Expr_path (varname x)
  | S.MLE_Name p -> Expr_path (snd p)
  | S.MLE_Let _ -> e |> extract_mlexpr_to_stmts g |> mk_block_expr
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals" ->
    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let _, b = type_of g e1 in
    if b
    then mk_assign e1 e2
    else mk_ref_assign e1 e2
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Bang" ->
    let e = extract_mlexpr g e in
    let _, b = type_of g e in
    if b then e
    else mk_ref_read e
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; i; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Rust.Slice.op_Array_Access" ->
    mk_expr_index (extract_mlexpr g e) (extract_mlexpr g i)
  | S.MLE_App ({expr=S.MLE_Name p}, [{expr=S.MLE_Fun (_, cond)}; {expr=S.MLE_Fun (_, body)}])
    when S.string_of_mlpath p = "Pulse.Lib.Core.while_" ->
    let expr_while_cond = extract_mlexpr g cond in
    let expr_while_body = extract_mlexpr_to_stmts g body in
    Expr_while {expr_while_cond; expr_while_body}
  | S.MLE_App ({expr=S.MLE_Name p}, [e1; e2])
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
    when p |> S.string_of_mlpath |> is_binop |> Some? ->
    let e1 = extract_mlexpr g e1 in
    let op = p |> S.string_of_mlpath |> is_binop |> must in
    let e2 = extract_mlexpr g e2 in
    mk_binop e1 op e2

  | S.MLE_App (head, args) ->
    let head = extract_mlexpr g head in
    let args = List.map (extract_mlexpr g) args in
    mk_call head args
  | S.MLE_TApp (head, _) -> extract_mlexpr g head  // make type applications explicit in the Rust code?
  | S.MLE_If (cond, if_then, if_else_opt) ->
    let cond = extract_mlexpr g cond in
    let then_ = extract_mlexpr_to_stmts g if_then in
    let else_ = map_option (extract_mlexpr g) if_else_opt in
    //
    // make sure that else is either another if or block
    //
    let else_ =
      match else_ with
      | None
      | Some (Expr_if _)
      | Some (Expr_block _) -> else_
      | Some else_ -> Some (mk_block_expr [Stmt_expr else_]) in 
    mk_if cond then_ else_
  | _ -> fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

and extract_mlexpr_to_stmts (g:env) (e:S.mlexpr) : list stmt =
  match e.expr with
  | S.MLE_Const S.MLC_Unit -> []
  | S.MLE_Var x -> [Stmt_expr (Expr_path (varname x))]
  | S.MLE_Name p -> [Stmt_expr (Expr_path (S.mlpath_to_string p))]
  | S.MLE_Let ((S.NonRec, [lb]), e) ->
    let is_mut = contains S.Mutable lb.mllb_meta in
    let init, ty =
      if is_mut
      then
        let init =
          match lb.mllb_def.expr with
          | S.MLE_App ({expr=S.MLE_Name p}, [init])
            when S.string_of_mlpath p = "Pulse.Lib.Reference.alloc" -> init
          | _ -> fail (format1 "unexpected initializer for mutable local: %s" (S.mlexpr_to_string lb.mllb_def))
        in
        let ty =
          match lb.mllb_tysc with
          | Some ([], S.MLTY_Named ([ty], p))
            when S.string_of_mlpath p = "Pulse.Lib.Reference.ref" ->
            ty
          | _ -> fail (format1 "unexpected type of mutable local: %s" (S.mltyscheme_to_string (must lb.mllb_tysc))) in
        init, ty
      else lb.mllb_def,
           snd (must lb.mllb_tysc) in
    let s = mk_local_stmt lb.mllb_name is_mut (extract_mlexpr g init) in
    s::(extract_mlexpr_to_stmts (push_local g lb.mllb_name (extract_mlty g ty) is_mut) e)
  | _ -> fail_nyi (format1 "mlexpr_to_stmt  %s" (S.mlexpr_to_string e))

let extract_top_level_lb (g:env) (lbs:S.mlletbinding) : fn & env =
  let is_rec, lbs = lbs in
  if is_rec = S.Rec
  then fail_nyi "recursive let bindings"
  else begin
    let [lb] = lbs in
    if None? lb.mllb_tysc
    then fail (format1 "unexpected: mllb_tsc is None for %s" lb.mllb_name);
    //
    // if tsc is not set, we could get the arg types from the fun inside
    //
    let Some tsc = lb.mllb_tysc in
    let arg_names, body =
      match lb.mllb_def.expr with
      | S.MLE_Fun (bs, body) ->
        List.map fst bs, body
      | _ -> fail_nyi (format1 "top level lb def %s" (S.mlexpr_to_string lb.mllb_def))
    in
    
    let tvars, arg_ts, ret_t = arg_ts_and_ret_t tsc in
    
    let fn_sig, g_body = extract_top_level_sig g lb.mllb_name (List.map tyvar_of tvars) arg_names arg_ts ret_t in
    let fn_body = extract_mlexpr_to_stmts g_body body in

    mk_fn fn_sig fn_body,
    push_fv g lb.mllb_name fn_sig
  end

let extract_one (file:string) : unit =
  let (gamma, decls)  : (list UEnv.binding & S.mlmodule) =
    match load_value_from_file file with
    | Some r -> r
    | None -> failwith "Could not load file" in
  let _ = List.fold_left (fun g d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    match d with
    | S.MLM_Let lb ->
      let f, g = extract_top_level_lb g lb in
      print_string "Extracted to:\n";
      print_string (RustBindings.fn_to_rust f ^ "\n");
      g
    | S.MLM_Loc _ -> g
    | _ -> fail_nyi (format1 "top level decl %s" (S.mlmodule1_to_string d))
  ) (empty_env ()) decls in
  ()

let extract (files:list string) : unit =
  List.iter extract_one files
