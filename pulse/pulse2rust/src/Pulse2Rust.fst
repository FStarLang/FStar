module Pulse2Rust

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax

open RustBindings

module S = FStar.Extraction.ML.Syntax

module UEnv = FStar.Extraction.ML.UEnv

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

let rec uncurry_arrow (t:S.mlty) : (list S.mlty & S.mlty) =
  match t with
  | S.MLTY_Fun (t1, _, t2) ->
    let arg_ts, ret_t = uncurry_arrow t2 in
    t1::arg_ts, ret_t
  | _ -> ([], t)

let extract_mlty (t:S.mlty) : typ =
  match t with
  | S.MLTY_Var s -> Typ_name (tyvar_of s)
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt32.t" -> Typ_name "u32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int32.t" -> Typ_name "i32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt64.t" -> Typ_name "u64"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int64.t" -> Typ_name "i64"
  | S.MLTY_Erased -> Typ_name "unit"
  | _ -> fail_nyi (format1 "mlty %s" (S.mlty_to_string t))

let extract_top_level_fn_arg (arg_name:string) (t:S.mlty) : fn_arg =
  match t with
  | S.MLTY_Var s -> mk_scalar_fn_arg arg_name (Typ_name (tyvar_of s))
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt32.t" ||
         S.string_of_mlpath p = "FStar.Int32.t"  ||
         S.string_of_mlpath p = "FStar.UInt64.t" ||
         S.string_of_mlpath p = "FStar.Int64.t" -> mk_scalar_fn_arg arg_name (extract_mlty t)

  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Reference.ref" ->
    let is_mut = true in
    mk_ref_fn_arg arg_name is_mut (extract_mlty arg)

  | S.MLTY_Erased ->
    mk_scalar_fn_arg arg_name (Typ_name "unit")
  
  | _ -> fail_nyi (format1 "top level fn arg %s" (S.mlty_to_string t))


let extract_top_level_sig
  (fn_name:string)
  (tvars:S.mlidents)
  (arg_names:list string)
  (arg_ts:list S.mlty)
  (ret_t:S.mlty)
  
  : fn_signature =

  let fn_args =
    List.map2 extract_top_level_fn_arg (List.map varname arg_names) arg_ts in
  let fn_ret_t = extract_mlty ret_t in
  mk_fn_signature fn_name tvars fn_args fn_ret_t

let arg_ts_and_ret_t (t:S.mltyscheme) : S.mlidents & list S.mlty & S.mlty =
  let tvars, t = t in
  match t with
  | S.MLTY_Fun (_, S.E_PURE, _)
  | S.MLTY_Fun (_, S.E_IMPURE, _) ->
    let arg_ts, ret_t = uncurry_arrow t in
    tvars, arg_ts, ret_t
  | _ -> fail_nyi (format1 "top level arg_ts and ret_t %s" (S.mlty_to_string t))

let rec extract_mlexpr (e:S.mlexpr) : expr =
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
  | S.MLE_Let _ -> e |> extract_mlexpr_to_stmts |> mk_block_expr
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals" ->
    let e1 = extract_mlexpr e1 in
    let e2 = extract_mlexpr e2 in
    mk_ref_assign e1 e2
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Bang" ->
    let e = extract_mlexpr e in
    mk_ref_read e
  | S.MLE_App (head, args) ->
    let head = extract_mlexpr head in
    let args = List.map extract_mlexpr args in
    mk_call head args
  | S.MLE_TApp (head, _) -> extract_mlexpr head  // make type applications explicit in the Rust code?
  | _ -> fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

and extract_mlexpr_to_stmts (e:S.mlexpr) : list stmt =
  match e.expr with
  | S.MLE_Const S.MLC_Unit -> []
  | S.MLE_Var x -> [Stmt_expr (Expr_path (varname x))]
  | S.MLE_Name p -> [Stmt_expr (Expr_path (S.mlpath_to_string p))]
  | S.MLE_Let ((S.NonRec, [lb]), e) ->
    let is_mut = false in
    let s = mk_local_stmt lb.mllb_name is_mut (extract_mlexpr lb.mllb_def) in
    s::(extract_mlexpr_to_stmts e)
  | _ -> fail_nyi (format1 "mlexpr_to_stmt  %s" (S.mlexpr_to_string e))

let extract_top_level_lb (lbs:S.mlletbinding) : fn =
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
    
    let fn_sig = extract_top_level_sig lb.mllb_name (List.map tyvar_of tvars) arg_names arg_ts ret_t in
    let fn_body = extract_mlexpr_to_stmts body in

    mk_fn fn_sig fn_body
  end

let extract_one (file:string) : unit =
  let (gamma, decls)  : (list UEnv.binding & S.mlmodule) =
    match load_value_from_file file with
    | Some r -> r
    | None -> failwith "Could not load file" in
  List.iter (fun d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    match d with
    | S.MLM_Let lb ->
      let f = extract_top_level_lb lb in
      print_string "Extracted to:\n";
      print_string (RustBindings.fn_to_string f ^ "\n")
    | _ -> fail_nyi (format1 "top level decl %s" (S.mlmodule1_to_string d))
  ) decls

let extract (files:list string) : unit =
  List.iter extract_one files
