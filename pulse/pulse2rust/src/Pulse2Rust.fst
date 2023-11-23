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
//
// We keep the is_mut flag in the binding in gamma
// We use it to extract !x in pulse to x in rust
//   for a mutable local x
//
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

//
// A very shallow type checker for rust ast terms
// For now this is used only for variables,
//   to see whether a variable is mut
// Later, this may be used to insert coercions (e.g., &)
//
let type_of (g:env) (e:expr) : typ & bool =  // is_mut
  match e with
  | Expr_path [s] ->
    (match lookup_local g s with
     | Some (t, b) -> t, b
     | None -> fail (format1 "lookup in env for %s" s))

  | _ -> fail_nyi (format1 "type_of %s" (expr_to_string e))

//
// rust functions are uncurried
//
let rec uncurry_arrow (t:S.mlty) : (list S.mlty & S.mlty) =
  match t with
  | S.MLTY_Fun (t1, _, t2) ->
    let arg_ts, ret_t = uncurry_arrow t2 in
    t1::arg_ts, ret_t
  | _ -> ([], t)

//
// Most translations are straightforward
//
// Array.array t is extracted to &mut [t]
//   we need to figure permissions better
//
let rec extract_mlty (g:env) (t:S.mlty) : typ =
  let mk_slice (is_mut:bool) (t:S.mlty) =
    t |> extract_mlty g |> mk_slice_typ |> mk_ref_typ is_mut in

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
    when S.string_of_mlpath p = "Pulse.Lib.Box.box" ->
    arg |> extract_mlty g |> mk_box_typ
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.array" ->
    let is_mut = true in
    mk_slice is_mut arg
  | S.MLTY_Named ([arg; _], p)
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.larray" ->
    let is_mut = true in
    mk_slice is_mut arg
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Vec.vec" ->
    arg |> extract_mlty g |> mk_vec_typ
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "FStar.Pervasives.Native.option" ->
    arg |> extract_mlty g |> mk_option_typ
  | S.MLTY_Erased -> mk_scalar_typ "unit"

  | S.MLTY_Named (args, p) ->
    mk_named_typ (snd p) (List.map (extract_mlty g) args)

  | _ -> fail_nyi (format1 "mlty %s" (S.mlty_to_string t))

let extract_top_level_fn_arg (g:env) (arg_name:string) (t:S.mlty) : fn_arg =
  t |> extract_mlty g |> mk_scalar_fn_arg arg_name

let push_fn_arg (g:env) (arg_name:string) (arg:fn_arg) : env =
  match arg with
  | Fn_arg_pat { pat_typ_typ } ->
    let is_mut = false in
    push_local g arg_name pat_typ_typ false

//
// Top level function signature extraction
//
// The returned env is for extracting the body
//   with function parameters in scope
//
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

let arg_ts_and_ret_t (t:S.mltyscheme)
  : S.mlidents &   // type parameters
    list S.mlty &  // function argument types (after uncurrying the input type)
    S.mlty =       // function return type
  let tvars, t = t in
  match t with
  | S.MLTY_Fun (_, S.E_PURE, _)
  | S.MLTY_Fun (_, S.E_IMPURE, _) ->
    let arg_ts, ret_t = uncurry_arrow t in
    tvars, arg_ts, ret_t
  | _ -> fail_nyi (format1 "top level arg_ts and ret_t %s" (S.mlty_to_string t))

//
// TODO: add machine integers binops?
//
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

let extract_mlconstant_to_lit (c:S.mlconstant) : lit =
  match c with 
  | S.MLC_Int (lit_int_val, swopt) ->
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
      | Some (_, FStar.Const.Sizet) -> Some I64  // TODO: FIXME
      | None -> None in
    Lit_int {lit_int_val; lit_int_signed; lit_int_width}
  | S.MLC_Bool b -> Lit_bool b
  | _ -> fail_nyi (format1 "mlconstant_to_lit %s" (S.mlconstant_to_string c))


let rec extract_mlpattern_to_pat (p:S.mlpattern) : pat =
  match p with
  | S.MLP_Wild -> Pat_wild
  | S.MLP_Const c -> Pat_lit (extract_mlconstant_to_lit c)
  | S.MLP_Var x -> mk_pat_ident (varname x)
  | S.MLP_CTor (p, ps) ->
    mk_pat_ts (snd p) (List.map extract_mlpattern_to_pat ps)
  | _ -> fail_nyi (format1 "mlpattern_to_pat %s" (S.mlpattern_to_string p))

//
// Given an mllb,
//   compute the rust let binding mut flag, typ, and initializer
//
// If the mllb has Mutable flag, this means either a Tm_WithLocal or Tm_WithLocalArray in pulse
//
// Tm_WithLocal in pulse looks like (in mllb): let x : ref t = alloc e, where e : t
// So we return true, extract t, extract e
//
// Tm_WithLocalArray in pulse looks like (in mllb): let x : array t = alloc init len
// So we return false, extract (array t), mk_mutable_ref (repeat (extract init) (extract len))
// Basically, a local array in pulse becomes a mutable reference to a slice in rust
// Note that the let binding itself is immutable, but the slice is mutable
//
// If the mllb does not have Mutable flag, but the initializer is Vec::alloc or Box::alloc,
//   we extract it as: let mut x = std::vec::new(...) or std::boxed::Box::new(...)
// So we return true, extract (vec t), extract (Vec::alloc (...)), or
//              true, extract (box t), extract (Box::new (...))
//
let rec lb_init_and_def (g:env) (lb:S.mllb)
  : bool &       // whether the let binding in rust should be mut
    typ &        // type of the let binder
    expr =       // init expression
  
  let is_mut = contains S.Mutable lb.mllb_meta in
  if is_mut
  then
    match lb.mllb_def.expr, lb.mllb_tysc with
    | S.MLE_App ({expr=S.MLE_Name pe}, [init]),
      Some ([], S.MLTY_Named ([ty], pt))
      when S.string_of_mlpath pe = "Pulse.Lib.Reference.alloc" &&
           S.string_of_mlpath pt = "Pulse.Lib.Reference.ref" ->
      is_mut,
      extract_mlty g ty,
      extract_mlexpr g init

    | S.MLE_App ({expr=S.MLE_Name pe}, [init; len]),
      Some ([], S.MLTY_Named ([ty], pt))
      when S.string_of_mlpath pe = "Pulse.Lib.Array.Core.alloc" &&
           S.string_of_mlpath pt = "Pulse.Lib.Array.Core.array" ->
      let init = extract_mlexpr g init in
      let len = extract_mlexpr g len in
      let is_mut = false in
      is_mut,
      lb.mllb_tysc |> must |> snd |> extract_mlty g,
      mk_reference_expr true (mk_repeat init len)

    | _ ->
      fail (format1 "unexpected initializer for mutable local: %s" (S.mlexpr_to_string lb.mllb_def))

  else
    let is_mut =
      match lb.mllb_def.expr with
      | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _) ->
        S.string_of_mlpath p = "Pulse.Lib.Vec.alloc" ||
        S.string_of_mlpath p = "Pulse.Lib.Box.alloc"
      | _ -> false in
    is_mut,
    lb.mllb_tysc |> must |> snd |> extract_mlty g,
    extract_mlexpr g lb.mllb_def

//
// We have two mutually recursive functions:
//   extract_mlexpr and extract_mlexpr_to_stmts
// The top-level starts with the latter
// Nested let bindings are extracted as block expressions in rust
//
and extract_mlexpr (g:env) (e:S.mlexpr) : expr =
  match e.expr with
  | S.MLE_Const (S.MLC_Unit) -> mk_expr_path_singl "unitv"
    //
    // Must come after unit,
    //   no unit extraction in the lit function
    //
  | S.MLE_Const c ->
    let lit = extract_mlconstant_to_lit c in
    Expr_lit lit
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.SizeT.uint_to_t" ->
    extract_mlexpr g e

  | S.MLE_Var x -> mk_expr_path_singl (varname x)
  | S.MLE_Name p -> mk_expr_path_singl (snd p)

    // nested let binding
  | S.MLE_Let _ -> e |> extract_mlexpr_to_stmts g |> mk_block_expr

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Colon_Equals" ->
    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let _, b = type_of g e1 in
    if b
    then mk_assign e1 e2
    else mk_ref_assign e1 e2
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Bang" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Bang" ->
    let e = extract_mlexpr g e in
    let _, b = type_of g e in
    if b then e
    else mk_ref_read e
  
    //
    // box_as_ref e extracted to &mut e
    //
    // We need to figure out permissions
    //
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Box.box_to_ref" ->

    let e = extract_mlexpr g e in
    let is_mut = true in
    mk_reference_expr is_mut e

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Box.alloc" ->
    let e = extract_mlexpr g e in
    mk_call (mk_expr_path (["std"; "boxed"; "Box"; "new"])) [e]


  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; i; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Access" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Access"  ->

    mk_expr_index (extract_mlexpr g e) (extract_mlexpr g i)

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; e3; _])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Assignment" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Assignment" ->

    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let e3 = extract_mlexpr g e3 in
    mk_assign (mk_expr_index e1 e2) e3

    //
    // vec_as_array e extracted to &mut e
    //
    // We need to figure out permissions
    //
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Vec.vec_to_array" ->

    let e = extract_mlexpr g e in
    let is_mut = true in
    mk_reference_expr is_mut e

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
    when S.string_of_mlpath p = "Pulse.Lib.Vec.alloc" ->
    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    mk_call (mk_expr_path_singl vec_new_fn) [e1; e2]

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.alloc" ->

    fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _])
    when S.string_of_mlpath p = "Pulse.Lib.Vec.free" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.free" ->
    let e = extract_mlexpr g e in
    mk_call (mk_expr_path_singl "drop") [e]

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.free" ->

    fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

  | S.MLE_App ({expr=S.MLE_Name p}, [{expr=S.MLE_Fun (_, cond)}; {expr=S.MLE_Fun (_, body)}])
    when S.string_of_mlpath p = "Pulse.Lib.Core.while_" ->
    let expr_while_cond = extract_mlexpr g cond in
    let expr_while_body = extract_mlexpr_to_stmts g body in
    Expr_while {expr_while_cond; expr_while_body}

  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
    when S.string_of_mlpath p = "failwith" ->
    mk_call (mk_expr_path_singl panic_fn) []

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

  | S.MLE_Match (e, branches) ->
    let e = extract_mlexpr g e in
    mk_match e (List.map (extract_mlbranch_to_arm g) branches)

  | S.MLE_Coerce (e, _, _) -> extract_mlexpr g e  // TODO: FIXME: perhaps cast in Rust?

  | S.MLE_Record (p, fields) ->
    mk_expr_struct p (List.map (fun (f, e) -> f, extract_mlexpr g e) fields)

  | S.MLE_Proj (e, p) -> mk_expr_field (extract_mlexpr g e) (snd p)

  | _ -> fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

and extract_mlexpr_to_stmts (g:env) (e:S.mlexpr) : list stmt =

  let is_assign (e:S.mlexpr) =
    match e.expr with
    | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _) ->
      S.string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals"
    | _ -> false
  in

  match e.expr with
  | S.MLE_Const S.MLC_Unit -> []
  | S.MLE_Var x -> [Stmt_expr (mk_expr_path_singl (varname x))]
  | S.MLE_Name p -> [Stmt_expr (mk_expr_path_singl (S.mlpath_to_string p))]

  | S.MLE_Let ((S.NonRec, [{mllb_def=e1}]), e2)
    when is_assign e1 ->
    (Stmt_expr (extract_mlexpr g e1))::(extract_mlexpr_to_stmts g e2)

  | S.MLE_Let ((S.NonRec, [lb]), e) ->
    let is_mut, ty, init = lb_init_and_def g lb in
    let s = mk_local_stmt lb.mllb_name is_mut init in
    s::(extract_mlexpr_to_stmts (push_local g lb.mllb_name ty is_mut) e)

  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
    when S.string_of_mlpath p = "failwith" ->
    [Stmt_expr (mk_call (mk_expr_path_singl panic_fn) [])]
  | _ -> fail_nyi (format1 "mlexpr_to_stmt  %s" (S.mlexpr_to_string e))

and extract_mlbranch_to_arm (g:env) ((pat, pat_guard, body):S.mlbranch) : arm =
  match pat_guard with
  | Some e -> fail_nyi (format1 "mlbranch_to_arm with pat guard %s" (S.mlexpr_to_string e))
  | None ->
    let pat = extract_mlpattern_to_pat pat in
    let arm_body = extract_mlexpr g body in
    mk_arm pat arm_body

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
    // print1 "Typescheme is: %s\n\n" (S.mltyscheme_to_string tsc);
    // print1 "lbdef is: %s\n\n" (S.mlexpr_to_string lb.mllb_def);
    let arg_names, body =
      match lb.mllb_def.expr with
      | S.MLE_Fun (bs, body) ->
        List.map fst bs, body
      | _ -> fail_nyi (format1 "top level lb def %s" (S.mlexpr_to_string lb.mllb_def))
    in
    
    let tvars, arg_ts, ret_t = arg_ts_and_ret_t tsc in
    
    // print3 "tvars: %s, arg_ts: %s, ret_t: %s\n"
    //   (String.concat ", " tvars)
    //   (String.concat ", " (List.map S.mlty_to_string arg_ts))
    //   (S.mlty_to_string ret_t);

    let fn_sig, g_body = extract_top_level_sig g lb.mllb_name (List.map tyvar_of tvars) arg_names arg_ts ret_t in
    let fn_body = extract_mlexpr_to_stmts g_body body in

    mk_fn fn_sig fn_body,
    push_fv g lb.mllb_name fn_sig
  end

// let extract_struct_defn (g:env) (d:S.mlmodule1) : item & env =
//   match d with
//   | S.MLM_Ty [ d ] ->
//     let Some (S.MLTD_Record fts) = d.tydecl_defn in
//     mk_item_struct
//       d.tydecl_name
//       d.tydecl_parameters
//       (List.map (fun (f, t) -> f, extract_mlty g t) fts),
//     g  // TODO: add it to env if needed later

let extract_one (file:string) : unit =
  let (gamma, decls)  : (list UEnv.binding & S.mlmodule) =
    match load_value_from_file file with
    | Some r -> r
    | None -> failwith "Could not load file" in
  
  let items, _ = List.fold_left (fun (items, g) d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    match d with
    | S.MLM_Let lb ->
      let f, g = extract_top_level_lb g lb in
      // print_string "Extracted to:\n";
      // print_string (RustBindings.fn_to_rust f ^ "\n");
      items@[Item_fn f],
      g
    | S.MLM_Loc _ -> items, g
    // | S.MLM_Ty [ {tydecl_defn = Some (S.MLTD_Record _)} ] ->
    //   let item, g = extract_struct_defn g d in
    //   items@[item], g
    | _ -> fail_nyi (format1 "top level decl %s" (S.mlmodule1_to_string d))
  ) ([], empty_env ()) decls in
  
  let f = mk_file "a.rs" items in
  let s = RustBindings.file_to_rust f in
  print_string (s ^ "\n")

let extract (files:list string) : unit =
  List.iter extract_one files
