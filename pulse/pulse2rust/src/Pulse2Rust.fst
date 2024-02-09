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

module Pulse2Rust

open FStar.Compiler
open FStar.Compiler.Util
open FStar.Compiler.List
open FStar.Compiler.Effect

open Pulse2Rust.Rust.Syntax

open RustBindings

module S = FStar.Extraction.ML.Syntax
module EUtil = FStar.Extraction.ML.Util

module UEnv = FStar.Extraction.ML.UEnv

type var = string
//
// We keep the is_mut flag in the binding in gamma
// We use it to extract !x in pulse to x in rust
//   for a mutable local x
//
type binding = var & typ & bool // name, type, is_mut
type reachable_defs = Set.set string

let reachable_defs_to_string (d:reachable_defs) : string =
  d |> Set.elems |> String.concat ";" |> format1 "[%s]"

type env = {
  fns : list (string & fn_signature);
  statics : list (string & typ);
  gamma : list binding;
  record_field_names : psmap (list string);
  reachable_defs : reachable_defs
}

//
// 'a to A
//
let tyvar_of (s:string) : string =
  String.uppercase (String.substring s 1 (String.length s - 1))

//
// Pulse has variable _'n, which are not valid in Rust
//
let varname (s:string) : string =
  replace_char s '\'' '_'

let enum_or_struct_name (s:string) : string = s
  // let hd::tl = String.list_of_string s in
  // String.string_of_list ((FStar.Char.uppercase hd)::tl)

let is_internal_name (s:string) : bool =
  starts_with s "uu___" ||
  s = "_fret" ||
  s = "_bind_c" ||
  s = "_while_c" ||
  s = "_while_b" ||
  s = "_if_br"

let fail (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: %s" s)

let fail_nyi (s:string) =
  failwith (format1 "Pulse to Rust extraction failed: no support yet for %s" s)

let empty_env (reachable_defs:reachable_defs) =
  { fns = []; gamma = []; statics = []; record_field_names = psmap_empty (); reachable_defs }

let lookup_global_fn (g:env) (s:string) : option fn_signature =
  map_option (fun (_, t) -> t) (tryFind (fun (f, _) -> f = s) g.fns)

let lookup_local (g:env) (s:string) : option (typ & bool) =
  map_option (fun (_, t, b) -> t, b) (tryFind (fun (x, _, _) -> x = s) g.gamma)

let push_fn (g:env) (s:string) (t:fn_signature) : env =
  { g with fns = (s, t)::g.fns }

let push_static (g:env) (s:string) (t:typ) : env =
  { g with statics = (s, t)::g.statics }

let push_local (g:env) (s:string) (t:typ) (is_mut:bool) : env =
  { g with gamma = (s, t, is_mut)::g.gamma }

//
// A very shallow type checker for rust ast terms
// For now this is used only for variables,
//   to see whether a variable is mut
// Later, this may be used to insert coercions (e.g., &)
//
let type_of (g:env) (e:expr) : bool =  // is_mut
  match e with
  | Expr_path [s] ->
    (match lookup_local g s with
     | Some (_t, b) -> b
     | None -> fail (format1 "lookup in env for %s" s))
  
  | _ -> false

  // | _ -> fail_nyi (format1 "type_of %s" (expr_to_string e))

//
// rust functions are uncurried
//
let rec uncurry_arrow (t:S.mlty) : (list S.mlty & S.mlty) =
  match t with
  | S.MLTY_Fun (t1, _, t2) ->
    let arg_ts, ret_t = uncurry_arrow t2 in
    t1::arg_ts, ret_t
  | _ -> ([], t)

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
    when S.string_of_mlpath p = "FStar.UInt8.t" -> mk_scalar_typ "u8"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt32.t" -> mk_scalar_typ "u32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int32.t" -> mk_scalar_typ "i32"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt64.t" -> mk_scalar_typ "u64"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "Prims.string" -> mk_scalar_typ "String"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.Int64.t" ||
         S.string_of_mlpath p = "Prims.int"     ||
         S.string_of_mlpath p = "Prims.nat" -> mk_scalar_typ "i64"  // TODO: int to int64, nat to int64, FIX
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.SizeT.t" -> mk_scalar_typ "usize"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "Prims.bool" -> mk_scalar_typ "bool"
  | S.MLTY_Named (l, p)
    when S.string_of_mlpath p = "FStar.Pervasives.Native.tuple2" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.tuple3" ->
    mk_tuple_typ (List.map (extract_mlty g) l)
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
  | S.MLTY_Named (arg::_, p)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.mutex" ->
    arg |> extract_mlty g |> mk_mutex_typ
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "FStar.Pervasives.Native.option" ->
    arg |> extract_mlty g |> mk_option_typ
  | S.MLTY_Erased -> Typ_unit

  | S.MLTY_Named (args, p) ->
    mk_named_typ (snd p) (List.map (extract_mlty g) args)

  | S.MLTY_Fun _ ->
    let _, arg_ts, ret_t = arg_ts_and_ret_t ([], t) in
    mk_fn_typ (List.map (extract_mlty g) arg_ts) (extract_mlty g ret_t)

  | S.MLTY_Top -> Typ_infer

  | _ -> fail_nyi (format1 "mlty %s" (S.mlty_to_string t))

let extract_mltyopt (g:env) (t:option S.mlty) : typ =
  match t with
  | None -> Typ_infer
  | Some t -> extract_mlty g t

let arg_has_mut_attribute (attrs:list S.mlexpr) : bool =
  List.existsb (fun attr ->
    match attr.S.expr with
    | S.MLE_CTor (p, _)
      when S.string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_mut_binder" -> true
    | _ -> false
  ) attrs

let extract_top_level_fn_arg (g:env) (arg_name:string) (arg_attrs:list S.mlexpr) (t:S.mlty) : fn_arg =
  mk_scalar_fn_arg
    arg_name
    (arg_has_mut_attribute arg_attrs)
    (t |> extract_mlty g) 

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
  (fn_const:bool)
  (fn_name:string)
  (generic_type_params:list generic_type_param)
  (arg_names:list string)
  (arg_attrs:list (list S.mlexpr))
  (arg_ts:list S.mlty)
  (ret_t:option S.mlty)
  
  : fn_signature & env =

  let fn_args =
    List.map3 (extract_top_level_fn_arg g) (List.map varname arg_names) arg_attrs arg_ts in
  let fn_ret_t = extract_mltyopt g ret_t in
  mk_fn_signature
    fn_const
    fn_name
    generic_type_params
    fn_args
    fn_ret_t,
  fold_left (fun g (arg_name, arg) -> push_fn_arg g arg_name arg) g (zip arg_names fn_args)

//
// TODO: add machine integers binops?
//
let is_binop (s:string) : option binop =
  if s = "Prims.op_Addition" ||
     s = "FStar.UInt32.add" ||
     s = "FStar.SizeT.add"
  then Some Add
  else if s = "Prims.op_Subtraction" ||
          s = "FStar.SizeT.sub" ||
          s = "FStar.UInt32.sub"
  then Some Sub
  else if s = "Prims.op_Multiply" ||
          s = "FStar.Mul.op_Star" ||
          s = "FStar.UInt32.mul" ||
          s = "FStar.UInt32.op_Star_Hat" ||
          s = "FStar.SizeT.mul" ||
          s = "FStar.SizeT.op_Star_Hat"
  then Some Mul
  else if s = "Prims.op_disEquality"
  then Some Ne
  else if s = "Prims.op_LessThanOrEqual" ||
          s = "FStar.UInt32.lte" ||
          s = "FStar.SizeT.lte"
  then Some Le
  else if s = "Prims.op_LessThan" ||
          s = "FStar.UInt32.lt" ||
          s = "FStar.SizeT.lt"
  then Some Lt
  else if s = "Prims.op_GreaterThanOrEqual" ||
          s = "FStar.UInt32.gte" ||
          s = "FStar.SizeT.gte"
  then Some Ge
  else if s = "Prims.op_GreaterThan" ||
          s = "FStar.UInt32.gt" ||
          s = "FStar.SizeT.gt"
  then Some Gt
  else if s = "Prims.op_Equality"
  then Some Eq
  else if s = "Prims.rem" ||
          s = "FStar.UInt32.rem" ||
          s = "FStar.SizeT.rem"
  then Some Rem
  else if s = "Prims.op_AmpAmp"
  then Some And
  else if s = "Prims.op_BarBar"
  then Some Or
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
  | S.MLC_String s -> Lit_string s
  | _ -> fail_nyi (format1 "mlconstant_to_lit %s" (S.mlconstant_to_string c))

let rec extract_mlpattern_to_pat (g:env) (p:S.mlpattern) : env & pat =
  match p with
  | S.MLP_Wild -> g, Pat_wild
  | S.MLP_Const c -> g, Pat_lit (extract_mlconstant_to_lit c)
  | S.MLP_Var x ->
    push_local g x Typ_infer false,
    (if is_internal_name x
     then Pat_wild
     else mk_pat_ident (varname x))
  | S.MLP_CTor (p, ps)
    when snd p = "Mktuple2" ||
         snd p = "Mktuple3" ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g ps in
    g,
    mk_pat_tuple ps
  | S.MLP_CTor (p, ps) ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g ps in
    g,
    mk_pat_ts (snd p) ps
  | S.MLP_Record (p, fs) ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g (List.map snd fs) in
    g,
    mk_pat_struct (List.last p) (zip (List.map fst fs) ps)
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
  | S.MLE_Const (S.MLC_Unit) -> Expr_lit Lit_unit
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

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tfst" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.fst" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 0
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tsnd" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.snd" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 1
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tthd" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 2

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [_; e])
    when starts_with (snd p) "explode_ref_" ->
    let n = String.length "explode_ref_" in
    let rname = String.substring (snd p) n (String.length (snd p) - n) in
    let flds = psmap_try_find g.record_field_names rname in
    let flds = flds |> must in
    let e = extract_mlexpr g e in
    let es = flds |> List.map (fun f -> mk_reference_expr true (mk_expr_field e f)) in
    mk_expr_tuple es

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Colon_Equals" ->
    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let b = type_of g e1 in
    if b
    then mk_assign e1 e2
    else mk_ref_assign e1 e2
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.op_Bang" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Bang" ->
    let e = extract_mlexpr g e in
    let b = type_of g e in
    if b then e
    else mk_ref_read e
  
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.ref_apply" ->

    mk_call (extract_mlexpr g e1) [extract_mlexpr g e2]
 
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
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Access" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.read_ref" ->

    mk_expr_index (extract_mlexpr g e) (extract_mlexpr g i)

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e1::e2::e3::_)
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Assignment" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Assignment" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.write_ref" ->

    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let e3 = extract_mlexpr g e3 in
    mk_assign (mk_expr_index e1 e2) e3

  | S.MLE_App ({ expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e_v::e_i::e_x::_)
    when S.string_of_mlpath p = "Pulse.Lib.Vec.replace_i" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.replace_i_ref" ->

    let e_v = extract_mlexpr g e_v in
    let e_i = extract_mlexpr g e_i in
    let e_x = extract_mlexpr g e_x in
    let is_mut = true in
    mk_mem_replace (mk_reference_expr is_mut (mk_expr_index e_v e_i)) e_x

  | S.MLE_App ({ expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e_r::e_x::_)
    when S.string_of_mlpath p = "Pulse.Lib.Reference.replace" ->
   
    mk_mem_replace (extract_mlexpr g e_r) (extract_mlexpr g e_x)

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

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.new_mutex" ->
    let e = extract_mlexpr g e in
    mk_new_mutex e
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.lock" ->
    let e = extract_mlexpr g e in
    mk_lock_mutex e

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.free" ->

    fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

  | S.MLE_App ({expr=S.MLE_Name p}, [{expr=S.MLE_Fun (_, cond)}; {expr=S.MLE_Fun (_, body)}])
    when S.string_of_mlpath p = "Pulse.Lib.Core.while_" ->
    let expr_while_cond = extract_mlexpr g cond in
    let expr_while_body = extract_mlexpr_to_stmts g body in
    Expr_while {expr_while_cond; expr_while_body}

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, _::e::_)
    when S.string_of_mlpath p = "DPE.run_stt" ->  // TODO: FIXME
    extract_mlexpr g e

  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
  | S.MLE_App ({expr=S.MLE_Name p}, _)
    when S.string_of_mlpath p = "failwith" ||
         S.string_of_mlpath p = "Pulse.Lib.Core.unreachable" ->
    mk_call (mk_expr_path_singl panic_fn) []

  | S.MLE_App ({expr=S.MLE_Name p}, [e1; e2])

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
  | S.MLE_App ({expr=S.MLE_Name p}, [e1; e2])
    when p |> S.string_of_mlpath |> is_binop |> Some? ->
    let e1 = extract_mlexpr g e1 in
    let op = p |> S.string_of_mlpath |> is_binop |> must in
    let e2 = extract_mlexpr g e2 in
    mk_binop e1 op e2

  | S.MLE_App (head, args) ->
    let head = extract_mlexpr g head in
    let args = List.map (extract_mlexpr g) args in
    mk_call head args

  | S.MLE_CTor (p, args) ->
    let is_native =
      S.mlpath_to_string p = "FStar.Pervasives.Native.Some" ||
      S.mlpath_to_string p = "FStar.Pervasives.Native.None" in
    let ty_name =
      match e.mlty with
      | S.MLTY_Named (_, p) -> p |> snd |> enum_or_struct_name
      | _ -> failwith "S.MLE_CTor: unexpected type" in
    let dexpr =
      if is_native then mk_expr_path_singl (snd p)
      else mk_expr_path [ty_name; snd p] in
    if List.length args = 0
    then dexpr
    else mk_call dexpr (List.map (extract_mlexpr g) args)

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

  | S.MLE_Record (_, nm, fields) ->
    mk_expr_struct [nm] (List.map (fun (f, e) -> f, extract_mlexpr g e) fields)

  | S.MLE_Proj (e, p) -> mk_expr_field (extract_mlexpr g e) (snd p)

  | S.MLE_Tuple l -> mk_expr_tuple (List.map (extract_mlexpr g) l)

  | _ -> fail_nyi (format1 "mlexpr %s" (S.mlexpr_to_string e))

and extract_mlexpr_to_stmts (g:env) (e:S.mlexpr) : list stmt =
  match e.expr with
  | S.MLE_Const S.MLC_Unit -> []

  | S.MLE_Let ((_, [{mllb_def = {expr = S.MLE_Const S.MLC_Unit }}]), e) ->
    extract_mlexpr_to_stmts g e

  | S.MLE_Let ((S.NonRec, [lb]), e) ->
    begin
      match lb.mllb_def.expr with
      | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, _)
        when starts_with (snd p) "unexplode_ref" ||
             S.mlpath_to_string p = "Pulse.Lib.Mutex.unlock" ->
        extract_mlexpr_to_stmts g e
      | _ ->
        let is_mut, ty, init = lb_init_and_def g lb in
        let topt =
          match lb.mllb_def.expr with
          | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::e::_)
            when S.string_of_mlpath p = "Pulse.Lib.Mutex.lock" ->
            Some ty
          | _ -> None in 
        let s = mk_local_stmt
          (match lb.mllb_tysc with
           | Some (_, S.MLTY_Erased) -> None
           | _ -> Some (varname lb.mllb_name))
          topt
          is_mut
          init in
        s::(extract_mlexpr_to_stmts (push_local g lb.mllb_name ty is_mut) e)
    end


  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
    when S.string_of_mlpath p = "failwith" ->
    [Stmt_expr (mk_call (mk_expr_path_singl panic_fn) [])]

  | _ -> [Stmt_expr (extract_mlexpr g e)]

and extract_mlbranch_to_arm (g:env) ((pat, pat_guard, body):S.mlbranch) : arm =
  match pat_guard with
  | Some e -> fail_nyi (format1 "mlbranch_to_arm with pat guard %s" (S.mlexpr_to_string e))
  | None ->
    let g, pat = extract_mlpattern_to_pat g pat in
    let arm_body = extract_mlexpr g body in
    mk_arm pat arm_body

let has_rust_const_fn_attribute (lb:S.mllb) : bool =
  List.existsb (fun attr ->
    match attr.S.expr with
    | S.MLE_CTor (p, _)
      when S.string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_const_fn" -> true
    | _ -> false
  ) lb.mllb_attrs

let extract_generic_type_param_trait_bounds_aux (attrs:list S.mlexpr) : list (list (list string)) =
  let open S in
  attrs
  |> List.tryFind (fun attr ->
       match attr.expr with
       | MLE_CTor (p, _)
         when string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_generics_bounds" -> true
       | _ -> false)
  |> map_option (fun attr ->
       let MLE_CTor (p, args) = attr.expr in
       let Some l = EUtil.list_elements (List.hd args) in
       l |> List.map (fun tyvar_bounds ->
              let Some l = EUtil.list_elements tyvar_bounds in
              l |> List.map (fun e ->
                     match e.expr with
                     | MLE_Const (MLC_String s) -> s
                     | _ -> failwith "unexpected generic type param bounds")
                |> List.map (fun bound -> FStar.Compiler.Util.split bound "::")))
  |> dflt []

let expand_list_with (#a:Type) (l:list a) (n:nat) (x:a) : list a =
  let rec nlist (n:nat) (x:a) : list a =
    if n = 0 then [] else x::(nlist (n - 1) x) in
  if n <= List.length l
  then l
  else l @ (nlist (n - List.length l) x)

let extract_generic_type_param_trait_bounds (n:nat) (attrs:list S.mlattribute)
  : list (list (list string)) =

  let l = extract_generic_type_param_trait_bounds_aux attrs in
  expand_list_with l n []

let extract_generic_type_params (tyvars:list S.mlident) (attrs:list S.mlattribute)
  : list generic_type_param =

  attrs
  |> extract_generic_type_param_trait_bounds (List.length tyvars)
  |> List.map2 (fun tvar bounds -> mk_generic_type_param (tyvar_of tvar) bounds) tyvars  

let extract_top_level_lb (g:env) (lbs:S.mlletbinding) : item & env =
  let is_rec, lbs = lbs in
  if is_rec = S.Rec
  then fail_nyi "recursive let bindings"
  else begin
    let [lb] = lbs in
    
    match lb.mllb_def.expr with
    | S.MLE_Fun (bs, body) ->
      let arg_names = List.map (fun b -> b.S.mlbinder_name) bs in
      let arg_attrs = List.map (fun b -> b.S.mlbinder_attrs) bs in
      let tvars, arg_ts, ret_t =
        match lb.mllb_tysc with
        | Some tsc ->
          let tvars, arg_ts, ret_t = arg_ts_and_ret_t tsc in
          tvars, arg_ts, Some ret_t
        | None ->
          [], List.map (fun b -> b.S.mlbinder_ty) bs, None in

      let fn_const = has_rust_const_fn_attribute lb in
      let fn_sig, g_body =
        extract_top_level_sig 
          g
          fn_const
          lb.mllb_name
          (extract_generic_type_params tvars lb.mllb_attrs)
          arg_names
          arg_attrs
          arg_ts
          ret_t in
      let fn_body = extract_mlexpr_to_stmts g_body body in

      Item_fn (mk_fn fn_sig fn_body),
      push_fn g lb.mllb_name fn_sig
    
    | _ ->
      match lb.mllb_tysc with
      | Some ([], ty) ->
        let name = lb.mllb_name in
        let ty = extract_mlty g ty in
        (mk_item_static name ty (extract_mlexpr g lb.mllb_def)),
        push_static g name ty
      | _ ->
        fail_nyi (format1 "top level lb def with either no tysc or generics %s" (S.mlexpr_to_string lb.mllb_def))
  end

  //   let tvars, arg_ts, ret_t 

  //   if None? lb.mllb_tysc
  //   then fail (format1 "unexpected: mllb_tsc is None for %s" lb.mllb_name);
  //   //
  //   // if tsc is not set, we could get the arg types from the fun inside
  //   //
  //   let Some tsc = lb.mllb_tysc in
  //   // print1 "Typescheme is: %s\n\n" (S.mltyscheme_to_string tsc);
  //   // print1 "lbdef is: %s\n\n" (S.mlexpr_to_string lb.mllb_def);
  //   let arg_names, body =
  //     match lb.mllb_def.expr with
  //     | S.MLE_Fun (bs, body) ->
  //       List.map fst bs, body
  //     | _ -> fail_nyi (format1 "top level lb def %s" (S.mlexpr_to_string lb.mllb_def))
  //   in
    
  //   let tvars, arg_ts, ret_t = arg_ts_and_ret_t tsc in
    
  //   // print3 "tvars: %s, arg_ts: %s, ret_t: %s\n"
  //   //   (String.concat ", " tvars)
  //   //   (String.concat ", " (List.map S.mlty_to_string arg_ts))
  //   //   (S.mlty_to_string ret_t);

  //   let fn_sig, g_body = extract_top_level_sig g lb.mllb_name (List.map tyvar_of tvars) arg_names arg_ts ret_t in
  //   let fn_body = extract_mlexpr_to_stmts g_body body in

  //   mk_fn fn_sig fn_body,
  //   push_fv g lb.mllb_name fn_sig
  // end

let has_rust_derive_attr (attrs:list S.mlattribute) : option attribute =
  attrs
    |> List.tryFind (fun attr ->
       match attr.S.expr with
       | S.MLE_CTor (p, _)
         when S.string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_derive" -> true
       | _ -> false)
    |> map_option (fun attr ->
       let S.MLE_CTor (p, arg::_) = attr.S.expr in
       let S.MLE_Const (S.MLC_String s) = arg.S.expr in
       mk_derive_attr s)

let extract_struct_defn (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_Record fts) = d.tydecl_defn in
  // print1 "Adding to record field with %s\n" d.tydecl_name;
  mk_item_struct
    (attrs |> has_rust_derive_attr |> map_option (fun a -> [a]) |> dflt [])
    (d.tydecl_name |> enum_or_struct_name)
    (extract_generic_type_params d.tydecl_parameters attrs)
    (List.map (fun (f, t) -> f, extract_mlty g t) fts),
  { g with record_field_names = psmap_add g.record_field_names d.tydecl_name (List.map fst fts) }

let extract_type_abbrev (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_Abbrev t) = d.tydecl_defn in
  mk_item_type
    d.tydecl_name
    (extract_generic_type_params d.tydecl_parameters attrs)
    (extract_mlty g t),
  g

let extract_enum (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_DType cts) = d.tydecl_defn in
  // print1 "enum attrs: %s\n" (String.concat ";" (List.map S.mlexpr_to_string attrs));
  mk_item_enum
    (attrs |> has_rust_derive_attr |> map_option (fun a -> [a]) |> dflt [])
    (d.tydecl_name |> enum_or_struct_name)
    (extract_generic_type_params d.tydecl_parameters attrs)
    (List.map (fun (cname, dts) -> cname, List.map (fun (_, t) -> extract_mlty g t) dts) cts),
  g  // TODO: add it to env if needed later

let extract_mltydecl (g:env) (mlattrs:list S.mlexpr) (d:S.mltydecl) : list item & env =
  List.fold_left (fun (items, g) d ->
    let f =
      match d.S.tydecl_defn with
      | Some (S.MLTD_Abbrev _) -> extract_type_abbrev
      | Some (S.MLTD_Record _) -> extract_struct_defn
      | Some (S.MLTD_DType _) -> extract_enum
      | _ -> fail_nyi (format1 "mltydecl %s" (S.one_mltydecl_to_string d))
    in
    let item, g = f g mlattrs d in
    items@[item], g) ([], g) d


let empty_defs : reachable_defs = Set.empty ()
let singleton (p:S.mlpath) : reachable_defs = Set.singleton (S.string_of_mlpath p)

let reachable_defs_list (#a:Type) (f:a -> reachable_defs) (l:list a) : reachable_defs =
  List.fold_left (fun defs x -> Set.union defs (f x)) (Set.empty ()) l

let reachable_defs_option (#a:Type) (f:a -> reachable_defs) (o:option a) : reachable_defs =
  match o with
  | None -> empty_defs
  | Some x -> f x

let rec reachable_defs_mlty (t:S.mlty) : reachable_defs =
  let open S in
  match t with
  | MLTY_Var _ -> empty_defs
  | MLTY_Fun (t1, _, t2) -> Set.union (reachable_defs_mlty t1) (reachable_defs_mlty t2)
  | MLTY_Named (tps, p) ->
    Set.union (reachable_defs_list reachable_defs_mlty tps) (singleton p)
  | MLTY_Tuple ts -> reachable_defs_list reachable_defs_mlty ts
  | MLTY_Top
  | MLTY_Erased -> empty_defs

let reachable_defs_mltyscheme ((_, t):S.mltyscheme) : reachable_defs =
  reachable_defs_mlty t

let rec reachable_defs_mlpattern (p:S.mlpattern) : reachable_defs =
  let open S in
  match p with
  | MLP_Wild
  | MLP_Const _
  | MLP_Var _ -> empty_defs
  | MLP_CTor (c, ps) ->
    Set.union (singleton c) (reachable_defs_list reachable_defs_mlpattern ps)
  | MLP_Branch ps -> reachable_defs_list reachable_defs_mlpattern ps
  | MLP_Record (syms, fs) ->
    Set.union (Set.singleton (String.concat "." syms))
              (reachable_defs_list (fun (_, p) -> reachable_defs_mlpattern p) fs)
  | MLP_Tuple ps -> reachable_defs_list reachable_defs_mlpattern ps

let rec reachable_defs_expr' (e:S.mlexpr') : reachable_defs =
  let open S in
  match e with
  | MLE_Const _
  | MLE_Var _ -> empty_defs
  | MLE_Name p -> singleton p
  | MLE_Let (lb, e) -> Set.union (reachable_defs_mlletbinding lb) (reachable_defs_expr e)
  | MLE_App (e, es) ->
    Set.union (reachable_defs_expr e) (reachable_defs_list reachable_defs_expr es)
  | MLE_TApp (e, ts) ->
    Set.union (reachable_defs_expr e) (reachable_defs_list reachable_defs_mlty ts)
  | MLE_Fun (args, e) ->
    Set.union (reachable_defs_list (fun b -> reachable_defs_mlty b.S.mlbinder_ty) args)
              (reachable_defs_expr e)
  | MLE_Match (e, bs) ->
    Set.union (reachable_defs_expr e)
              (reachable_defs_list reachable_defs_mlbranch bs)
  | MLE_Coerce (e, t1, t2) ->
    Set.union (reachable_defs_expr e)
              (Set.union (reachable_defs_mlty t1) (reachable_defs_mlty t2))
  | MLE_CTor (p, es) ->
    Set.union (singleton p)
               (reachable_defs_list reachable_defs_expr es)
  | MLE_Seq es
  | MLE_Tuple es -> reachable_defs_list reachable_defs_expr es
  | MLE_Record (p, n, fs) ->
    Set.union (Set.singleton (String.concat "." (p@[n])))
              (reachable_defs_list (fun (_, e) -> reachable_defs_expr e) fs)
  | MLE_Proj (e, _) -> reachable_defs_expr e
  | MLE_If (e1, e2, e3_opt) ->
    Set.union (reachable_defs_expr e1)
              (Set.union (reachable_defs_expr e2)
                         (reachable_defs_option reachable_defs_expr e3_opt))
  | MLE_Raise (p, es) ->
    Set.union (singleton p)
              (reachable_defs_list reachable_defs_expr es)
  | MLE_Try (e, bs) -> Set.union (reachable_defs_expr e)
                                 (reachable_defs_list reachable_defs_mlbranch bs)

and reachable_defs_expr (e:S.mlexpr) : reachable_defs =
  Set.union (reachable_defs_expr' e.expr)
            (reachable_defs_mlty e.mlty)

and reachable_defs_mlbranch ((p, wopt, e):S.mlbranch) : reachable_defs =
  Set.union (reachable_defs_mlpattern p)
            (Set.union (reachable_defs_option reachable_defs_expr wopt)
                       (reachable_defs_expr e))

and reachable_defs_mllb (lb:S.mllb) : reachable_defs =
  Set.union (reachable_defs_option reachable_defs_mltyscheme lb.mllb_tysc)
            (reachable_defs_expr lb.mllb_def)

and reachable_defs_mlletbinding ((_, lbs):S.mlletbinding) : reachable_defs =
  reachable_defs_list reachable_defs_mllb lbs

let reachable_defs_mltybody (t:S.mltybody) : reachable_defs =
  let open S in
  match t with
  | MLTD_Abbrev t -> reachable_defs_mlty t
  | MLTD_Record fs ->
    reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) fs
  | MLTD_DType cts ->
    reachable_defs_list (fun (_, dts) -> reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) dts) cts

let reachable_defs_one_mltydecl (t:S.one_mltydecl) : reachable_defs =
  reachable_defs_option reachable_defs_mltybody t.tydecl_defn

let reachable_defs_mltydecl (t:S.mltydecl) : reachable_defs =
  reachable_defs_list reachable_defs_one_mltydecl t

let mlmodule1_name (m:S.mlmodule1) : list S.mlsymbol =
  let open S in
  match m.mlmodule1_m with
  | MLM_Ty l -> List.map (fun t -> t.tydecl_name) l
  | MLM_Let (_, lbs) -> List.map (fun lb -> lb.mllb_name) lbs
  | MLM_Exn (s, _) -> [s]
  | MLM_Top _
  | MLM_Loc _ -> []

let reachable_defs_mlmodule1 (m:S.mlmodule1) : reachable_defs =
  let open S in
  let defs =
    match m.mlmodule1_m with
    | MLM_Ty t -> reachable_defs_mltydecl t
    | MLM_Let lb -> reachable_defs_mlletbinding lb
    | MLM_Exn (_, args) ->
      reachable_defs_list (fun (_, t) -> reachable_defs_mlty t) args
    | MLM_Top e -> reachable_defs_expr e
    | MLM_Loc _ -> empty_defs in
  // print2 "reachable defs for %s are %s\n"
    // (S.mlmodule1_to_string m)
    // (reachable_defs_to_string defs);
  defs

let reachable_defs_decls (decls:S.mlmodule) : reachable_defs =
  reachable_defs_list reachable_defs_mlmodule1 decls

let decl_reachable (reachable_defs:reachable_defs) (mname:string) (d:S.mlmodule1) : bool =
  let open S in
  match d.mlmodule1_m with
  | MLM_Ty t ->
    List.existsb (fun ty_decl ->Set.mem (mname ^ "." ^ ty_decl.tydecl_name) reachable_defs) t
  | MLM_Let (_, lbs) ->
    List.existsb (fun lb -> Set.mem (mname ^ "." ^ lb.mllb_name) reachable_defs) lbs
  | MLM_Exn (p, _) -> false
  | MLM_Top _ -> false
  | MLM_Loc _ -> false

let extract_one
  (g:env)
  (mname:string)
  (gamma:list UEnv.binding)
  (decls:S.mlmodule) : string & env =
  // let (deps, gamma, decls)  : (list string & list UEnv.binding & S.mlmodule) =
  //   match load_value_from_file file with
  //   | Some r -> r
  //   | None -> failwith "Could not load file" in

  // print2 "Loaded file %s with deps: %s\n" file (String.concat "; " deps);  
  let items, env = List.fold_left (fun (items, g) d ->
    // print1 "Decl: %s\n" (S.mlmodule1_to_string d);
    // print1 "Decl deps: %s\n"
    //   (String.concat "\n" (reachable_defs_mlmodule1 d |> Set.elems));
    if not (decl_reachable g.reachable_defs mname d)
    then begin
      // print1 "decl %s is not reachable\n" (String.concat ";" (mlmodule1_name d));
      // if mname = "Pulse.Lib.HashTable.Type"
      // then print1 "decl %s is not reachable\n" (S.mlmodule1_to_string d);
      items, g
    end
    else
    // let _ = print1 "decl %s is reachable\n" (String.concat ";" (mlmodule1_name d)) in
    //
    // NOTE: Rust extraction of discriminators doesn't work for unit variants
    //       (i.e. variants that do not have payloads)
    //       Because we always have a wild card argument to these patterns in discriminator body
    //       In OCaml it works fine.
    //       In Rust it is an error
    //       Should fix it in a better way
    //       For now, just not extracting them ... that too with a hack on names
    //
    match d.S.mlmodule1_m with
    | S.MLM_Let (S.NonRec, [{mllb_name}])
      when starts_with mllb_name "explode_ref" ||
           starts_with mllb_name "unexplode_ref" ||
           starts_with mllb_name "uu___is_" ||
           starts_with mllb_name "__proj__" -> items, g
    | S.MLM_Let lb ->
      let f, g = extract_top_level_lb g lb in
      // print_string "Extracted to:\n";
      // print_string (RustBindings.fn_to_rust f ^ "\n");
      items@[f],
      g
    | S.MLM_Loc _ -> items, g
    | S.MLM_Ty td ->
      let d_items, g = extract_mltydecl g d.S.mlmodule1_attrs td in
      items@d_items, g
    | _ -> fail_nyi (format1 "top level decl %s" (S.mlmodule1_to_string d))
  ) ([], g) decls in
  
  let f = mk_file "a.rs" items in
  let s = RustBindings.file_to_rust f in
  s, env

// let collect_reachable_defs (files:list string) (roots:list string) : reachable_defs =
//   let files = List.filter (fun x -> List.mem x roots) files in
//   reachable_defs_list (fun f ->
//     let (_, _, decls)  : (list string & list UEnv.binding & S.mlmodule) =
//       match load_value_from_file f with
//       | Some r -> r
//       | None -> failwith "Could not load file" in
//     reachable_defs_mlmodule decls) files

let file_to_module_name (f:string) : string =
  let suffix = ".ast" in
  let s = basename f in
  let s = String.substring s 0 (String.length s - String.length suffix) in
  replace_chars s '_' "."

type dict = smap (list string & list UEnv.binding & S.mlmodule)

let rec topsort (d:dict) (grey:list string) (black:list string) (root:string)
  : (list string & list string) =  // grey and black
  let grey = root::grey in
  let deps = root |> smap_try_find d |> must |> (fun (deps, _, _) -> deps) in
  let deps = deps |> List.filter (fun f -> List.mem f (smap_keys d) && not (f = root)) in
  if List.existsb (fun d -> List.mem d grey) deps
  then failwith (format1 "cyclic dependency: %s" root);
  let deps = deps |> List.filter (fun f -> not (List.mem f black)) in
  let grey, black = List.fold_left (fun (grey, black) dep ->
    topsort d grey black dep) (grey, black) deps in
  List.filter (fun g -> not (g = root)) grey,
  (if List.mem root black then black else root::black)

let rec topsort_all (d:dict) (black:list string)
  : list string =
  
  if List.for_all (fun f -> List.contains f black) (smap_keys d)
  then black
  else
    let rem = List.filter (fun f -> not (List.contains f black)) (smap_keys d) in
    let root = List.nth rem (List.length rem - 1) in
    let grey, black = topsort d [] black root in
    if List.length grey <> 0
    then failwith "topsort_all: not all files are reachable";
    topsort_all d black

let read_all_ast_files (files:list string) : dict =
  let d = smap_create 100 in
  files |> List.iter (fun f ->
    let contents  : (list string & list UEnv.binding & S.mlmodule) =
      match load_value_from_file f with
      | Some r -> r
      | None -> failwith (format1 "Could not load file %s" f) in
    smap_add d (file_to_module_name f) contents);
  d

let build_decls_dict (d:dict) : smap S.mlmodule1 =
  let dd = smap_create 100 in
  smap_iter d (fun module_nm (_, _, decls) ->
    List.iter (fun (decl:S.mlmodule1) ->
      List.iter (fun decl_nm ->
        smap_add dd (module_nm ^ "." ^ decl_nm) decl
      ) (mlmodule1_name decl)
    ) decls
  );
  dd

let rec collect_reachable_defs_aux
  (dd:smap S.mlmodule1)
  (worklist:reachable_defs)
  (reachable_defs:reachable_defs) =

  if Set.is_empty worklist
  then reachable_defs
  else let hd::_ = Set.elems worklist in
       let worklist = Set.remove hd worklist in
      //  print1 "Adding %s to reachable_defs\n" hd;
       let reachable_defs = Set.add hd reachable_defs in
       let worklist =
         let hd_decl = smap_try_find dd hd in
         match hd_decl with
         | None -> worklist
         | Some hd_decl ->
           let hd_reachable_defs = reachable_defs_mlmodule1 hd_decl in
           hd_reachable_defs |> Set.elems |> List.fold_left (fun worklist def ->
             if Set.mem def reachable_defs ||
                Set.mem def worklist
             then worklist
             else Set.add def worklist
           ) worklist in
       collect_reachable_defs_aux dd worklist reachable_defs

let collect_reachable_defs (d:dict) (root_module:string) : reachable_defs =
  let dd = build_decls_dict d in
  let root_decls = smap_try_find d root_module |> must |> (fun (_, _, decls) -> decls) in
  let worklist = List.fold_left (fun worklist decl ->
    Set.addn
      (decl |> mlmodule1_name |> List.map (fun s -> root_module ^ "." ^ s))
      worklist
  ) empty_defs root_decls in
  collect_reachable_defs_aux dd worklist empty_defs

let extract (files:list string) : string =
  let d = read_all_ast_files files in
  //
  // reversed order in which decls should be emitted,
  //   i.e., main function first
  //
  let all_modules = topsort_all d [] in
  print1 "order: %s\n" (String.concat "; " all_modules);
  let root_module::_ = all_modules in
  // let reachable_defs : reachable_defs = empty_defs in
  let reachable_defs = collect_reachable_defs d root_module in
  // let root_decls = smap_try_find d root_module |> must |> (fun (_, _, decls) -> decls) in
  // let reachable_defs =
  //   List.fold_left (fun reachable_defs decl ->
  //     let nms = mlmodule1_name decl in
  //     List.fold_left (fun reachable_defs nm ->
  //       Set.union reachable_defs (Set.singleton (root_module ^ "." ^ nm))
  //     ) reachable_defs nms
  //   ) reachable_defs root_decls
  // in
  // print1 "Root reachable defs: %s\n" (reachable_defs_to_string reachable_defs);
  // // print1 "Before:%s\n" (String.concat ";" (reachable_defs |> Set.elems));
  // let reachable_defs =
  //   List.fold_left (fun reachable_defs m ->
  //     let m_decls = smap_try_find d m |> must |> (fun (_, _, decls) -> decls) in
  //     let m_decls = List.filter (fun d ->
  //       let nms = mlmodule1_name d in
  //       List.existsb (fun nm -> Set.mem (m ^ "." ^ nm) reachable_defs) nms
  //     ) m_decls in
  //     Set.union reachable_defs (reachable_defs_decls m_decls)
  //   ) reachable_defs all_modules
  // in

  let g = empty_env reachable_defs in
  let s = List.fold_left_map (fun g f ->
    let (_, bs, ds) = smap_try_find d f |> must in
    let s, g = extract_one g f bs ds in
    g, s) g (List.rev all_modules) |> snd |> String.concat " " in
  s
