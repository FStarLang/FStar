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

module Pulse2Rust.Extract

open FStarC
open FStarC.Util
open FStarC.List
open FStarC.Effect

open Pulse2Rust.Rust.Syntax
open Pulse2Rust.Env

open RustBindings

module S = FStarC.Extraction.ML.Syntax
module EUtil = FStarC.Extraction.ML.Util


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

let lookup_datacon_in_module1 (s:S.mlident) (m:S.mlmodule1) : option S.mlsymbol =
  match m.mlmodule1_m with
  | S.MLM_Ty l ->
    find_map l (fun t ->
      match t.tydecl_defn with
      | Some (S.MLTD_DType l) ->
        find_map l (fun (consname, _) -> if consname = s then Some t.tydecl_name else None)
      | _ -> None
    )
  | _ -> None

let lookup_datacon (g:env) (s:S.mlident) : option (list string & S.mlsymbol) =
  let d_keys = SMap.keys g.d in
  find_map d_keys (fun k ->
    let (_, _, decls) = SMap.try_find g.d k |> Option.must in
    let ropt = find_map decls (lookup_datacon_in_module1 s) in
    match ropt with
    | None -> None
    | Some tname -> Some (FStarC.Util.split k ".", tname)
  )

//
// A very shallow type checker for rust ast terms
// For now this is used only for variables,
//   to see whether a variable is mut
// Later, this may be used to insert coercions (e.g., &)
//
let type_of (g:env) (e:expr) : bool =  // is_mut
  match e with
  | Expr_path [{path_segment_name}] ->
    (match lookup_local g path_segment_name with
     | Some (_t, b) -> b
     | None -> fail (Format.fmt1 "lookup in env for %s" path_segment_name))
  
  | _ -> false

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
  : list S.ty_param &   // type parameters
    list S.mlty &  // function argument types (after uncurrying the input type)
    S.mlty =       // function return type
  let tvars, t = t in
  match t with
  | S.MLTY_Fun (_, S.E_PURE, _)
  | S.MLTY_Fun (_, S.E_IMPURE, _) ->
    let arg_ts, ret_t = uncurry_arrow t in
    tvars, arg_ts, ret_t
  | _ -> fail_nyi (Format.fmt1 "top level arg_ts and ret_t %s" (S.mlty_to_string t))

let should_extract_mlpath_with_symbol (g:env) (path:list S.mlsymbol) : bool =
  let p = String.concat "." path in
  let b =
    p = "Prims" || p = "Pulse.Lib.Pervasives" || p = "FStar.Pervasives.Native" ||
    p = "FStar.Pervasives" in
  not b
  // List.contains (String.concat "." path) g.all_modules

let rust_mod_name (path:list S.mlsymbol) : string =
  path |> List.map String.lowercase
       |> String.concat "_"  

let extract_path_for_symbol (g:env) (path:list S.mlsymbol) : list string =
  let prefix =
    if is_external_lib g (String.concat "." path)
    then "crate"
    else "super" in
  [ prefix; rust_mod_name path ]

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
    when S.string_of_mlpath p = "FStar.Char.char" -> mk_scalar_typ "char"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt8.t" -> mk_scalar_typ "u8"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.UInt16.t" -> mk_scalar_typ "u16"
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
         S.string_of_mlpath p = "Prims.nat"     ||
         S.string_of_mlpath p = "Prims.pos" -> mk_scalar_typ "i64"  // TODO: int to int64, nat to int64, FIX
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "FStar.SizeT.t" -> mk_scalar_typ "usize"
  | S.MLTY_Named ([], p)
    when S.string_of_mlpath p = "Prims.bool" -> mk_scalar_typ "bool"
  | S.MLTY_Named (l, p)
    when S.string_of_mlpath p = "FStar.Pervasives.Native.tuple2" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.tuple3" ||
         S.string_of_mlpath p = "Prims.dtuple2" ->
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
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Slice.slice" ->
    let is_mut = true in
    mk_slice is_mut arg
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "Pulse.Lib.Vec.vec" ->
    arg |> extract_mlty g |> mk_vec_typ
  | S.MLTY_Named (arg::_, p)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.mutex" ->
    arg |> extract_mlty g |> mk_mutex_typ
  | S.MLTY_Named (arg::_, p)
    when S.string_of_mlpath p = "Pulse.Lib.GlobalVar.gvar" ->
    arg |> extract_mlty g
  | S.MLTY_Named ([arg], p)
    when S.string_of_mlpath p = "FStar.Pervasives.Native.option" ->
    arg |> extract_mlty g |> mk_option_typ
  | S.MLTY_Erased -> Typ_unit

  | S.MLTY_Named (args, p) ->
    let path =
      if should_extract_mlpath_with_symbol g (fst p)
      then extract_path_for_symbol g (fst p)
      else [] in
    mk_named_typ path (snd p) (List.map (extract_mlty g) args)

  | S.MLTY_Fun _ ->
    let _, arg_ts, ret_t = arg_ts_and_ret_t ([], t) in
    mk_fn_typ (List.map (extract_mlty g) arg_ts) (extract_mlty g ret_t)

  | S.MLTY_Top -> Typ_infer

  | _ -> fail_nyi (Format.fmt1 "mlty %s" (S.mlty_to_string t))

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
     s = "FStar.UInt8.add" ||
     s = "FStar.UInt16.add" ||
     s = "FStar.UInt32.add" ||
     s = "FStar.UInt64.add" ||
     s = "FStar.SizeT.add"
  then Some Add
  else if s = "Prims.op_Subtraction" ||
          s = "FStar.SizeT.sub" ||
          s = "FStar.UInt8.sub" ||
          s = "FStar.UInt16.sub" ||
          s = "FStar.UInt32.sub" ||
          s = "FStar.UInt64.sub"
  then Some Sub
  else if s = "Prims.op_Multiply" ||
          s = "FStar.Mul.op_Star" ||
          s = "FStar.UInt8.mul" ||
          s = "FStar.UInt16.mul" ||
          s = "FStar.UInt32.mul" ||
          s = "FStar.UInt32.op_Star_Hat" ||
          s = "FStar.UInt64.mul" ||
          s = "FStar.SizeT.mul" ||
          s = "FStar.SizeT.op_Star_Hat"
  then Some Mul
  else if s = "Prims.op_disEquality"
  then Some Ne
  else if s = "Prims.op_LessThanOrEqual" ||
          s = "FStar.UInt8.lte" ||
          s = "FStar.UInt16.lte" ||
          s = "FStar.UInt32.lte" ||
          s = "FStar.UInt64.lte" ||
          s = "FStar.SizeT.lte"
  then Some Le
  else if s = "Prims.op_LessThan" ||
          s = "FStar.UInt8.lt" ||
          s = "FStar.UInt16.lt" ||
          s = "FStar.UInt32.lt" ||
          s = "FStar.UInt64.lt" ||
          s = "FStar.SizeT.lt"
  then Some Lt
  else if s = "Prims.op_GreaterThanOrEqual" ||
          s = "FStar.UInt8.gte" ||
          s = "FStar.UInt16.gte" ||
          s = "FStar.UInt32.gte" ||
          s = "FStar.UInt64.gte" ||
          s = "FStar.SizeT.gte"
  then Some Ge
  else if s = "Prims.op_GreaterThan" ||
          s = "FStar.UInt8.gt" ||
          s = "FStar.UInt16.gt" ||
          s = "FStar.UInt32.gt" ||
          s = "FStar.UInt64.gt" ||
          s = "FStar.SizeT.gt"
  then Some Gt
  else if s = "Prims.op_Equality"
  then Some Eq
  else if s = "Prims.rem" ||
          s = "FStar.UInt8.rem" ||
          s = "FStar.UInt16.rem" ||
          s = "FStar.UInt32.rem" ||
          s = "FStar.UInt64.rem" ||
          s = "FStar.SizeT.rem"
  then Some Rem
  else if s = "Prims.op_AmpAmp"
  then Some And
  else if s = "Prims.op_BarBar"
  then Some Or
  else if
    s = "FStar.UInt8.shift_left" ||
    s = "FStar.UInt16.shift_left" ||
    s = "FStar.UInt32.shift_left" ||
    s = "FStar.UInt64.shift_left"
  then Some Shl
  else if
    s = "FStar.UInt8.shift_right" ||
    s = "FStar.UInt16.shift_right" ||
    s = "FStar.UInt32.shift_right" ||
    s = "FStar.UInt64.shift_right"
  then Some Shr
  else if
    s = "FStar.UInt8.logor" ||
    s = "FStar.UInt16.logor" ||
    s = "FStar.UInt32.logor" ||
    s = "FStar.UInt64.logor"
  then Some BitOr
  else if
    s = "FStar.UInt8.logand" ||
    s = "FStar.UInt16.logand" ||
    s = "FStar.UInt32.logand" ||
    s = "FStar.UInt64.logand"
  then Some BitAnd
  else None

let extract_mlconstant_to_lit (c:S.mlconstant) : lit =
  match c with 
  | S.MLC_Int (lit_int_val, swopt) ->
    let lit_int_signed =
      match swopt with
      | Some (FStarC.Const.Unsigned, _) -> Some false
      | Some (FStarC.Const.Signed, _) -> Some true
      | None -> None in
    let lit_int_width =
      match swopt with
      | Some (_, FStarC.Const.Int8) -> Some I8
      | Some (_, FStarC.Const.Int16) -> Some I16
      | Some (_, FStarC.Const.Int32) -> Some I32
      | Some (_, FStarC.Const.Int64) -> Some I64
      | Some (_, FStarC.Const.Sizet) -> Some I64  // TODO: FIXME
      | None -> None in
    Lit_int {lit_int_val; lit_int_signed; lit_int_width}
  | S.MLC_Bool b -> Lit_bool b
  | S.MLC_String s -> Lit_string s
  | _ -> fail_nyi (Format.fmt1 "mlconstant_to_lit %s" (S.mlconstant_to_string c))

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
         snd p = "Mktuple3" ||
         snd p = "Mkdtuple2" ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g ps in
    g,
    mk_pat_tuple ps
  | S.MLP_CTor (p, ps) ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g ps in
    let path =
      let ropt = lookup_datacon g (snd p) in
      match ropt with
      | Some (l, t) ->
        if should_extract_mlpath_with_symbol g l
        then List.append (extract_path_for_symbol g l) [t]
        else []
      | None -> [] in
    g,
    mk_pat_ts path (snd p) ps
  | S.MLP_Record (p, fs) ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g (List.map snd fs) in
    g,
    mk_pat_struct (List.last p) (zip (List.map fst fs) ps)
  | S.MLP_Tuple ps ->
    let g, ps = fold_left_map extract_mlpattern_to_pat g ps in
    g, mk_pat_tuple ps
  | _ -> fail_nyi (Format.fmt1 "mlpattern_to_pat %s" (S.mlpattern_to_string p))

//
// Given an mllb,
//   compute the rust let binding mut flag, typ, and initializer
//
// Tm_WithLocal in pulse looks like (in mllb): let x : ref t = alloc e, where e : t
// So we return true, extract t, extract e
//
// Tm_WithLocalArray in pulse looks like (in mllb): let x : array t = alloc init len
// So we return false, extract (array t), mk_mutable_ref (repeat (extract init) (extract len))
// Basically, a local array in pulse becomes a mutable reference to a slice in rust
// Note that the let binding itself is immutable, but the slice is mutable
//
// If the initializer is Vec::alloc or Box::alloc,
//   we extract it as: let mut x = std::vec::new(...) or std::boxed::Box::new(...)
// So we return true, extract (vec t), extract (Vec::alloc (...)), or
//              true, extract (box t), extract (Box::new (...))
//
let rec lb_init_and_def (g:env) (lb:S.mllb)
  : bool &       // whether the let binding in rust should be mut
    typ &        // type of the let binder
    expr =       // init expression
  
    match lb.mllb_def.expr, lb.mllb_tysc with
    | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name pe}, _)}, [_; init]),
      Some ([], S.MLTY_Named ([ty], pt))
      when S.string_of_mlpath pe = "Pulse.Lib.Reference.alloc" &&
           S.string_of_mlpath pt = "Pulse.Lib.Reference.ref" ->
      let is_mut = true in
      is_mut,
      extract_mlty g ty,
      extract_mlexpr g init

    | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name pe}, _)}, [_; init; len; _; _]),
      Some ([], S.MLTY_Named ([ty], pt))
      when S.string_of_mlpath pe = "Pulse.Lib.Array.Core.mask_alloc_with_vis" &&
           S.string_of_mlpath pt = "Pulse.Lib.Array.Core.array" ->
      let init = extract_mlexpr g init in
      let len = extract_mlexpr g len in
      let is_mut = false in
      is_mut,
      lb.mllb_tysc |> Option.must |> snd |> extract_mlty g,
      mk_reference_expr true (mk_repeat init len)

    | _ ->

    let is_mut =
      match lb.mllb_def.expr with
      | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _) ->
        S.string_of_mlpath p = "Pulse.Lib.Vec.alloc" ||
        S.string_of_mlpath p = "Pulse.Lib.Box.alloc" ||
        S.string_of_mlpath p = "Pulse.Lib.Mutex.lock"
      | _ -> false in
    is_mut,
    lb.mllb_tysc |> Option.must |> snd |> extract_mlty g,
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
    let elit = extract_mlconstant_to_lit c |> Expr_lit in
    (match c with
     | S.MLC_String _ ->
       mk_method_call elit "to_string" [] 
     | _ -> elit)
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.SizeT.uint_to_t" ->
    extract_mlexpr g e
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.SizeT.uint16_to_sizet" ->
    mk_cast (extract_mlexpr g e) (mk_scalar_typ "usize")

  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.Int.Cast.uint16_to_uint8" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint32_to_uint8" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint64_to_uint8" ->
    mk_cast (extract_mlexpr g e) (mk_scalar_typ "u8")
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.Int.Cast.uint8_to_uint16" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint32_to_uint16" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint64_to_uint16" ->
    mk_cast (extract_mlexpr g e) (mk_scalar_typ "u16")
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.Int.Cast.uint8_to_uint32" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint16_to_uint32" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint64_to_uint32" ->
    mk_cast (extract_mlexpr g e) (mk_scalar_typ "u32")
  | S.MLE_App ({expr=S.MLE_Name p}, [e])
    when S.string_of_mlpath p = "FStar.Int.Cast.uint8_to_uint64" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint16_to_uint64" ||
         S.string_of_mlpath p = "FStar.Int.Cast.uint32_to_uint64" ->
    mk_cast (extract_mlexpr g e) (mk_scalar_typ "u64")

  | S.MLE_Var x -> mk_expr_path_singl (varname x)
  | S.MLE_Name p ->
    if should_extract_mlpath_with_symbol g (fst p)
    then mk_expr_path (List.append (extract_path_for_symbol g (fst p)) [snd p])
    else mk_expr_path_singl (snd p)

    // nested let binding
  | S.MLE_Let _ | S.MLE_Seq _ ->
    e |> extract_mlexpr_to_stmts g |> mk_block_expr

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tfst" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.__proj__Mktuple2__item___1" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.fst" ||
         S.string_of_mlpath p = "FStar.Pervasives.dfst" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 0
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tsnd" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.__proj__Mktuple2__item___2" ||
         S.string_of_mlpath p = "FStar.Pervasives.Native.snd" ||
         S.string_of_mlpath p = "FStar.Pervasives.dsnd" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 1
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, [e])
    when S.string_of_mlpath p = "Pulse.Lib.Pervasives.tthd" ->
    let e = extract_mlexpr g e in
    mk_expr_field_unnamed e 2

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.write" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Colon_Equals" ||
         S.string_of_mlpath p = "Pulse.Lib.Mutex.op_Colon_Equals" ->
    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let b = type_of g e1 in
    let is_mutex_guard =
      S.string_of_mlpath p = "Pulse.Lib.Mutex.op_Colon_Equals" in
    if is_mutex_guard || not b
    then mk_ref_assign e1 e2
    else mk_assign e1 e2
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Reference.read" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.op_Bang" ||
         S.string_of_mlpath p = "Pulse.Lib.Mutex.op_Bang" ->
    let e = extract_mlexpr g e in
    let b = type_of g e in
    let is_mutex_guard =
      S.string_of_mlpath p = "Pulse.Lib.Mutex.op_Bang" in
    if is_mutex_guard || not b
    then mk_ref_read e
    else e
  
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


  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e::i::_)
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.mask_read" ||
         S.string_of_mlpath p = "Pulse.Lib.Slice.op_Array_Access" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Access" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.read_ref" ->

    mk_expr_index (extract_mlexpr g e) (extract_mlexpr g i)

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e1::e2::e3::_)
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.mask_write" ||
         S.string_of_mlpath p = "Pulse.Lib.Slice.op_Array_Assignment" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Assignment" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.write_ref" ->

    let e1 = extract_mlexpr g e1 in
    let e2 = extract_mlexpr g e2 in
    let e3 = extract_mlexpr g e3 in
    mk_assign (mk_expr_index e1 e2) e3

  | S.MLE_App ({ expr=S.MLE_TApp ({expr=S.MLE_Name p}, [a])}, e_v::e_i::e_x::_)
    when S.string_of_mlpath p = "Pulse.Lib.Vec.replace_i" ||
         S.string_of_mlpath p = "Pulse.Lib.Vec.replace_i_ref" ->

    let e_v = extract_mlexpr g e_v in
    let e_i = extract_mlexpr g e_i in
    let e_x = extract_mlexpr g e_x in
    let is_mut = true in
    mk_mem_replace (extract_mlty g a)
                   (mk_reference_expr is_mut (mk_expr_index e_v e_i)) e_x

  | S.MLE_App ({ expr=S.MLE_TApp ({expr=S.MLE_Name p}, [a])}, e_r::e_x::_)
    when S.string_of_mlpath p = "Pulse.Lib.Reference.replace" ->

    mk_mem_replace (extract_mlty g a)
                   (extract_mlexpr g e_r)
                   (extract_mlexpr g e_x)

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Slice.from_array" ->
    extract_mlexpr g e
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, e::_::i::_)
    when S.string_of_mlpath p = "Pulse.Lib.Slice.split" ->
    mk_method_call (extract_mlexpr g e) "split_at_mut" [extract_mlexpr g i]
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, s::_::a::b::_)
    when S.string_of_mlpath p = "Pulse.Lib.Slice.subslice" ->
    let mutb = true in
    mk_reference_expr true (mk_expr_index (extract_mlexpr g s) (mk_range (Some (extract_mlexpr g a)) RangeLimitsHalfOpen (Some (extract_mlexpr g b))))
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, a::_::b::_)
    when S.string_of_mlpath p = "Pulse.Lib.Slice.copy" ->
    mk_method_call (extract_mlexpr g a) "copy_from_slice" [extract_mlexpr g b]
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [a])
    when S.string_of_mlpath p = "Pulse.Lib.Slice.len" ->
    mk_method_call (extract_mlexpr g a) "len" []

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

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [_; e1; e2; _; _])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.mask_alloc_with_vis" ->

    fail_nyi (Format.fmt1 "mlexpr %s" (S.mlexpr_to_string e))

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e; _])
    when S.string_of_mlpath p = "Pulse.Lib.Vec.free" ||
         S.string_of_mlpath p = "Pulse.Lib.Box.free" ->
    let e = extract_mlexpr g e in
    mk_call (mk_expr_path_singl "drop") [e]

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.new_mutex" ->
    let e = extract_mlexpr g e in
    mk_new_mutex e
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::_::e::_)
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.lock" ->
    let e = extract_mlexpr g e in
    mk_lock_mutex e
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::_::_::e::_)
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, _::_::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.unlock" ->
    let e = extract_mlexpr g e in
    mk_unlock_mutex e
  | S.MLE_App ({ expr=S.MLE_TApp ({expr=S.MLE_Name p}, [a])}, e_mg::e_x::_)
    when S.string_of_mlpath p = "Pulse.Lib.Mutex.replace" ->

    let is_mut = true in
    mk_mem_replace (extract_mlty g a)
                   (mk_reference_expr is_mut (extract_mlexpr g e_mg))
                   (extract_mlexpr g e_x)


  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2; _])
    when S.string_of_mlpath p = "Pulse.Lib.Array.Core.mask_free" ->

    fail_nyi (Format.fmt1 "mlexpr %s" (S.mlexpr_to_string e))

  | S.MLE_App ({expr=S.MLE_Name p}, [{expr=S.MLE_Fun (_, cond)}; {expr=S.MLE_Fun (_, body)}])
    when S.string_of_mlpath p = "Pulse.Lib.Dv.while_" ->
    let expr_while_cond = extract_mlexpr g cond in
    let expr_while_body = extract_mlexpr_to_stmts g body in
    Expr_while {expr_while_cond; expr_while_body}

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, _::_::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.GlobalVar.mk_gvar" ->
    mk_call (extract_mlexpr g e) [Expr_lit (Lit_unit)]
    
  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, _)}, _::e::_)
    when S.string_of_mlpath p = "Pulse.Lib.GlobalVar.read_gvar" ->
    mk_reference_expr false (extract_mlexpr g e)

  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
  | S.MLE_App ({expr=S.MLE_Name p}, _)
    when S.string_of_mlpath p = "failwith" ||
         S.string_of_mlpath p = "Pulse.Lib.Dv.unreachable" ->
    mk_call (mk_expr_path_singl panic_fn) []

  | S.MLE_App ({expr=S.MLE_Name p}, [e1; e2])

  | S.MLE_App ({expr=S.MLE_TApp ({expr=S.MLE_Name p}, [_])}, [e1; e2])
  | S.MLE_App ({expr=S.MLE_Name p}, [e1; e2])
    when p |> S.string_of_mlpath |> is_binop |> Some? ->
    let e1 = extract_mlexpr g e1 in
    let op = p |> S.string_of_mlpath |> is_binop |> Option.must in
    let e2 = extract_mlexpr g e2 in
    mk_binop e1 op e2

  | S.MLE_App (head, args) ->
    let head = extract_mlexpr g head in
    let args = List.map (extract_mlexpr g) args in
    mk_call head args

  | S.MLE_CTor (p, e1::e2::_)
    when snd p = "Mkdtuple2" ->
    mk_expr_tuple [extract_mlexpr g e1; extract_mlexpr g e2]

  | S.MLE_CTor (p, args) ->
    let is_native =
      S.string_of_mlpath p = "FStar.Pervasives.Native.Some" ||
      S.string_of_mlpath p = "FStar.Pervasives.Native.None" in
    let ty_name =
      match e.mlty with
      | S.MLTY_Named (_, p) -> p |> snd |> enum_or_struct_name
      | _ -> failwith "S.MLE_CTor: unexpected type" in
    let dexpr =
      if is_native then mk_expr_path_singl (snd p)
      else let path =
             if should_extract_mlpath_with_symbol g (fst p)
             then extract_path_for_symbol g (fst p)
             else [] in
           mk_expr_path (List.append path [ty_name; snd p]) in
    if List.length args = 0
    then dexpr
    else mk_call dexpr (List.map (extract_mlexpr g) args)

  | S.MLE_TApp (head, _) -> extract_mlexpr g head  // make type applications explicit in the Rust code?
  | S.MLE_If (cond, if_then, if_else_opt) ->
    let cond = extract_mlexpr g cond in
    let then_ = extract_mlexpr_to_stmts g if_then in
    let else_ = Option.map (extract_mlexpr g) if_else_opt in
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

  | S.MLE_Record (p, nm, fields) ->
    let path =
      if should_extract_mlpath_with_symbol g p
      then extract_path_for_symbol g p
      else [] in
    mk_expr_struct (List.append path [nm]) (List.map (fun (f, e) -> f, extract_mlexpr g e) fields)

  | S.MLE_Proj (e, p) -> mk_expr_field (extract_mlexpr g e) (snd p)

  | S.MLE_Tuple l -> mk_expr_tuple (List.map (extract_mlexpr g) l)

  | _ -> fail_nyi (Format.fmt1 "mlexpr %s" (S.mlexpr_to_string e))

and extract_mlexpr_to_stmts (g:env) (e:S.mlexpr) : list stmt =
  match e.expr with
  | S.MLE_Const S.MLC_Unit -> []

  | S.MLE_Let ((_, [{mllb_def = {expr = S.MLE_Const S.MLC_Unit }}]), e) ->
    extract_mlexpr_to_stmts g e

  | S.MLE_Let ((S.NonRec, [lb]), e) ->
    begin
      let is_mut, ty, init = lb_init_and_def g lb in
      let topt = None in
      let s = mk_local_stmt
        (match lb.mllb_tysc with
         | Some (_, S.MLTY_Erased) -> None
         | _ -> Some (varname lb.mllb_name))
        topt
        is_mut
        init in
      s::(extract_mlexpr_to_stmts (push_local g lb.mllb_name ty is_mut) e)
    end

  | S.MLE_Seq es ->
    let rec fixup_nonterminal_exprs = function
      | [] -> []
      | [e] -> [e]
      | Stmt_expr e :: es ->
        Stmt_local {
          local_stmt_pat = None;
          local_stmt_init = Some e;
        } :: fixup_nonterminal_exprs es
      | e::es -> e :: fixup_nonterminal_exprs es in
    let rec aux = function
      | [] -> []
      | e::es -> extract_mlexpr_to_stmts g e @ aux es in
    fixup_nonterminal_exprs (aux es)

  | S.MLE_App ({ expr=S.MLE_TApp ({ expr=S.MLE_Name p }, _) }, _)
    when S.string_of_mlpath p = "failwith" ->
    [Stmt_expr (mk_call (mk_expr_path_singl panic_fn) [])]

  | _ -> [Stmt_expr (extract_mlexpr g e)]

and extract_mlbranch_to_arm (g:env) ((pat, pat_guard, body):S.mlbranch) : arm =
  match pat_guard with
  | Some e -> fail_nyi (Format.fmt1 "mlbranch_to_arm with pat guard %s" (S.mlexpr_to_string e))
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

let extract_generic_type_param_trait_bounds (attrs:list S.mlexpr) : list (list string) =
  let open S in
  attrs
  |> List.tryFind (fun attr ->
       match attr.expr with
       | MLE_CTor (p, _)
         when string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_generics_bounds" -> true
       | _ -> false)
  |> Option.map (fun attr ->
       let MLE_CTor (p, args) = attr.expr in
       let Some l = EUtil.list_elements (List.hd args) in
       l |> List.map (fun e ->
                      match e.expr with
                      | MLE_Const (MLC_String s) -> s
                      | _ -> failwith "unexpected generic type param bounds")
         |> List.map (fun bound -> FStarC.Util.split bound "::"))
  |> Option.dflt []

let extract_generic_type_params (tyvars:list S.ty_param)
  : list generic_type_param =
  
  tyvars
  |> List.map (fun {S.ty_param_name; S.ty_param_attrs} ->
               mk_generic_type_param (tyvar_of ty_param_name)
                                     (extract_generic_type_param_trait_bounds ty_param_attrs))

let extract_top_level_lb (g:env) (lbs:S.mlletbinding) : item & env =
  let is_rec, lbs = lbs in
  // FIXME: [@@extract_as] marks all replaced lbs as recursive
  if false && is_rec = S.Rec
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
          (extract_generic_type_params tvars)
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
        fail_nyi (Format.fmt1 "top level lb def with either no tysc or generics %s" (S.mlexpr_to_string lb.mllb_def))
  end

let has_rust_derive_attr (attrs:list S.mlattribute) : option attribute =
  attrs
    |> List.tryFind (fun attr ->
       match attr.S.expr with
       | S.MLE_CTor (p, _)
         when S.string_of_mlpath p = "Pulse.Lib.Pervasives.Rust_derive" -> true
       | _ -> false)
    |> Option.map (fun attr ->
       let S.MLE_CTor (p, arg::_) = attr.S.expr in
       let S.MLE_Const (S.MLC_String s) = arg.S.expr in
       mk_derive_attr s)

let extract_struct_defn (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_Record fts) = d.tydecl_defn in
  // print1 "Adding to record field with %s\n" d.tydecl_name;
  mk_item_struct
    (attrs |> has_rust_derive_attr |> Option.map (fun a -> [a]) |> Option.dflt [])
    (d.tydecl_name |> enum_or_struct_name)
    (extract_generic_type_params d.tydecl_parameters)
    (List.map (fun (f, t) -> f, extract_mlty g t) fts),
  g

let extract_type_abbrev (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_Abbrev t) = d.tydecl_defn in
  mk_item_type
    d.tydecl_name
    (extract_generic_type_params d.tydecl_parameters)
    (extract_mlty g t),
  g

let extract_enum (g:env) (attrs:list S.mlattribute) (d:S.one_mltydecl) : item & env =
  let Some (S.MLTD_DType cts) = d.tydecl_defn in
  // print1 "enum attrs: %s\n" (String.concat ";" (List.map S.mlexpr_to_string attrs));
  mk_item_enum
    (attrs |> has_rust_derive_attr |> Option.map (fun a -> [a]) |> Option.dflt [])
    (d.tydecl_name |> enum_or_struct_name)
    (extract_generic_type_params d.tydecl_parameters)
    (List.map (fun (cname, dts) -> cname, List.map (fun (_, t) -> extract_mlty g t) dts) cts),
  g  // TODO: add it to env if needed later

let extract_mltydecl (g:env) (mlattrs:list S.mlexpr) (d:S.mltydecl) : list item & env =
  List.fold_left (fun (items, g) d ->
    let f =
      match d.S.tydecl_defn with
      | Some (S.MLTD_Abbrev _) -> extract_type_abbrev
      | Some (S.MLTD_Record _) -> extract_struct_defn
      | Some (S.MLTD_DType _) -> extract_enum
      | _ -> fail_nyi (Format.fmt1 "mltydecl %s" (S.one_mltydecl_to_string d))
    in
    let item, g = f g mlattrs d in
    items@[item], g) ([], g) d
