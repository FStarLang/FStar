module ExtractPulse
friend FStar.Extraction.Krml

(* IMPORTANT: these `open` directives come from FStar.Extraction.Krml.
   Without them, spurious dependencies on F* ulib will be introduced *)
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Const
open FStar.BaseTypes

module BU = FStar.Compiler.Util
module FC = FStar.Const

open FStar.Extraction.Krml

let pulse_translate_type_without_decay : translate_type_without_decay_t = fun env t ->
  match t with
  | MLTY_Named ([arg], p) when
    (let p = Syntax.string_of_mlpath p in
     p = "Pulse.Lib.Reference.ref" ||
     p = "Pulse.Lib.Array.Core.array")
    ->
      TBuf (translate_type_without_decay env arg)

  | _ -> raise NotSupportedByKrmlExtension

let flatten_app e =
  let rec aux args e = 
    match e.expr with 
    | MLE_App (head, args0) -> aux (args0@args) head
    | _ -> (
      match args with
      | [] -> e
      | _ -> {e with expr=MLE_App (e, args)}
    )
  in
  aux [] e

let pulse_translate_expr : translate_expr_t = fun env e ->
  let e = flatten_app e in
  match e.expr with

  (* Pulse references *)
  | MLE_App ({ expr = MLE_Name p } , [ init ])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when string_of_mlpath p = "Pulse.Lib.Reference.alloc" ->
    EBufCreate (Stack, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])}, [_v])}, [_perm])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; _v; _perm ])
    when string_of_mlpath p = "Pulse.Lib.Reference.op_Bang" ->
    EBufRead (translate_expr env e, EQualified (["C"], "_zero_for_deref"))

  | MLE_App ({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1 ])}, [e2])}, [_e3])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ])
    when string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals" ->
    EBufWrite (translate_expr env e1, EQualified (["C"], "_zero_for_deref"), translate_expr env e2)

  (* Pulse arrays *)
  | MLE_App ({ expr = MLE_Name p }, [ x; n])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; n])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.alloc" ->
    EBufCreate (ManuallyManaged, translate_expr env x, translate_expr env n)
    
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Access" ->
    EBufRead (translate_expr env e, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; v; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Assignment" ->
    EBufWrite (translate_expr env e, translate_expr env i, translate_expr env v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: _))
    when string_of_mlpath p = "Pulse.Lib.Array.Core.pts_to_range_index" ->
    EBufRead (translate_expr env e, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: v :: _))
    when string_of_mlpath p = "Pulse.Lib.Array.Core.pts_to_range_upd" ->
    EBufWrite (translate_expr env e, translate_expr env i, translate_expr env v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.free" ->
    EBufFree (translate_expr env x)

  (* Pulse control, while etc *)
  | MLE_App ({expr=MLE_Name p}, [{expr=MLE_Fun (_, test)}; {expr=MLE_Fun(_, body)}])
    when (string_of_mlpath p = "Pulse.Lib.Core.while_") ->
    EWhile(translate_expr env test, translate_expr env body)

  // FIXME: What should we do with DPE.run_stt? Pulse2Rust has a similar ad-hoc rule
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _post; body ])
    when string_of_mlpath p = "DPE.run_stt" ->
    translate_expr env body

  | _ -> raise NotSupportedByKrmlExtension

let _ =
  register_pre_translate_type_without_decay pulse_translate_type_without_decay;
  register_pre_translate_expr pulse_translate_expr
