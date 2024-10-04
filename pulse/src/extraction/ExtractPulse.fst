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

open FStar.Class.Show

open FStar.Extraction.Krml

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

let dbg = Debug.get_toggle "extraction"

let pulse_translate_type_without_decay : translate_type_without_decay_t = fun env t ->
  match t with
  | MLTY_Named ([arg], p) when
    (let p = Syntax.string_of_mlpath p in
     p = "Pulse.Lib.Reference.ref" ||
     p = "Pulse.Lib.Array.Core.array" ||
     p = "Pulse.Lib.ArrayPtr.ptr" ||
     p = "Pulse.Lib.Vec.vec" ||
     p = "Pulse.Lib.Box.box")
    ->
      TBuf (translate_type_without_decay env arg)

  | _ -> raise NotSupportedByKrmlExtension

let head_and_args (e : mlexpr) : mlexpr & list mlexpr =
  let rec aux acc e =
    match e.expr with
    | MLE_App (head, args) -> aux (args @ acc) head
    | _ -> (e, acc)
  in
  aux [] e

let zero_for_deref = EQualified (["C"], "_zero_for_deref")

let pulse_translate_expr : translate_expr_t = fun env e ->
  let e = flatten_app e in
  if !dbg
  then BU.print1_warning "ExtractPulse.pulse_translate_expr %s\n" (mlexpr_to_string e);
  let cb = translate_expr env in
  match e.expr with

  (* Pulse references *)
  | MLE_App ({ expr = MLE_Name p } , [ init ])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when string_of_mlpath p = "Pulse.Lib.Reference.alloc" ->
    EBufCreate (Stack, cb init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_Name p } , [ init ])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when string_of_mlpath p = "Pulse.Lib.Box.alloc" ->
    EBufCreate (ManuallyManaged, cb init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _w ])
    when string_of_mlpath p = "Pulse.Lib.Box.free" ->
    EBufFree (cb x)

  | MLE_App({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])}, [_v])}, [_perm])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; _v; _perm ])
    when string_of_mlpath p = "Pulse.Lib.Reference.op_Bang"
      || string_of_mlpath p = "Pulse.Lib.Box.op_Bang" ->
    EBufRead (cb e, zero_for_deref)

  | MLE_App ({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1 ])}, [e2])}, [_e3])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ])
    when string_of_mlpath p = "Pulse.Lib.Reference.op_Colon_Equals"
      || string_of_mlpath p = "Pulse.Lib.Box.op_Colon_Equals" ->
    EBufWrite (cb e1, zero_for_deref, cb e2)

  (* Pulse arrays *)
  | MLE_App ({ expr = MLE_Name p }, [ x; n])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; n])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.alloc" ->
    EBufCreate (ManuallyManaged, cb x, cb n)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Access" ->
    EBufRead (cb e, cb i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; v; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.op_Array_Assignment" ->
    EBufWrite (cb e, cb i, cb v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: _))
    when string_of_mlpath p = "Pulse.Lib.Array.Core.pts_to_range_index" ->
    EBufRead (cb e, cb i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: v :: _))
    when string_of_mlpath p = "Pulse.Lib.Array.Core.pts_to_range_upd" ->
    EBufWrite (cb e, cb i, cb v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.free" ->
    EBufFree (cb x)

  (* Pulse array pointers (ArrayPtr, as an underlying C extraction for slices *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _fp; _w ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.op_Array_Access" ->
    EBufRead (translate_expr env e, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.from_array" ->
    translate_expr env x

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ a; _p; _fp; _w; i ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.split" ->
    EBufSub (translate_expr env a, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: v :: _))
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.op_Array_Assignment" ->
    EBufWrite (translate_expr env e, translate_expr env i, translate_expr env v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _; _; _; _; _; e1; e2; e3; e4; e5 ]) when (
      string_of_mlpath p = "Pulse.Lib.ArrayPtr.blit"
    ) ->
      EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)


  (* Pulse control, while etc *)
  | MLE_App ({expr=MLE_Name p}, [{expr=MLE_Fun (_, test)}; {expr=MLE_Fun(_, body)}])
    when (string_of_mlpath p = "Pulse.Lib.Dv.while_") ->
    EWhile(cb test, cb body)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ ])
    when (string_of_mlpath p = "Pulse.Lib.Dv.unreachable") ->
    EAbortS (string_of_mlpath p)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ b ])
    when string_of_mlpath p = "Pulse.Lib.Box.box_to_ref" ->
    cb b

  // FIXME: What should we do with DPE.run_stt? Pulse2Rust has a similar ad-hoc rule
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _post; body ])
    when string_of_mlpath p = "DPE.run_stt" ->
    cb body

  | _ -> raise NotSupportedByKrmlExtension

let _ =
  register_pre_translate_type_without_decay pulse_translate_type_without_decay;
  register_pre_translate_expr pulse_translate_expr
