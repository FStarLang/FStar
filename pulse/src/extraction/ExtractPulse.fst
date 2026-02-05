module ExtractPulse
friend FStarC.Extraction.Krml

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Const
open FStarC.BaseTypes

module BU = FStarC.Util

open FStarC.Class.Show

open FStarC.Extraction.Krml

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
  
  | MLTY_Named ([arg; _], p) when Syntax.string_of_mlpath p = "Pulse.Lib.GlobalVar.gvar" ->
      translate_type_without_decay env arg

  | _ -> raise NotSupportedByKrmlExtension

let head_and_args (e : mlexpr) : mlexpr & list mlexpr =
  let rec aux acc e =
    match e.expr with
    | MLE_App (head, args) -> aux (args @ acc) head
    | _ -> (e, acc)
  in
  aux [] e

let zero_for_deref = EQualified (["C"], "_zero_for_deref")

type goto_env_elem =
  | ReturnLabel

type goto_env_t = list (mlident & goto_env_elem)

let goto_env : ref goto_env_t = mk_ref []

let with_goto_env_update #a (f: goto_env_t -> goto_env_t) (k: unit -> ML a) : ML a =
  let old = !goto_env in
  finally (fun _ -> goto_env := old) fun _ ->
    goto_env := f old;
    k ()

let with_goto_env_elem #a (id: mlident) (e: goto_env_elem) (k: unit -> ML a) : ML a =
  with_goto_env_update (Cons (id, e)) k

let lookup_goto (id: mlident) : option goto_env_elem =
  let rec go (env: goto_env_t) =
    match env with
    | [] -> None
    | (j, e) :: _ when j = id -> Some e
    | _ :: env -> go env
  in
  go !goto_env

let pulse_translate_let : translate_let_t = fun env flv lb ->
  if !dbg then Format.print1_warning "ExtractPulse.pulse_translate_let %s\n" (mlletbinding_to_string (flv, [lb]));
  match lb with
  | { mllb_def = { expr = MLE_Fun (args,
        { expr = MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ { expr = MLE_Fun ([{mlbinder_name=lbl}], body) } ]) }) } }
      when string_of_mlpath p = "Pulse.Lib.Dv.forward_jump_label" ->
    with_goto_env_elem lbl ReturnLabel fun _ ->
      translate_let env flv { lb with mllb_def = { lb.mllb_def with expr = MLE_Fun (args, body) } }
  | _ ->
    raise NotSupportedByKrmlExtension

let pulse_translate_expr : translate_expr_t = fun env e ->
  let e = flatten_app e in
  if !dbg
  then Format.print1_warning "ExtractPulse.pulse_translate_expr %s\n" (mlexpr_to_string e);
  let cb = translate_expr env in
  match e.expr with

  (* Pulse references *)
  | MLE_App ({ expr = MLE_Name p } , [ _; init ])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _; init ])
    when string_of_mlpath p = "Pulse.Lib.Reference.alloc" ->
    EBufCreate (Stack, cb init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ _; _ ])
    when string_of_mlpath p = "Pulse.Lib.Reference.alloc_uninit" ->
    EBufCreate (Stack, EAny, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x ])
    when string_of_mlpath p = "Pulse.Lib.Reference.free" ->
    EUnit // no-op to support manual stack allocation for testing

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ ty ] )}, [ _ ])
  | MLE_TApp({ expr = MLE_Name p }, [ ty ] )
    when
      string_of_mlpath p = "Pulse.Lib.ArrayPtr.null" ||
      string_of_mlpath p = "Pulse.Lib.Reference.null" ->
    EBufNull (translate_type_without_decay env ty)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ty]) } , [ r ])
    when string_of_mlpath p = "Pulse.Lib.Reference.is_null" ->
    generate_is_null (translate_type_without_decay env ty) (cb r)

  | MLE_App ({ expr = MLE_Name p } , [ init ])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when string_of_mlpath p = "Pulse.Lib.Box.alloc" ->
    EBufCreate (ManuallyManaged, cb init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ ty ] )}, [ _ ])
  | MLE_TApp({ expr = MLE_Name p }, [ ty ] )
    when string_of_mlpath p = "Pulse.Lib.Box.null" ->
    EBufNull (translate_type_without_decay env ty)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ty]) } , [ r ])
    when string_of_mlpath p = "Pulse.Lib.Box.is_null" ->
    generate_is_null (translate_type_without_decay env ty) (cb r)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, [ty]) } , [ r; _p; _v; ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.is_null" ->
    generate_is_null (translate_type_without_decay env ty) (cb r)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _w ])
    when string_of_mlpath p = "Pulse.Lib.Box.free" ->
    EBufFree (cb x)

  | MLE_App({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])}, [_v])}, [_perm])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; _v; _perm ])
    when string_of_mlpath p = "Pulse.Lib.Reference.read"
      || string_of_mlpath p = "Pulse.Lib.Box.op_Bang" ->
    EBufRead (cb e, zero_for_deref)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "Pulse.Lib.Reference.write" ->
    EBufWrite (cb e1, zero_for_deref, cb e2)

  | MLE_App ({expr=MLE_App({expr=MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1 ])}, [e2])}, [_e3])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2; _e3 ])
    when string_of_mlpath p = "Pulse.Lib.Box.op_Colon_Equals" ->
    EBufWrite (cb e1, zero_for_deref, cb e2)

  (* Pulse arrays *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [_; n; _; _])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.mask_alloc_with_vis" ->
    EBufCreate (Stack, EAny, cb n)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [_; x; n])
    when string_of_mlpath p = "Pulse.Lib.Array.PtsTo.alloc" ->
    EBufCreate (Stack, cb x, cb n)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [x; _; _])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.mask_free" ->
    EUnit // no-op to support manual stack allocation for testing

  | MLE_App ({ expr = MLE_Name p }, [ x; n])
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; n])
    when string_of_mlpath p = "Pulse.Lib.Vec.alloc" ->
    EBufCreate (ManuallyManaged, cb x, cb n)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Access" ->
    EBufRead (cb e, cb i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _w; _m ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.mask_read" ->
    EBufRead (cb e, cb i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; v; _w ])
    when string_of_mlpath p = "Pulse.Lib.Vec.op_Array_Assignment" ->
    EBufWrite (cb e, cb i, cb v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; v; _; _ ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.mask_write" ->
    EBufWrite (cb e, cb i, cb v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ a; _p; _m; i; j; _w ])
    when string_of_mlpath p = "Pulse.Lib.Array.Core.sub" ->
    EBufSub (translate_expr env a, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ r; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.Reference.to_array_mask" ->
    translate_expr env r

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ a; i; _p; _w; _m ])
    when string_of_mlpath p = "Pulse.Lib.Reference.array_at" ->
    EBufSub (translate_expr env a, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ a; i; _w; _m ])
    when string_of_mlpath p = "Pulse.Lib.Reference.array_at_uninit" ->
    EBufSub (translate_expr env a, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _w ])
    when string_of_mlpath p = "Pulse.Lib.Vec.free" ->
    EBufFree (cb x)

  (* Pulse array pointers (ArrayPtr, as an underlying C extraction for slices *)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e; i; _p; _w ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.op_Array_Access" ->
    EBufRead (translate_expr env e, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ x; _p; _w ])
    when
      string_of_mlpath p = "Pulse.Lib.ArrayPtr.as_ref" ||
      string_of_mlpath p = "Pulse.Lib.ArrayPtr.from_ref" ||
      string_of_mlpath p = "Pulse.Lib.ArrayPtr.from_array" ->
    translate_expr env x

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ a; _p; i; _w ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.split" ->
    EBufSub (translate_expr env a, translate_expr env i)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, (e :: i :: v :: _))
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.op_Array_Assignment" ->
    EBufWrite (translate_expr env e, translate_expr env i, translate_expr env v)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _; e1; e2; e3; e4; e5; _; _ ])
    when string_of_mlpath p = "Pulse.Lib.ArrayPtr.memcpy" ->
    EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ b ])
    when string_of_mlpath p = "Pulse.Lib.Vec.vec_to_array" ->
    cb b

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
  
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _post; _dup; init ])
    when string_of_mlpath p = "Pulse.Lib.GlobalVar.mk_gvar" ->
    cb { init with expr = MLE_App (init, [ml_unit]) }
  
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _post; x ])
    when string_of_mlpath p = "Pulse.Lib.GlobalVar.read_gvar" ->
    cb x

  // FIXME: What should we do with DPE.run_stt? Pulse2Rust has a similar ad-hoc rule
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _post; body ])
    when string_of_mlpath p = "DPE.run_stt" ->
    cb body

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ { expr = MLE_Var lbl }; arg ])
    when string_of_mlpath p = "Pulse.Lib.Dv.goto" ->
    (match lookup_goto lbl with
    | Some ReturnLabel -> EReturn (cb arg)
    | _ -> raise NotSupportedByKrmlExtension)

  | _ -> raise NotSupportedByKrmlExtension

let _ =
  register_pre_translate_type_without_decay pulse_translate_type_without_decay;
  register_pre_translate_let pulse_translate_let;
  register_pre_translate_expr pulse_translate_expr
