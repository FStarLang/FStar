module ExtractSteel
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

let steel_translate_type_without_decay : translate_type_without_decay_t = fun env t ->
  match t with
  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "Steel.TLArray.t" ->
      TConstBuf (translate_type_without_decay env arg)

  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "Steel.Reference.ref" ||
    Syntax.string_of_mlpath p = "Steel.ST.Reference.ref" ||
    Syntax.string_of_mlpath p = "Steel.ST.HigherArray.ptr"
    ->
      TBuf (translate_type_without_decay env arg)

  | _ -> raise NotSupportedByKrmlExtension

let steel_translate_expr : translate_expr_t = fun env e ->
  match e.expr with
  | MLE_App ({expr = MLE_TApp ({expr = MLE_Name p}, [t]) }, _)
    when string_of_mlpath p = "Steel.ST.HigherArray.null_ptr"
    ->
    EBufNull (translate_type env t)
  | MLE_App ({expr = MLE_TApp ({expr = MLE_Name p }, [t])}, [arg])
    when string_of_mlpath p = "Steel.ST.HigherArray.is_null_ptr"
    ->
    generate_is_null (translate_type env t) (translate_expr env arg)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p}, _) }, [ _perm0; _perm1; _seq0; _seq1; e0; _len0; e1; _len1])
    when string_of_mlpath p = "Steel.ST.HigherArray.ptrdiff_ptr" ->
    EBufDiff (translate_expr env e0, translate_expr env e1)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "Steel.TLArray.get" ->
    EBufRead (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _perm; e1; _len; _seq; e2 ])
    when string_of_mlpath p = "Steel.ST.HigherArray.index_ptr" ->
      EBufRead (translate_expr env e1, translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e ])
    when string_of_mlpath p = "Steel.Reference.read" ->
      EBufRead (translate_expr env e, EQualified (["C"], "_zero_for_deref"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _perm; _v; e ])
    when string_of_mlpath p = "Steel.ST.Reference.read" ->
      EBufRead (translate_expr env e, EQualified (["C"], "_zero_for_deref"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when (
      string_of_mlpath p = "Steel.ST.Reference._alloca"
    ) ->
    EBufCreate (Stack, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) } , [ init ])
    when (string_of_mlpath p = "Steel.Reference.malloc" ||
          string_of_mlpath p = "Steel.ST.Reference.alloc") ->
      EBufCreate (ManuallyManaged, translate_expr env init, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e0; e1 ])
    when string_of_mlpath p = "Steel.ST.HigherArray.malloc_ptr" ->
      EBufCreate (ManuallyManaged, translate_expr env e0, translate_expr env e1)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e2 ]) when
      string_of_mlpath p = "Steel.Reference.free" ->
      EBufFree (translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _v; e2 ]) when
       string_of_mlpath p = "Steel.ST.HigherArray.free_ptr" ||
       string_of_mlpath p = "Steel.ST.Reference.free" ->
      EBufFree (translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "Steel.ST.HigherArray.ptr_shift" ->
      EBufSub (translate_expr env e1, translate_expr env e2)
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; _len; _s; e2; e3 ])
    when string_of_mlpath p = "Steel.ST.HigherArray.upd_ptr" ->
      EBufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; _len; _s; e2; e3 ])
    when string_of_mlpath p = "Steel.ST.HigherArray.upd_ptr" ->
      EBufWrite (translate_expr env e1, translate_expr env e2, translate_expr env e3)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ e1; e2 ])
    when string_of_mlpath p = "Steel.Reference.write" ->
      EBufWrite (translate_expr env e1, EQualified (["C"], "_zero_for_deref"), translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _v; e1; e2 ])
    when string_of_mlpath p = "Steel.ST.Reference.write" ->
      EBufWrite (translate_expr env e1, EQualified (["C"], "_zero_for_deref"), translate_expr env e2)

  | MLE_App ({ expr = MLE_Name p }, [ _ ]) when (
        string_of_mlpath p = "Steel.ST.Reference._push_frame"
      ) ->
      EPushFrame

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _; _ ]) when (string_of_mlpath p = "Steel.ST.Reference._free_and_pop_frame") ->
      EPopFrame

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _; _; _; e1; _; e2; e3; _; e4; e5 ]) when (
      string_of_mlpath p = "Steel.ST.HigherArray.blit_ptr"
    ) ->
      EBufBlit (translate_expr env e1, translate_expr env e2, translate_expr env e3, translate_expr env e4, translate_expr env e5)

  (* Misc. Steel operations *)
  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_; _; e])
    when string_of_mlpath p = "Steel.Effect.Atomic.return" ->
    translate_expr env e

  | MLE_App ({expr=MLE_Name p}, [ _inv; test; body ])
    when (string_of_mlpath p = "Steel.ST.Loops.while_loop") ->
    EApp (EQualified (["Steel"; "Loops"], "while_loop"), [ EUnit; translate_expr env test; translate_expr env body ])

  (* Piggyback Steel.ST.Printf primitives to LowStar.Printf *)
  | MLE_App ({ expr = MLE_Name (["Steel"; "ST"; "Printf"], fn) }, args) ->
        EApp (EQualified ([ "LowStar"; "Printf" ], fn), List.map (translate_expr env) args)

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_; _; e])
    when string_of_mlpath p = "Steel.Effect.Atomic.return" ||
         string_of_mlpath p = "Steel.ST.Util.return" ->
    translate_expr env e

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_fp; _fp'; _opened; _p; _i; {expr=MLE_Fun (_, body)}])
    when string_of_mlpath p = "Steel.ST.Util.with_invariant" ||
         string_of_mlpath p = "Steel.Effect.Atomic.with_invariant" ->
    translate_expr env body

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_fp; _fp'; _opened; _p; _i; e])
    when string_of_mlpath p = "Steel.ST.Util.with_invariant" ||
         string_of_mlpath p = "Steel.Effect.Atomic.with_invariant" ->
    Errors.raise_error
      (Errors.Fatal_ExtractionUnsupported,
       BU.format2
         "Extraction of with_invariant requires its argument to be a function literal \
         at extraction time, try marking its argument inline_for_extraction (%s, %s)"
         (string_of_int (fst e.loc))
         (snd e.loc))
      Range.dummyRange

  | _ -> raise NotSupportedByKrmlExtension

let steel_translate_let : translate_let_t = fun env flavor lb ->
  match lb with
    | {
      mllb_name = name;
      mllb_tysc = Some (tvars, t);
      mllb_def = { expr = MLE_App ({
        expr = MLE_TApp ({expr = MLE_Name p}, _)}, [ l ] ) };
      mllb_meta = meta
    }
    when string_of_mlpath p = "Steel.TLArray.create" ->
    if List.mem Syntax.NoExtract meta then
      None
    else
      // This is a global const array, defined using Steel.TLArray
      let meta = translate_flags meta in
      let env = List.fold_left (fun env name -> extend_t env name) env tvars in
      let t = translate_type env t in
      let name = env.module_name, name in
      begin try
        let expr = List.map (translate_expr env) (list_elements l) in
        Some (DGlobal (meta, name, List.length tvars, t, EBufCreateL (Eternal, expr)))
      with e ->
          Errors. log_issue Range.dummyRange (Errors.Warning_DefinitionNotTranslated, (BU.format2 "Error extracting %s to KaRaMeL (%s)\n" (Syntax.string_of_mlpath name) (BU.print_exn e)));
          Some (DGlobal (meta, name, List.length tvars, t, EAny))
        end
    | _ -> raise NotSupportedByKrmlExtension

let _ =
  register_pre_translate_type_without_decay steel_translate_type_without_decay;
  register_pre_translate_expr steel_translate_expr;
  register_pre_translate_let steel_translate_let
