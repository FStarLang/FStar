module ExtractSteelC

friend FStar.Extraction.Krml
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
open FStar.Extraction.Krml
module K = FStar.Extraction.Krml
module BU = FStar.Compiler.Util

(* JL: TODO: in stdlib somewhere? *)
let opt_bind (m: option 'a) (k: 'a -> option 'b): option 'b =
  match m with Some x -> k x | None -> None

let char_of_typechar (t: mlty): option char =
  match t with
  | MLTY_Named ([], p) ->
    let p = Syntax.string_of_mlpath p in
    if p = "Steel.C.Typestring.cdot" then
      Some '.'
    else if BU.starts_with p "Steel.C.Typestring.c" then
      Some (FStar.String.get p (FStar.String.strlen "Steel.C.Typestring.c"))
    else
      None

  | _ -> None

let string_of_typestring (t: mlty): option string =
  let rec go t: option (list string) =
    match t with
    | MLTY_Named ([], p)
      when Syntax.string_of_mlpath p = "Steel.C.Typestring.string_nil"
      ->
      Some []

    | MLTY_Named ([c; t], p)
      when Syntax.string_of_mlpath p = "Steel.C.Typestring.string_cons"
      ->
      opt_bind (char_of_typechar c) (fun c' ->
      opt_bind (go t) (fun s' ->
      Some (String.make 1 c' :: s')))
      
    | _ -> None
  in
  opt_bind (go t) (fun ss -> Some (FStar.String.concat "" ss))

let lident_of_string (s: string): option lident =
  let path = FStar.String.split ['.'] s in
  let rec go p =
    match p with
    | [] -> None
    | [s] -> Some ([], s)
    | s :: p ->
      opt_bind (go p) (fun (names, name) ->
      Some (s :: names, name))
  in go path

let lident_of_typestring (t: mlty): option lident =
  opt_bind (string_of_typestring t) lident_of_string

let int_of_typenat (t: mlty): option int =
  let rec go t =
    match t with
    | MLTY_Named ([], p)
      when Syntax.string_of_mlpath p = "Steel.C.Typenat.z"
      ->
      Some 0

    | MLTY_Named ([t], p)
      when Syntax.string_of_mlpath p = "Steel.C.Typenat.s"
      ->
      opt_bind (go t) (fun n -> Some (n + 1))

    | _ ->
      None
  in
  go t

let my_types_without_decay () = 
  register_pre_translate_type_without_decay begin fun env t ->
  match t with
  
  | MLTY_Named ([tag; _; _; _], p) when
    BU.starts_with (Syntax.string_of_mlpath p) "Steel.ST.C.Types.Struct.struct_t0"
    || BU.starts_with (Syntax.string_of_mlpath p) "Steel.ST.C.Types.Union.union_t0"
    ->
      TQualified (must (lident_of_typestring tag))

  | MLTY_Named ([arg], p) when
      Syntax.string_of_mlpath p = "Steel.ST.C.Types.Array.array_ptr_gen"
    ->
      TBuf (translate_type_without_decay env arg)

  | MLTY_Named ([arg], p) when
      Syntax.string_of_mlpath p = "Steel.ST.C.Types.Base.ptr_gen"
    ->
      TBuf (translate_type_without_decay env arg)

  | MLTY_Named ([arg], p) when
    Syntax.string_of_mlpath p = "Steel.ST.C.Types.Scalar.scalar_t"
    ->
      translate_type_without_decay env arg

  | MLTY_Named ([t; n; s], p)
    when false
     || Syntax.string_of_mlpath p = "Steel.ST.C.Types.Array.base_array_t"
    ->
      TArray (
        translate_type_without_decay env t,
        (UInt32, string_of_int (must (int_of_typenat n))))
  
  | _ -> raise NotSupportedByKrmlExtension
end

let my_types () = register_pre_translate_type begin fun env t ->
  match t with
  | MLTY_Named ([t; _; _], p)
    when false
     || Syntax.string_of_mlpath p = "Steel.ST.C.Types.Array.base_array_t"
    ->
      TBuf (translate_type_without_decay env t)
      
  | _ -> raise NotSupportedByKrmlExtension
end

let my_exprs () = register_pre_translate_expr begin fun env e ->
  match e.expr with
  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ (* typedef *) ])
    when (
          string_of_mlpath p = "Steel.ST.C.Types.Base.alloc" ||
          false) ->
      EBufCreateNoInit (ManuallyManaged, EConstant (UInt32, "1"))

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ (* td *); sz ])
    when (
          string_of_mlpath p = "Steel.ST.C.Types.Array.array_ptr_alloc" ||
          false) ->
      EBufCreateNoInit (ManuallyManaged, translate_expr env sz)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _(* td *); _ (* s *); e2; _ (* len *) ])
    when (
          string_of_mlpath p = "Steel.ST.C.Types.Array.array_ref_free" ||
          false) ->
      EBufFree (translate_expr env e2)

  | MLE_App ({ expr = MLE_TApp({ expr = MLE_Name p }, _) }, [ _ (* typedef *); _ (* v *); e ]) when
       string_of_mlpath p = "Steel.ST.C.Types.Base.free" ->
      EBufFree (translate_expr env e)

(* BEGIN support for the Steel null pointer. *)

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, [t])}, [_ (* opened *); _ (* td *); _ (* v *); e; _ (* len *) ])
    when string_of_mlpath p = "Steel.ST.C.Types.Array.array_ptr_is_null"
    -> generate_is_null (translate_type env t) (translate_expr env e)

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, [t])}, [_ (* opened *); _ (* td *); _ (* v *); e])
    when string_of_mlpath p = "Steel.ST.C.Types.Base.is_null"
    -> generate_is_null (translate_type env t) (translate_expr env e)
  
  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, [t])}, _)
    when false
    || Syntax.string_of_mlpath p = "Steel.ST.C.Types.Array.null_array_ptr"
    -> EBufNull (translate_type env t)

  | MLE_TApp ({expr=MLE_Name p}, [t]) when
      string_of_mlpath p = "Steel.ST.C.Types.Base.null_gen"
    -> EBufNull (translate_type env t)

(* END support for the Steel null pointer *)


  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)},
             [
               ({expr=MLE_Const (MLC_String struct_name)})
               ; _ (* fields *)
               ; _ (* v *)
               ; r
               ; ({expr=MLE_Const (MLC_String field_name)})
               ; _ (* td' *)
             ])
    when string_of_mlpath p = "Steel.ST.C.Types.Struct.struct_field0"
    || string_of_mlpath p = "Steel.ST.C.Types.Union.union_field0"
    || string_of_mlpath p = "Steel.ST.C.Types.Union.union_switch_field0"
    ->
      EAddrOf (EField (
        TQualified (must (lident_of_string struct_name)),
        EBufRead (translate_expr env r, EQualified (["C"], "_zero_for_deref")),
        field_name))

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)},
             [
               _ (* struct_def *)
               ; _ (* v *)
               ; r
               ; ({expr=MLE_Const (MLC_String field_name)})
               ; _ (* td' *)
             ])
    when string_of_mlpath p = "Steel.ST.C.Types.UserStruct.struct_field0"
    ->
      EAddrOf (EField (
        assert_lid env r.mlty,
        EBufRead (translate_expr env r, EQualified (["C"], "_zero_for_deref")),
        field_name))

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_ (* value *) ; _ (* perm *) ; r])
    when string_of_mlpath p = "Steel.ST.C.Types.Scalar.read0" ->
      EBufRead (translate_expr env r, EQualified (["C"], "_zero_for_deref"))

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [_ (* value *); r; x])
    when string_of_mlpath p = "Steel.ST.C.Types.Scalar.write" ->
      EAssign (
        EBufRead (translate_expr env r, EQualified (["C"], "_zero_for_deref")),
        translate_expr env x)

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [
      _ (* typedef *);
      _ (* source value *);
      _ (* source perm *);
      _ (* dest perm *);
      src;
      dst
    ])
    when string_of_mlpath p = "Steel.ST.C.Types.Base.copy" ->
      EAssign (
        EBufRead (translate_expr env dst, EQualified (["C"], "_zero_for_deref")),
        EBufRead (translate_expr env src, EQualified (["C"], "_zero_for_deref")))

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [
      _ (* opened *);
      _ (* n *);
      _ (* typedef *);
      _ (* v *);
      r
    ])
    when string_of_mlpath p = "Steel.ST.C.Types.Array.array_ref_of_base" ->
      // this is not a true read, this is how Karamel models arrays decaying into pointers
      EBufRead (translate_expr env r, EQualified (["C"], "_zero_for_deref"))

  | MLE_App ({expr=MLE_TApp ({expr=MLE_Name p}, _)}, [
      _ (* typedef *);
      _ (* s *);
      a;
      _ (* len *);
      i
    ])
    when string_of_mlpath p = "Steel.ST.C.Types.Array.array_ref_cell"
    || string_of_mlpath p = "Steel.ST.C.Types.Array.array_ref_split"
    ->
      EBufSub (translate_expr env a, translate_expr env i)

  | _ -> raise NotSupportedByKrmlExtension
end

let parse_steel_c_fields env (fields: mlty): option (list _) =
      let rec go fields =
        match fields with
        | MLTY_Named ([], p)
          when false
          || Syntax.string_of_mlpath p = "Steel.ST.C.Types.Fields.field_t_nil"
          -> Some []
          
        | MLTY_Named ([field; t; fields], p)
          when false
          || Syntax.string_of_mlpath p = "Steel.ST.C.Types.Fields.field_t_cons"
          ->
          opt_bind (string_of_typestring field) (fun field ->
          if field = "" then go fields else
          opt_bind (go fields) (fun fields ->
          Some ((field, t) :: fields)))

        | _ ->
          None
      in
      match go fields with
      | None ->
        BU.print1 "Failed to parse fields from %s.\n"
          (FStar.Extraction.ML.Code.string_of_mlty ([], "") fields);
        None

      | Some fields ->
          print_endline "Got fields:";
          List.fold_left
            (fun () (field, ty) ->
               BU.print2 "  %s : %s\n"
                 field
                 (FStar.Extraction.ML.Code.string_of_mlty ([], "") ty))
            ()
            fields;
          Some (
            List.map
              (fun (field, ty) ->
                 BU.print1 "Translating %s.\n"
                   (FStar.Extraction.ML.Code.string_of_mlty ([], "") ty);
                 (field, translate_type_without_decay env ty))
              fields)

let define_struct_gen
  env p args fields
=
    let env = List.fold_left (fun env name -> extend_t env name) env args in
    let fields = must (parse_steel_c_fields env fields) in
    Some (DTypeFlat (p, [], List.length args,
      List.map (fun (field, ty) -> (field, (ty, true))) fields))

let define_struct
  env tag fields
=
  (* JL: TODO remove/improve these print commands *)
  print_endline "Parsing struct definition.";
  match lident_of_typestring tag with
  | None ->
    BU.print1 "Failed to parse struct tag from %s.\n"
      (FStar.Extraction.ML.Code.string_of_mlty ([], "") tag);
    None
  | Some p ->
    define_struct_gen env p [] fields

let define_union_gen
  env p args fields
=
    let env = List.fold_left (fun env name -> extend_t env name) env args in
    let fields = must (parse_steel_c_fields env fields) in
    Some (DUntaggedUnion (p, [], List.length args, fields))

let define_union
  env tag fields
=
  (* JL: TODO remove/improve these print commands *)
  print_endline "Parsing union definition.";
  match lident_of_typestring tag with
  | None ->
    BU.print1 "Failed to parse union tag from %s.\n"
      (FStar.Extraction.ML.Code.string_of_mlty ([], "") tag);
    None
  | Some p ->
    define_union_gen env p [] fields

let my_type_decls () = register_pre_translate_type_decl begin fun env ty ->
    match ty with
    | {tydecl_defn=Some (MLTD_Abbrev (MLTY_Named ([tag; fields; _; _], p)))}
      when Syntax.string_of_mlpath p = "Steel.ST.C.Types.Struct.define_struct0"
      ->
      define_struct env tag fields

    | {tydecl_defn=Some (MLTD_Abbrev (MLTY_Named ([tag; fields; _; _], p)))}
      when Syntax.string_of_mlpath p = "Steel.ST.C.Types.Union.define_union0"
      ->
      define_union env tag fields

    | {tydecl_name=name;
       tydecl_parameters=args;
       tydecl_defn=Some (MLTD_Abbrev (MLTY_Named ([_; fields; _; _], p)))}
      when Syntax.string_of_mlpath p = "Steel.ST.C.Types.Struct.struct_t0"
      ->
      let name = env.module_name, name in
      define_struct_gen env name args fields

    | {tydecl_name=name;
       tydecl_parameters=args;
       tydecl_defn=Some (MLTD_Abbrev (MLTY_Named ([_; fields; _; _], p)))}
      when Syntax.string_of_mlpath p = "Steel.ST.C.Types.Union.union_t0"
      ->
      let name = env.module_name, name in
      define_union_gen env name args fields

    | _ -> raise NotSupportedByKrmlExtension
end

let _ =
  my_types_without_decay ();
  my_types ();
  my_exprs ();
  my_type_decls ()
