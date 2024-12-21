open Prims
let (info_at_pos :
  FStarC_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string, FStarC_Ident.lident) FStar_Pervasives.either *
            FStarC_Syntax_Syntax.typ * FStarC_Compiler_Range_Type.range)
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun file ->
      fun row ->
        fun col ->
          let uu___ =
            let uu___1 =
              FStarC_Compiler_Effect.op_Bang
                env.FStarC_TypeChecker_Env.identifier_info in
            FStarC_TypeChecker_Common.id_info_at_pos uu___1 file row col in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStarC_TypeChecker_Common.identifier with
               | FStar_Pervasives.Inl bv ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         FStarC_Class_Show.show FStarC_Ident.showable_ident
                           bv.FStarC_Syntax_Syntax.ppname in
                       FStar_Pervasives.Inl uu___3 in
                     let uu___3 = FStarC_Syntax_Syntax.range_of_bv bv in
                     (uu___2, (info.FStarC_TypeChecker_Common.identifier_ty),
                       uu___3) in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives.Inr fv ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = FStarC_Syntax_Syntax.lid_of_fv fv in
                       FStar_Pervasives.Inr uu___3 in
                     let uu___3 = FStarC_Syntax_Syntax.range_of_fv fv in
                     (uu___2, (info.FStarC_TypeChecker_Common.identifier_ty),
                       uu___3) in
                   FStar_Pervasives_Native.Some uu___1)
let print_discrepancy : 'a 'b . ('a -> 'b) -> 'a -> 'a -> ('b * 'b) =
  fun f ->
    fun x ->
      fun y ->
        let print uu___ =
          let xs = f x in let ys = f y in (xs, ys, (xs <> ys)) in
        let rec blist_leq l1 l2 =
          match (l1, l2) with
          | (h1::t1, h2::t2) ->
              ((Prims.op_Negation h1) || h2) && (blist_leq t1 t2)
          | ([], []) -> true
          | uu___ -> failwith "print_discrepancy: bad lists" in
        let rec succ l =
          match l with
          | (false)::t -> true :: t
          | (true)::t -> let uu___ = succ t in false :: uu___
          | [] -> failwith "" in
        let full l = FStarC_Compiler_List.for_all (fun b1 -> b1) l in
        let get_bool_option s =
          let uu___ = FStarC_Options.get_option s in
          match uu___ with
          | FStarC_Options.Bool b1 -> b1
          | uu___1 -> failwith "print_discrepancy: impossible" in
        let set_bool_option s b1 =
          FStarC_Options.set_option s (FStarC_Options.Bool b1) in
        let get uu___ =
          let pi = get_bool_option "print_implicits" in
          let pu = get_bool_option "print_universes" in
          let pea = get_bool_option "print_effect_args" in
          let pf = get_bool_option "print_full_names" in [pi; pu; pea; pf] in
        let set l =
          match l with
          | pi::pu::pea::pf::[] ->
              (set_bool_option "print_implicits" pi;
               set_bool_option "print_universes" pu;
               set_bool_option "print_effect_args" pea;
               set_bool_option "print_full_names " pf)
          | uu___ -> failwith "impossible: print_discrepancy" in
        let bas = get () in
        let rec go cur =
          if full cur
          then
            let uu___ = print () in
            match uu___ with | (xs, ys, uu___1) -> (xs, ys)
          else
            if (let uu___ = blist_leq bas cur in Prims.op_Negation uu___)
            then (let uu___ = succ cur in go uu___)
            else
              (set cur;
               (let uu___1 = print () in
                match uu___1 with
                | (xs, ys, true) -> (xs, ys)
                | uu___2 -> let uu___3 = succ cur in go uu___3)) in
        FStarC_Options.with_saved_options (fun uu___ -> go bas)
let (errors_smt_detail :
  FStarC_TypeChecker_Env.env ->
    FStarC_Errors.error Prims.list ->
      FStarC_Errors_Msg.error_message -> FStarC_Errors.error Prims.list)
  =
  fun env ->
    fun errs ->
      fun smt_detail ->
        let errs1 =
          FStarC_Compiler_List.map
            (fun uu___ ->
               match uu___ with
               | (e, msg, r, ctx) ->
                   let uu___1 =
                     let msg1 = FStarC_Compiler_List.op_At msg smt_detail in
                     if r = FStarC_Compiler_Range_Type.dummyRange
                     then
                       let uu___2 = FStarC_TypeChecker_Env.get_range env in
                       (e, msg1, uu___2, ctx)
                     else
                       (let r' =
                          let uu___3 = FStarC_Compiler_Range_Type.use_range r in
                          FStarC_Compiler_Range_Type.set_def_range r uu___3 in
                        let uu___3 =
                          let uu___4 =
                            FStarC_Compiler_Range_Ops.file_of_range r' in
                          let uu___5 =
                            let uu___6 = FStarC_TypeChecker_Env.get_range env in
                            FStarC_Compiler_Range_Ops.file_of_range uu___6 in
                          uu___4 <> uu___5 in
                        if uu___3
                        then
                          let msg2 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    FStarC_Compiler_Range_Ops.string_of_use_range
                                      r in
                                  Prims.strcat "Also see: " uu___7 in
                                FStarC_Pprint.doc_of_string uu___6 in
                              let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStarC_Compiler_Range_Type.use_range r in
                                    let uu___10 =
                                      FStarC_Compiler_Range_Type.def_range r in
                                    uu___9 <> uu___10 in
                                  if uu___8
                                  then
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Compiler_Range_Ops.string_of_def_range
                                          r in
                                      Prims.strcat
                                        "Other related locations: " uu___10 in
                                    FStarC_Pprint.doc_of_string uu___9
                                  else FStarC_Pprint.empty in
                                [uu___7] in
                              uu___5 :: uu___6 in
                            FStarC_Compiler_List.op_At msg1 uu___4 in
                          let uu___4 = FStarC_TypeChecker_Env.get_range env in
                          (e, msg2, uu___4, ctx)
                        else (e, msg1, r, ctx)) in
                   (match uu___1 with
                    | (e1, msg1, r1, ctx1) -> (e1, msg1, r1, ctx1))) errs in
        errs1
let (add_errors :
  FStarC_TypeChecker_Env.env -> FStarC_Errors.error Prims.list -> unit) =
  fun env ->
    fun errs ->
      let uu___ = errors_smt_detail env errs [] in
      FStarC_Errors.add_errors uu___
let (log_issue :
  FStarC_TypeChecker_Env.env ->
    FStarC_Compiler_Range_Type.range ->
      (FStarC_Errors_Codes.error_code * FStarC_Errors_Msg.error_message) ->
        unit)
  =
  fun env ->
    fun r ->
      fun uu___ ->
        match uu___ with
        | (e, m) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Errors.get_ctx () in (e, m, r, uu___3) in
              [uu___2] in
            add_errors env uu___1
let (log_issue_text :
  FStarC_TypeChecker_Env.env ->
    FStarC_Compiler_Range_Type.range ->
      (FStarC_Errors_Codes.error_code * Prims.string) -> unit)
  =
  fun env ->
    fun r ->
      fun uu___ ->
        match uu___ with
        | (e, m) ->
            let uu___1 =
              let uu___2 = let uu___3 = FStarC_Errors_Msg.text m in [uu___3] in
              (e, uu___2) in
            log_issue env r uu___1
let (err_msg_type_strings :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        print_discrepancy (FStarC_TypeChecker_Normalize.term_to_string env)
          t1 t2
let (err_msg_comp_strings :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp ->
      FStarC_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        print_discrepancy (FStarC_TypeChecker_Normalize.comp_to_string env)
          c1 c2
let (exhaustiveness_check : FStarC_Pprint.document Prims.list) =
  let uu___ = FStarC_Errors_Msg.text "Patterns are incomplete" in [uu___]
let (subtyping_failed :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ -> unit -> FStarC_Errors_Msg.error_message)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun uu___ ->
          let ppt = FStarC_TypeChecker_Normalize.term_to_doc env in
          let uu___1 = FStarC_Errors_Msg.text "Subtyping check failed" in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Errors_Msg.text "Expected type" in
                let uu___6 = ppt t2 in
                FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___5
                  uu___6 in
              let uu___5 =
                let uu___6 = FStarC_Errors_Msg.text "got type" in
                let uu___7 = ppt t1 in
                FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___6
                  uu___7 in
              FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
            [uu___3] in
          uu___1 :: uu___2
let (ill_kinded_type : FStarC_Errors_Msg.error_message) =
  FStarC_Errors_Msg.mkmsg "Ill-kinded type"
let unexpected_signature_for_monad :
  'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        FStarC_Ident.lident -> FStarC_Syntax_Syntax.term -> 'a
  =
  fun env ->
    fun rng ->
      fun m ->
        fun k ->
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Ident.showable_lident m in
            let uu___2 = FStarC_TypeChecker_Normalize.term_to_string env k in
            FStarC_Compiler_Util.format2
              "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type -> WP a -> Effect); got %s"
              uu___1 uu___2 in
          FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
            FStarC_Errors_Codes.Fatal_UnexpectedSignatureForMonad ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___)
let expected_a_term_of_type_t_got_a_function :
  'uuuuu .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        Prims.string ->
          FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.term -> 'uuuuu
  =
  fun env ->
    fun rng ->
      fun msg ->
        fun t ->
          fun e ->
            let uu___ =
              let uu___1 = FStarC_TypeChecker_Normalize.term_to_string env t in
              let uu___2 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              FStarC_Compiler_Util.format3
                "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
                uu___1 uu___2 msg in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              rng FStarC_Errors_Codes.Fatal_ExpectTermGotFunction ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___)
let (unexpected_implicit_argument :
  (FStarC_Errors_Codes.error_code * Prims.string)) =
  (FStarC_Errors_Codes.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
let expected_expression_of_type :
  'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> 'a
  =
  fun env ->
    fun rng ->
      fun t1 ->
        fun e ->
          fun t2 ->
            let d1 = FStarC_TypeChecker_Normalize.term_to_doc env t1 in
            let d2 = FStarC_TypeChecker_Normalize.term_to_doc env t2 in
            let ed = FStarC_TypeChecker_Normalize.term_to_doc env e in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_Errors_Msg.text "Expected expression of type" in
                  FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                    uu___3 d1 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStarC_Errors_Msg.text "got expression" in
                    FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                      uu___5 ed in
                  let uu___5 =
                    let uu___6 = FStarC_Errors_Msg.text "of type" in
                    FStarC_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                      uu___6 d2 in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
              [uu___1] in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              rng FStarC_Errors_Codes.Fatal_UnexpectedExpressionType ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___)
let (expected_pattern_of_type :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term ->
          (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu___ = err_msg_type_strings env t1 t2 in
          match uu___ with
          | (s1, s2) ->
              let uu___1 =
                let uu___2 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
                FStarC_Compiler_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu___2 s2 in
              (FStarC_Errors_Codes.Fatal_UnexpectedPattern, uu___1)
let (basic_type_error :
  FStarC_TypeChecker_Env.env ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> unit)
  =
  fun env ->
    fun rng ->
      fun eopt ->
        fun t1 ->
          fun t2 ->
            let uu___ = err_msg_type_strings env t1 t2 in
            match uu___ with
            | (s1, s2) ->
                let msg =
                  match eopt with
                  | FStar_Pervasives_Native.None ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Errors_Msg.text "Expected type" in
                          let uu___4 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t1 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___3 uu___4 in
                        let uu___3 =
                          let uu___4 = FStarC_Errors_Msg.text "got type" in
                          let uu___5 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t2 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___4 uu___5 in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                      [uu___1]
                  | FStar_Pervasives_Native.Some e ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Errors_Msg.text "Expected type" in
                          let uu___4 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t1 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___3 uu___4 in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = FStarC_Errors_Msg.text "but" in
                            let uu___6 =
                              FStarC_TypeChecker_Normalize.term_to_doc env e in
                            FStarC_Pprint.prefix (Prims.of_int (4))
                              Prims.int_one uu___5 uu___6 in
                          let uu___5 =
                            let uu___6 = FStarC_Errors_Msg.text "has type" in
                            let uu___7 =
                              FStarC_TypeChecker_Normalize.term_to_doc env t2 in
                            FStarC_Pprint.prefix (Prims.of_int (4))
                              Prims.int_one uu___6 uu___7 in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                      [uu___1] in
                FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                  rng FStarC_Errors_Codes.Error_TypeError ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic msg)
let raise_basic_type_error :
  'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option ->
          FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> 'a
  =
  fun env ->
    fun rng ->
      fun eopt ->
        fun t1 ->
          fun t2 ->
            let uu___ = err_msg_type_strings env t1 t2 in
            match uu___ with
            | (s1, s2) ->
                let msg =
                  match eopt with
                  | FStar_Pervasives_Native.None ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Errors_Msg.text "Expected type" in
                          let uu___4 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t1 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___3 uu___4 in
                        let uu___3 =
                          let uu___4 = FStarC_Errors_Msg.text "got type" in
                          let uu___5 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t2 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___4 uu___5 in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                      [uu___1]
                  | FStar_Pervasives_Native.Some e ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Errors_Msg.text "Expected type" in
                          let uu___4 =
                            FStarC_TypeChecker_Normalize.term_to_doc env t1 in
                          FStarC_Pprint.prefix (Prims.of_int (4))
                            Prims.int_one uu___3 uu___4 in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = FStarC_Errors_Msg.text "but" in
                            let uu___6 =
                              FStarC_TypeChecker_Normalize.term_to_doc env e in
                            FStarC_Pprint.prefix (Prims.of_int (4))
                              Prims.int_one uu___5 uu___6 in
                          let uu___5 =
                            let uu___6 = FStarC_Errors_Msg.text "has type" in
                            let uu___7 =
                              FStarC_TypeChecker_Normalize.term_to_doc env t2 in
                            FStarC_Pprint.prefix (Prims.of_int (4))
                              Prims.int_one uu___6 uu___7 in
                          FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                        FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
                      [uu___1] in
                FStarC_Errors.raise_error
                  FStarC_Class_HasRange.hasRange_range rng
                  FStarC_Errors_Codes.Error_TypeError ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic msg)
let (occurs_check : (FStarC_Errors_Codes.error_code * Prims.string)) =
  (FStarC_Errors_Codes.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let constructor_fails_the_positivity_check :
  'uuuuu .
    'uuuuu ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Ident.lid -> (FStarC_Errors_Codes.error_code * Prims.string)
  =
  fun env ->
    fun d ->
      fun l ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_term d in
          let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident l in
          FStarC_Compiler_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu___1 uu___2 in
        (FStarC_Errors_Codes.Fatal_ConstructorFailedCheck, uu___)
let (inline_type_annotation_and_val_decl :
  FStarC_Ident.lid -> (FStarC_Errors_Codes.error_code * Prims.string)) =
  fun l ->
    let uu___ =
      let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident l in
      FStarC_Compiler_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu___1 in
    (FStarC_Errors_Codes.Fatal_DuplicateTypeAnnotationAndValDecl, uu___)
let (inferred_type_causes_variable_to_escape :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.bv ->
        (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun env ->
    fun t ->
      fun x ->
        let uu___ =
          let uu___1 = FStarC_TypeChecker_Normalize.term_to_string env t in
          let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
          FStarC_Compiler_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu___1 uu___2 in
        (FStarC_Errors_Codes.Fatal_InferredTypeCauseVarEscape, uu___)
let expected_function_typ :
  'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.term -> 'a
  =
  fun env ->
    fun rng ->
      fun t ->
        let uu___ =
          let uu___1 = FStarC_Errors_Msg.text "Expected a function." in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStarC_Errors_Msg.text "Got an expression of type:" in
              let uu___5 = FStarC_TypeChecker_Normalize.term_to_doc env t in
              FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___4
                uu___5 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
          FStarC_Errors_Codes.Fatal_FunctionTypeExpected ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___)
let (expected_poly_typ :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term ->
          (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun env ->
    fun f ->
      fun t ->
        fun targ ->
          let uu___ =
            let uu___1 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term f in
            let uu___2 = FStarC_TypeChecker_Normalize.term_to_string env t in
            let uu___3 = FStarC_TypeChecker_Normalize.term_to_string env targ in
            FStarC_Compiler_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu___1 uu___2 uu___3 in
          (FStarC_Errors_Codes.Fatal_PolyTypeExpected, uu___)
let (disjunctive_pattern_vars :
  FStarC_Syntax_Syntax.bv Prims.list ->
    FStarC_Syntax_Syntax.bv Prims.list ->
      (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun v1 ->
    fun v2 ->
      let vars v =
        let uu___ =
          FStarC_Compiler_List.map
            (FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv) v in
        FStarC_Compiler_String.concat ", " uu___ in
      let uu___ =
        let uu___1 = vars v1 in
        let uu___2 = vars v2 in
        FStarC_Compiler_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu___1 uu___2 in
      (FStarC_Errors_Codes.Fatal_DisjuctivePatternVarsMismatch, uu___)
let (name_and_result :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    (Prims.string * FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax))
  =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t -> ("Tot", t)
    | FStarC_Syntax_Syntax.GTotal t -> ("GTot", t)
    | FStarC_Syntax_Syntax.Comp ct ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Ident.showable_lident
            ct.FStarC_Syntax_Syntax.effect_name in
        (uu___, (ct.FStarC_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation :
  'uuuuu 'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        'uuuuu ->
          FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
            FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> 'a
  =
  fun env ->
    fun r ->
      fun e ->
        fun c ->
          fun c' ->
            let ppt = FStarC_TypeChecker_Normalize.term_to_doc env in
            let uu___ = name_and_result c in
            match uu___ with
            | (f1, r1) ->
                let uu___1 = name_and_result c' in
                (match uu___1 with
                 | (f2, r2) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Errors_Msg.text "Computed type" in
                           let uu___6 = ppt r1 in
                           FStarC_Pprint.prefix (Prims.of_int (2))
                             Prims.int_one uu___5 uu___6 in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 = FStarC_Errors_Msg.text "and effect" in
                             let uu___8 = FStarC_Errors_Msg.text f1 in
                             FStarC_Pprint.prefix (Prims.of_int (2))
                               Prims.int_one uu___7 uu___8 in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Errors_Msg.text
                                   "is not compatible with the annotated type" in
                               let uu___10 = ppt r2 in
                               FStarC_Pprint.prefix (Prims.of_int (2))
                                 Prims.int_one uu___9 uu___10 in
                             let uu___9 =
                               let uu___10 =
                                 FStarC_Errors_Msg.text "and effect" in
                               let uu___11 = FStarC_Errors_Msg.text f2 in
                               FStarC_Pprint.prefix (Prims.of_int (2))
                                 Prims.int_one uu___10 uu___11 in
                             FStarC_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                           FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                         FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                       [uu___3] in
                     FStarC_Errors.raise_error
                       FStarC_Class_HasRange.hasRange_range r
                       FStarC_Errors_Codes.Fatal_ComputedTypeNotMatchAnnotation
                       ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___2))
let computed_computation_type_does_not_match_annotation_eq :
  'uuuuu 'a .
    FStarC_TypeChecker_Env.env ->
      FStarC_Compiler_Range_Type.range ->
        'uuuuu ->
          FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp -> 'a
  =
  fun env ->
    fun r ->
      fun e ->
        fun c ->
          fun c' ->
            let ppc = FStarC_TypeChecker_Normalize.comp_to_doc env in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStarC_Errors_Msg.text "Computed type" in
                  let uu___4 = ppc c in
                  FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                    uu___3 uu___4 in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Errors_Msg.text "does not match annotated type" in
                    let uu___6 = ppc c' in
                    FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___5 uu___6 in
                  let uu___5 =
                    FStarC_Errors_Msg.text "and no subtyping was allowed" in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
              [uu___1] in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
              FStarC_Errors_Codes.Fatal_ComputedTypeNotMatchAnnotation ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___)
let unexpected_non_trivial_precondition_on_term :
  'a . FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> 'a =
  fun env ->
    fun f ->
      let uu___ =
        let uu___1 = FStarC_TypeChecker_Normalize.term_to_string env f in
        FStarC_Compiler_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu___1 in
      FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
        FStarC_Errors_Codes.Fatal_UnExpectedPreCondition ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
let __expected_eff_expression :
  'uuuuu .
    Prims.string ->
      FStarC_Compiler_Range_Type.range ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.comp ->
            Prims.string FStar_Pervasives_Native.option -> 'uuuuu
  =
  fun effname ->
    fun rng ->
      fun e ->
        fun c ->
          fun reason ->
            let uu___ =
              let uu___1 =
                FStarC_Errors_Msg.text
                  (Prims.strcat "Expected a "
                     (Prims.strcat effname " expression.")) in
              let uu___2 =
                let uu___3 =
                  match reason with
                  | FStar_Pervasives_Native.None -> FStarC_Pprint.empty
                  | FStar_Pervasives_Native.Some msg ->
                      let uu___4 = FStarC_Pprint.break_ Prims.int_one in
                      let uu___5 =
                        let uu___6 = FStarC_Pprint.doc_of_string "Because:" in
                        let uu___7 =
                          FStarC_Pprint.words (Prims.strcat msg ".") in
                        uu___6 :: uu___7 in
                      FStarC_Pprint.flow uu___4 uu___5 in
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = FStarC_Errors_Msg.text "Got an expression" in
                      let uu___8 =
                        FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term e in
                      FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                        uu___7 uu___8 in
                    let uu___7 =
                      let uu___8 =
                        let uu___9 = FStarC_Errors_Msg.text "with effect" in
                        let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 = name_and_result c in
                              FStar_Pervasives_Native.fst uu___13 in
                            FStarC_Pprint.doc_of_string uu___12 in
                          FStarC_Pprint.squotes uu___11 in
                        FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                          uu___9 uu___10 in
                      FStarC_Pprint.op_Hat_Hat uu___8 FStarC_Pprint.dot in
                    FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                  [uu___5] in
                uu___3 :: uu___4 in
              uu___1 :: uu___2 in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              rng FStarC_Errors_Codes.Fatal_ExpectedGhostExpression ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___)
let expected_pure_expression :
  'uuuuu .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.comp ->
          Prims.string FStar_Pervasives_Native.option -> 'uuuuu
  =
  fun rng ->
    fun e ->
      fun c -> fun reason -> __expected_eff_expression "pure" rng e c reason
let expected_ghost_expression :
  'uuuuu .
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.comp ->
          Prims.string FStar_Pervasives_Native.option -> 'uuuuu
  =
  fun rng ->
    fun e ->
      fun c -> fun reason -> __expected_eff_expression "ghost" rng e c reason
let (expected_effect_1_got_effect_2 :
  FStarC_Ident.lident ->
    FStarC_Ident.lident -> (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun c1 ->
    fun c2 ->
      let uu___ =
        let uu___1 = FStarC_Class_Show.show FStarC_Ident.showable_lident c1 in
        let uu___2 = FStarC_Class_Show.show FStarC_Ident.showable_lident c2 in
        FStarC_Compiler_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu___1 uu___2 in
      (FStarC_Errors_Codes.Fatal_UnexpectedEffect, uu___)
let (failed_to_prove_specification_of :
  FStarC_Syntax_Syntax.lbname ->
    Prims.string Prims.list ->
      (FStarC_Errors_Codes.error_code * Prims.string))
  =
  fun l ->
    fun lbls ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_either FStarC_Syntax_Print.showable_bv
               FStarC_Syntax_Print.showable_fv) l in
        FStarC_Compiler_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu___1 (FStarC_Compiler_String.concat ", " lbls) in
      (FStarC_Errors_Codes.Error_TypeCheckerFailToProve, uu___)
let (warn_top_level_effect : FStarC_Compiler_Range_Type.range -> unit) =
  fun rng ->
    FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range rng
      FStarC_Errors_Codes.Warning_TopLevelEffect ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
      (Obj.magic
         "Top-level let-bindings must be total; this term may have effects")