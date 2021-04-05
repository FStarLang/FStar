open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string, FStar_Ident.lid) FStar_Pervasives.either *
            FStar_Syntax_Syntax.typ * FStar_Range.range)
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun file ->
      fun row ->
        fun col ->
          let uu___ =
            let uu___1 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu___1 file row col in
          match uu___ with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Pervasives.Inl bv ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Pervasives.Inl uu___3 in
                     let uu___3 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu___2, (info.FStar_TypeChecker_Common.identifier_ty),
                       uu___3) in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives.Inr fv ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Pervasives.Inr uu___3 in
                     let uu___3 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu___2, (info.FStar_TypeChecker_Common.identifier_ty),
                       uu___3) in
                   FStar_Pervasives_Native.Some uu___1)
let print_discrepancy :
  'a . ('a -> Prims.string) -> 'a -> 'a -> (Prims.string * Prims.string) =
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
        let full l = FStar_List.for_all (fun b -> b) l in
        let get_bool_option s =
          let uu___ = FStar_Options.get_option s in
          match uu___ with
          | FStar_Options.Bool b -> b
          | uu___1 -> failwith "print_discrepancy: impossible" in
        let set_bool_option s b =
          FStar_Options.set_option s (FStar_Options.Bool b) in
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
          match () with
          | () when full cur ->
              let uu___ = print () in
              (match uu___ with | (xs, ys, uu___1) -> (xs, ys))
          | () when let uu___ = blist_leq bas cur in Prims.op_Negation uu___
              -> let uu___ = succ cur in go uu___
          | () ->
              (set cur;
               (let uu___1 = print () in
                match uu___1 with
                | (xs, ys, true) -> (xs, ys)
                | uu___2 -> let uu___3 = succ cur in go uu___3)) in
        FStar_Options.with_saved_options (fun uu___ -> go bas)
let (errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    FStar_Errors.error Prims.list ->
      (Prims.string, Prims.string) FStar_Pervasives.either ->
        FStar_Errors.error Prims.list)
  =
  fun env ->
    fun errs ->
      fun smt_detail ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Pervasives.Inr d ->
              Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
          | FStar_Pervasives.Inl d when (FStar_Util.trim_string d) <> "" ->
              Prims.op_Hat msg (Prims.op_Hat "; " d)
          | uu___ -> msg in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu___ ->
                  match uu___ with
                  | (e, msg, r, ctx) ->
                      let uu___1 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu___2 = FStar_TypeChecker_Env.get_range env in
                          (e, msg, uu___2, ctx)
                        else
                          (let r' =
                             let uu___3 = FStar_Range.use_range r in
                             FStar_Range.set_def_range r uu___3 in
                           let uu___3 =
                             let uu___4 = FStar_Range.file_of_range r' in
                             let uu___5 =
                               let uu___6 =
                                 FStar_TypeChecker_Env.get_range env in
                               FStar_Range.file_of_range uu___6 in
                             uu___4 <> uu___5 in
                           if uu___3
                           then
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStar_Range.string_of_use_range r in
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStar_Range.use_range r in
                                         let uu___12 =
                                           FStar_Range.def_range r in
                                         uu___11 <> uu___12 in
                                       if uu___10
                                       then
                                         let uu___11 =
                                           let uu___12 =
                                             FStar_Range.string_of_def_range
                                               r in
                                           Prims.op_Hat uu___12 ")" in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu___11
                                       else "" in
                                     Prims.op_Hat ")" uu___9 in
                                   Prims.op_Hat uu___7 uu___8 in
                                 Prims.op_Hat " (Also see: " uu___6 in
                               Prims.op_Hat msg uu___5 in
                             let uu___5 = FStar_TypeChecker_Env.get_range env in
                             (e, uu___4, uu___5, ctx)
                           else (e, msg, r, ctx)) in
                      (match uu___1 with
                       | (e1, msg1, r1, ctx1) ->
                           (e1, (maybe_add_smt_detail msg1), r1, ctx1)))) in
        errs1
let (add_errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    FStar_Errors.error Prims.list ->
      (Prims.string, Prims.string) FStar_Pervasives.either -> unit)
  =
  fun env ->
    fun errs ->
      fun smt_detail ->
        let uu___ = errors_smt_detail env errs smt_detail in
        FStar_Errors.add_errors uu___
let (add_errors :
  FStar_TypeChecker_Env.env -> FStar_Errors.error Prims.list -> unit) =
  fun env ->
    fun errs -> add_errors_smt_detail env errs (FStar_Pervasives.Inl "")
let (log_issue :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> (FStar_Errors.raw_error * Prims.string) -> unit)
  =
  fun env ->
    fun r ->
      fun uu___ ->
        match uu___ with
        | (e, m) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Errors.get_ctx () in (e, m, r, uu___3) in
              [uu___2] in
            add_errors env uu___1
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        print_discrepancy (FStar_TypeChecker_Normalize.term_to_string env) t1
          t2
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        print_discrepancy (FStar_TypeChecker_Normalize.comp_to_string env) c1
          c2
let (exhaustiveness_check : Prims.string) = "Patterns are incomplete"
let (subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun uu___ ->
          let uu___1 = err_msg_type_strings env t1 t2 in
          match uu___1 with
          | (s1, s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
let (ill_kinded_type : Prims.string) = "Ill-kinded type"
let (totality_check : Prims.string) = "This term may not terminate"
let (unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun m ->
      fun k ->
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid m in
          let uu___2 = FStar_TypeChecker_Normalize.term_to_string env k in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type -> WP a -> Effect); got %s"
            uu___1 uu___2 in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu___)
let (expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun msg ->
      fun t ->
        fun e ->
          let uu___ =
            let uu___1 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu___2 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu___1 uu___2 msg in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu___)
let (unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string))
  =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
let (expected_expression_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu___ = err_msg_type_strings env t1 t2 in
          match uu___ with
          | (s1, s2) ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu___2 s2 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu___1)
let (expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu___ = err_msg_type_strings env t1 t2 in
          match uu___ with
          | (s1, s2) ->
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu___2 s2 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu___1)
let (basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun eopt ->
      fun t1 ->
        fun t2 ->
          let uu___ = err_msg_type_strings env t1 t2 in
          match uu___ with
          | (s1, s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu___1 =
                      FStar_TypeChecker_Normalize.term_to_string env e in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu___1 s2 in
              (FStar_Errors.Error_TypeError, msg)
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let constructor_fails_the_positivity_check :
  'uuuuu .
    'uuuuu ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun d ->
      fun l ->
        let uu___ =
          let uu___1 = FStar_Syntax_Print.term_to_string d in
          let uu___2 = FStar_Syntax_Print.lid_to_string l in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu___1 uu___2 in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu___)
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu___ =
      let uu___1 = FStar_Syntax_Print.lid_to_string l in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu___1 in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu___)
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      fun x ->
        let uu___ =
          let uu___1 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu___2 = FStar_Syntax_Print.bv_to_string x in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu___1 uu___2 in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu___)
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      let uu___ =
        let uu___1 = FStar_TypeChecker_Normalize.term_to_string env t in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu___1 in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu___)
let (expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun f ->
      fun t ->
        fun targ ->
          let uu___ =
            let uu___1 = FStar_Syntax_Print.term_to_string f in
            let uu___2 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu___3 = FStar_TypeChecker_Normalize.term_to_string env targ in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu___1 uu___2 uu___3 in
          (FStar_Errors.Fatal_PolyTypeExpected, uu___)
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1 ->
    fun v2 ->
      let vars v =
        let uu___ =
          FStar_All.pipe_right v
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu___ (FStar_String.concat ", ") in
      let uu___ =
        let uu___1 = vars v1 in
        let uu___2 = vars v2 in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu___1 uu___2 in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu___)
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu___) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t, uu___) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu___ =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu___, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      'uuuuu ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu___ = name_and_result c in
          match uu___ with
          | (f1, r1) ->
              let uu___1 = name_and_result c' in
              (match uu___1 with
               | (f2, r2) ->
                   let uu___2 = err_msg_type_strings env r1 r2 in
                   (match uu___2 with
                    | (s1, s2) ->
                        let uu___3 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2 in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu___3)))
let computed_computation_type_does_not_match_annotation_eq :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      'uuuuu ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu___ = err_msg_comp_strings env c c' in
          match uu___ with
          | (s1, s2) ->
              let uu___1 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu___1)
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun f ->
      let uu___ =
        let uu___1 = FStar_TypeChecker_Normalize.term_to_string env f in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu___1 in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu___)
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      Prims.string -> (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      fun reason ->
        let msg = "Expected a pure expression" in
        let msg1 =
          if reason = ""
          then msg
          else FStar_Util.format1 (Prims.op_Hat msg " (%s)") reason in
        let uu___ =
          let uu___1 = FStar_Syntax_Print.term_to_string e in
          let uu___2 =
            let uu___3 = name_and_result c in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu___3 in
          FStar_Util.format2
            (Prims.op_Hat msg1
               "; got an expression \"%s\" with effect \"%s\"") uu___1 uu___2 in
        (FStar_Errors.Fatal_ExpectedPureExpression, uu___)
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      Prims.string -> (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      fun reason ->
        let msg = "Expected a ghost expression" in
        let msg1 =
          if reason = ""
          then msg
          else FStar_Util.format1 (Prims.op_Hat msg " (%s)") reason in
        let uu___ =
          let uu___1 = FStar_Syntax_Print.term_to_string e in
          let uu___2 =
            let uu___3 = name_and_result c in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu___3 in
          FStar_Util.format2
            (Prims.op_Hat msg1
               "; got an expression \"%s\" with effect \"%s\"") uu___1 uu___2 in
        (FStar_Errors.Fatal_ExpectedGhostExpression, uu___)
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1 ->
    fun c2 ->
      let uu___ =
        let uu___1 = FStar_Syntax_Print.lid_to_string c1 in
        let uu___2 = FStar_Syntax_Print.lid_to_string c2 in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu___1 uu___2 in
      (FStar_Errors.Fatal_UnexpectedEffect, uu___)
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l ->
    fun lbls ->
      let uu___ =
        let uu___1 = FStar_Syntax_Print.lbname_to_string l in
        let uu___2 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu___1 uu___2 in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu___)
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu___ ->
          let uu___1 = FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu___1 in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
let (top_level_effect : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
let (cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun l ->
    fun a ->
      let uu___ =
        let uu___1 = FStar_Syntax_Print.lid_to_string l in
        let uu___2 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu___1 uu___2 in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu___)