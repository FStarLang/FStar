open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string, FStar_Ident.lid) FStar_Util.either *
            FStar_Syntax_Syntax.typ * FStar_Range.range)
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun file ->
      fun row ->
        fun col ->
          let uu____39 =
            let uu____42 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____42 file row col in
          match uu____39 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____101 =
                     let uu____113 =
                       let uu____119 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____119 in
                     let uu____122 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____113,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____122) in
                   FStar_Pervasives_Native.Some uu____101
               | FStar_Util.Inr fv ->
                   let uu____140 =
                     let uu____152 =
                       let uu____158 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____158 in
                     let uu____160 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____152,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____160) in
                   FStar_Pervasives_Native.Some uu____140)
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____227 ->
               (let uu____229 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____231 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____233 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____231, uu____233)))
        else (s1, s2)
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let s1 = FStar_TypeChecker_Normalize.comp_to_string env c1 in
        let s2 = FStar_TypeChecker_Normalize.comp_to_string env c2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____291 ->
               (let uu____293 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args" in
                ());
               (let uu____295 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1 in
                let uu____297 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2 in
                (uu____295, uu____297)))
        else (s1, s2)
let (exhaustiveness_check : Prims.string) = "Patterns are incomplete"
let (subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun x ->
          let uu____330 = err_msg_type_strings env t1 t2 in
          match uu____330 with
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
        let uu____372 =
          let uu____374 = FStar_TypeChecker_Normalize.term_to_string env k in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____374 in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____372)
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
          let uu____406 =
            let uu____408 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____410 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____408 uu____410 msg in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____406)
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
          let uu____448 = err_msg_type_strings env t1 t2 in
          match uu____448 with
          | (s1, s2) ->
              let uu____466 =
                let uu____468 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____468 s2 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____466)
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
          let uu____498 = err_msg_type_strings env t1 t2 in
          match uu____498 with
          | (s1, s2) ->
              let uu____516 =
                let uu____518 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____518 s2 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____516)
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
          let uu____552 = err_msg_type_strings env t1 t2 in
          match uu____552 with
          | (s1, s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____575 =
                      FStar_TypeChecker_Normalize.term_to_string env e in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____575 s2 in
              (FStar_Errors.Error_TypeError, msg)
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let (incompatible_kinds :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun k1 ->
      fun k2 ->
        let uu____608 =
          let uu____610 = FStar_TypeChecker_Normalize.term_to_string env k1 in
          let uu____612 = FStar_TypeChecker_Normalize.term_to_string env k2 in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____610 uu____612 in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____608)
let (constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun d ->
      fun t ->
        fun t' ->
          let uu____642 =
            let uu____644 = FStar_Syntax_Print.term_to_string d in
            let uu____646 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____648 = FStar_TypeChecker_Normalize.term_to_string env t' in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____644 uu____646 uu____648 in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____642)
let constructor_fails_the_positivity_check :
  'Auu____661 .
    'Auu____661 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun d ->
      fun l ->
        let uu____682 =
          let uu____684 = FStar_Syntax_Print.term_to_string d in
          let uu____686 = FStar_Syntax_Print.lid_to_string l in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____684 uu____686 in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____682)
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l ->
    let uu____701 =
      let uu____703 = FStar_Syntax_Print.lid_to_string l in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____703 in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____701)
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      fun x ->
        let uu____728 =
          let uu____730 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____732 = FStar_Syntax_Print.bv_to_string x in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____730 uu____732 in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____728)
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun t ->
      let uu____752 =
        let uu____754 = FStar_TypeChecker_Normalize.term_to_string env t in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____754 in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____752)
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
          let uu____784 =
            let uu____786 = FStar_Syntax_Print.term_to_string f in
            let uu____788 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____790 =
              FStar_TypeChecker_Normalize.term_to_string env targ in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____786 uu____788 uu____790 in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____784)
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1 ->
    fun v2 ->
      let vars v3 =
        let uu____829 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____829 (FStar_String.concat ", ") in
      let uu____844 =
        let uu____846 = vars v1 in
        let uu____848 = vars v2 in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____846 uu____848 in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____844)
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____877) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t, uu____891) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____905 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____905, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation :
  'Auu____921 .
    FStar_TypeChecker_Env.env ->
      'Auu____921 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____955 = name_and_result c in
          match uu____955 with
          | (f1, r1) ->
              let uu____976 = name_and_result c' in
              (match uu____976 with
               | (f2, r2) ->
                   let uu____997 = err_msg_type_strings env r1 r2 in
                   (match uu____997 with
                    | (s1, s2) ->
                        let uu____1015 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2 in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1015)))
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____1030 .
    FStar_TypeChecker_Env.env ->
      'Auu____1030 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____1056 = err_msg_comp_strings env c c' in
          match uu____1056 with
          | (s1, s2) ->
              let uu____1074 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1074)
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env ->
    fun f ->
      let uu____1094 =
        let uu____1096 = FStar_TypeChecker_Normalize.term_to_string env f in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1096 in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1094)
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      let uu____1120 =
        let uu____1122 = FStar_Syntax_Print.term_to_string e in
        let uu____1124 =
          let uu____1126 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1126 in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____1122 uu____1124 in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____1120)
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e ->
    fun c ->
      let uu____1167 =
        let uu____1169 = FStar_Syntax_Print.term_to_string e in
        let uu____1171 =
          let uu____1173 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1173 in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1169 uu____1171 in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1167)
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1 ->
    fun c2 ->
      let uu____1210 =
        let uu____1212 = FStar_Syntax_Print.lid_to_string c1 in
        let uu____1214 = FStar_Syntax_Print.lid_to_string c2 in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1212 uu____1214 in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1210)
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l ->
    fun lbls ->
      let uu____1240 =
        let uu____1242 = FStar_Syntax_Print.lbname_to_string l in
        let uu____1244 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1242 uu____1244 in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1240)
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1275 ->
          let uu____1279 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1279 in
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
      let uu____1316 =
        let uu____1318 = FStar_Syntax_Print.lid_to_string l in
        let uu____1320 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1318 uu____1320 in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1316)