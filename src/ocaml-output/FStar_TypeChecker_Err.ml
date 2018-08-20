open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string, FStar_Ident.lid) FStar_Util.either,
            FStar_Syntax_Syntax.typ, FStar_Range.range)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun file ->
      fun row ->
        fun col ->
          let uu____33 =
            let uu____36 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____36 file row col in
          match uu____33 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____92 =
                     let uu____103 =
                       let uu____108 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____108 in
                     let uu____109 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____103,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____109) in
                   FStar_Pervasives_Native.Some uu____92
               | FStar_Util.Inr fv ->
                   let uu____125 =
                     let uu____136 =
                       let uu____141 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____141 in
                     let uu____142 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____136,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____142) in
                   FStar_Pervasives_Native.Some uu____125)
let (add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error, Prims.string, FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list -> unit)
  =
  fun env ->
    fun errs ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____225 ->
                match uu____225 with
                | (e, msg, r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____247 = FStar_TypeChecker_Env.get_range env in
                      (e, msg, uu____247)
                    else
                      (let r' =
                         let uu____250 = FStar_Range.use_range r in
                         FStar_Range.set_def_range r uu____250 in
                       let uu____251 =
                         let uu____252 = FStar_Range.file_of_range r' in
                         let uu____253 =
                           let uu____254 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____254 in
                         uu____252 <> uu____253 in
                       if uu____251
                       then
                         let uu____261 =
                           let uu____262 =
                             let uu____263 =
                               let uu____264 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____264 ")" in
                             Prims.strcat "(Also see: " uu____263 in
                           Prims.strcat msg uu____262 in
                         let uu____265 = FStar_TypeChecker_Env.get_range env in
                         (e, uu____261, uu____265)
                       else (e, msg, r)))) in
      FStar_Errors.add_errors errs1
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____304 ->
               (let uu____306 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____307 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____308 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____307, uu____308)))
        else (s1, s2)
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        (Prims.string, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let s1 = FStar_TypeChecker_Normalize.comp_to_string env c1 in
        let s2 = FStar_TypeChecker_Normalize.comp_to_string env c2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____347 ->
               (let uu____349 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args" in
                ());
               (let uu____350 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1 in
                let uu____351 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2 in
                (uu____350, uu____351)))
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
          let uu____373 = err_msg_type_strings env t1 t2 in
          match uu____373 with
          | (s1, s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
let (ill_kinded_type : Prims.string) = "Ill-kinded type"
let (totality_check : Prims.string) = "This term may not terminate"
let (unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun m ->
      fun k ->
        let uu____399 =
          let uu____400 = FStar_TypeChecker_Normalize.term_to_string env k in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____400 in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____399)
let (expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun msg ->
      fun t ->
        fun e ->
          let uu____425 =
            let uu____426 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____427 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____426 uu____427 msg in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____425)
let (unexpected_implicit_argument :
  (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2) =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
let (expected_expression_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu____456 = err_msg_type_strings env t1 t2 in
          match uu____456 with
          | (s1, s2) ->
              let uu____467 =
                let uu____468 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____468 s2 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____467)
let (expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t1 ->
      fun e ->
        fun t2 ->
          let uu____493 = err_msg_type_strings env t1 t2 in
          match uu____493 with
          | (s1, s2) ->
              let uu____504 =
                let uu____505 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____505 s2 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____504)
let (basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun eopt ->
      fun t1 ->
        fun t2 ->
          let uu____534 = err_msg_type_strings env t1 t2 in
          match uu____534 with
          | (s1, s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____547 =
                      FStar_TypeChecker_Normalize.term_to_string env e in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____547 s2 in
              (FStar_Errors.Error_TypeError, msg)
let (occurs_check :
  (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let (incompatible_kinds :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun k1 ->
      fun k2 ->
        let uu____571 =
          let uu____572 = FStar_TypeChecker_Normalize.term_to_string env k1 in
          let uu____573 = FStar_TypeChecker_Normalize.term_to_string env k2 in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____572 uu____573 in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____571)
let (constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      fun t ->
        fun t' ->
          let uu____598 =
            let uu____599 = FStar_Syntax_Print.term_to_string d in
            let uu____600 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____601 = FStar_TypeChecker_Normalize.term_to_string env t' in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____599 uu____600 uu____601 in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____598)
let constructor_fails_the_positivity_check :
  'Auu____610 .
    'Auu____610 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun d ->
      fun l ->
        let uu____630 =
          let uu____631 = FStar_Syntax_Print.term_to_string d in
          let uu____632 = FStar_Syntax_Print.lid_to_string l in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____631 uu____632 in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____630)
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    let uu____642 =
      let uu____643 = FStar_Syntax_Print.lid_to_string l in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____643 in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____642)
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t ->
      fun x ->
        let uu____663 =
          let uu____664 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____665 = FStar_Syntax_Print.bv_to_string x in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____664 uu____665 in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____663)
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun t ->
      let uu____680 =
        let uu____681 = FStar_TypeChecker_Normalize.term_to_string env t in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____681 in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____680)
let (expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error, Prims.string)
            FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun f ->
      fun t ->
        fun targ ->
          let uu____706 =
            let uu____707 = FStar_Syntax_Print.term_to_string f in
            let uu____708 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____709 =
              FStar_TypeChecker_Normalize.term_to_string env targ in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____707 uu____708 uu____709 in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____706)
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1 ->
    fun v2 ->
      let vars v3 =
        let uu____742 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____742 (FStar_String.concat ", ") in
      let uu____751 =
        let uu____752 = vars v1 in
        let uu____753 = vars v2 in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____752 uu____753 in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____751)
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string, FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____776) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t, uu____788) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____800 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____800, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation :
  'Auu____813 .
    FStar_TypeChecker_Env.env ->
      'Auu____813 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error, Prims.string)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____846 = name_and_result c in
          match uu____846 with
          | (f1, r1) ->
              let uu____863 = name_and_result c' in
              (match uu____863 with
               | (f2, r2) ->
                   let uu____880 = err_msg_type_strings env r1 r2 in
                   (match uu____880 with
                    | (s1, s2) ->
                        let uu____891 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2 in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____891)))
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____902 .
    FStar_TypeChecker_Env.env ->
      'Auu____902 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp ->
            (FStar_Errors.raw_error, Prims.string)
              FStar_Pervasives_Native.tuple2
  =
  fun env ->
    fun e ->
      fun c ->
        fun c' ->
          let uu____927 = err_msg_comp_strings env c c' in
          match uu____927 with
          | (s1, s2) ->
              let uu____938 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____938)
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun f ->
      let uu____953 =
        let uu____954 = FStar_TypeChecker_Normalize.term_to_string env f in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____954 in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____953)
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun c ->
      let uu____973 =
        let uu____974 = FStar_Syntax_Print.term_to_string e in
        let uu____975 =
          let uu____976 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____976 in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____974 uu____975 in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____973)
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun c ->
      let uu____1009 =
        let uu____1010 = FStar_Syntax_Print.term_to_string e in
        let uu____1011 =
          let uu____1012 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1012 in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1010 uu____1011 in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1009)
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun c1 ->
    fun c2 ->
      let uu____1041 =
        let uu____1042 = FStar_Syntax_Print.lid_to_string c1 in
        let uu____1043 = FStar_Syntax_Print.lid_to_string c2 in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1042 uu____1043 in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1041)
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    fun lbls ->
      let uu____1062 =
        let uu____1063 = FStar_Syntax_Print.lbname_to_string l in
        let uu____1064 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1063 uu____1064 in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1062)
let (failed_to_prove_specification :
  Prims.string Prims.list ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun lbls ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1081 ->
          let uu____1084 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1084 in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
let (top_level_effect :
  (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2) =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
let (cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    fun a ->
      let uu____1109 =
        let uu____1110 = FStar_Syntax_Print.lid_to_string l in
        let uu____1111 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1110 uu____1111 in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1109)