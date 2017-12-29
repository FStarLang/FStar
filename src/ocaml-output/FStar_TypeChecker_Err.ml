open Prims
let info_at_pos:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string,FStar_Ident.lid) FStar_Util.either,FStar_Syntax_Syntax.typ,
            FStar_Range.range) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option
  =
  fun env  ->
    fun file  ->
      fun row  ->
        fun col  ->
          let uu____25 =
            let uu____28 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____28 file row col in
          match uu____25 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____113 =
                     let uu____124 =
                       let uu____129 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____129 in
                     let uu____130 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____124,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____130) in
                   FStar_Pervasives_Native.Some uu____113
               | FStar_Util.Inr fv ->
                   let uu____146 =
                     let uu____157 =
                       let uu____162 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____162 in
                     let uu____163 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____157,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____163) in
                   FStar_Pervasives_Native.Some uu____146)
let add_errors:
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____242  ->
                match uu____242 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____264 = FStar_TypeChecker_Env.get_range env in
                      (e, msg, uu____264)
                    else
                      (let r' =
                         let uu____267 = FStar_Range.use_range r in
                         FStar_Range.set_def_range r uu____267 in
                       let uu____268 =
                         let uu____269 = FStar_Range.file_of_range r' in
                         let uu____270 =
                           let uu____271 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____271 in
                         uu____269 <> uu____270 in
                       if uu____268
                       then
                         let uu____278 =
                           let uu____279 =
                             let uu____280 =
                               let uu____281 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____281 ")" in
                             Prims.strcat "(Also see: " uu____280 in
                           Prims.strcat msg uu____279 in
                         let uu____282 = FStar_TypeChecker_Env.get_range env in
                         (e, uu____278, uu____282)
                       else (e, msg, r)))) in
      FStar_Errors.add_errors errs1
let err_msg_type_strings:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____315  ->
               (let uu____317 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____318 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____319 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____318, uu____319)))
        else (s1, s2)
let exhaustiveness_check: Prims.string = "Patterns are incomplete"
let subtyping_failed:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> Prims.unit -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun x  ->
          let uu____333 = err_msg_type_strings env t1 t2 in
          match uu____333 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
let ill_kinded_type: Prims.string = "Ill-kinded type"
let totality_check: Prims.string = "This term may not terminate"
let unexpected_signature_for_monad:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____353 =
          let uu____354 = FStar_TypeChecker_Normalize.term_to_string env k in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____354 in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____353)
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____371 =
            let uu____372 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____373 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____372 uu____373 msg in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____371)
let unexpected_implicit_argument:
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
let expected_expression_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____394 = err_msg_type_strings env t1 t2 in
          match uu____394 with
          | (s1,s2) ->
              let uu____405 =
                let uu____406 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____406 s2 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____405)
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____418 = err_msg_type_strings env t1 t2 in
        match uu____418 with
        | (s1,s2) ->
            FStar_Util.format3
              "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
              s1 s2
let expected_pattern_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____443 = err_msg_type_strings env t1 t2 in
          match uu____443 with
          | (s1,s2) ->
              let uu____454 =
                let uu____455 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____455 s2 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____454)
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____476 = err_msg_type_strings env t1 t2 in
          match uu____476 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____489 =
                      FStar_TypeChecker_Normalize.term_to_string env e in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____489 s2 in
              (FStar_Errors.Error_TypeError, msg)
let occurs_check:
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
let unification_well_formedness:
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Fatal_UnificationNotWellFormed,
    "Term or type of an unexpected sort")
let incompatible_kinds:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k1  ->
      fun k2  ->
        let uu____511 =
          let uu____512 = FStar_TypeChecker_Normalize.term_to_string env k1 in
          let uu____513 = FStar_TypeChecker_Normalize.term_to_string env k2 in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____512 uu____513 in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____511)
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____530 =
            let uu____531 = FStar_Syntax_Print.term_to_string d in
            let uu____532 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____533 = FStar_TypeChecker_Normalize.term_to_string env t' in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____531 uu____532 uu____533 in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____530)
let constructor_fails_the_positivity_check:
  'Auu____538 .
    'Auu____538 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____555 =
          let uu____556 = FStar_Syntax_Print.term_to_string d in
          let uu____557 = FStar_Syntax_Print.lid_to_string l in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____556 uu____557 in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____555)
let inline_type_annotation_and_val_decl:
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____565 =
      let uu____566 = FStar_Syntax_Print.lid_to_string l in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____566 in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____565)
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____580 =
          let uu____581 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____582 = FStar_Syntax_Print.bv_to_string x in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____581 uu____582 in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____580)
let expected_function_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____593 =
        let uu____594 = FStar_TypeChecker_Normalize.term_to_string env t in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____594 in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____593)
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____611 =
            let uu____612 = FStar_Syntax_Print.term_to_string f in
            let uu____613 = FStar_TypeChecker_Normalize.term_to_string env t in
            let uu____614 =
              FStar_TypeChecker_Normalize.term_to_string env targ in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____612 uu____613 uu____614 in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____611)
let nonlinear_pattern_variable:
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let m = FStar_Syntax_Print.bv_to_string x in
    let uu____623 =
      FStar_Util.format1
        "The pattern variable \"%s\" was used more than once" m in
    (FStar_Errors.Fatal_NonLinearPatternVars, uu____623)
let disjunctive_pattern_vars:
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____650 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____650 (FStar_String.concat ", ") in
      let uu____659 =
        let uu____660 = vars v1 in
        let uu____661 = vars v2 in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____660 uu____661 in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____659)
let name_and_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____682) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____694) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____706 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____706, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation:
  'Auu____714 .
    FStar_TypeChecker_Env.env ->
      'Auu____714 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error,Prims.string)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____743 = name_and_result c in
          match uu____743 with
          | (f1,r1) ->
              let uu____760 = name_and_result c' in
              (match uu____760 with
               | (f2,r2) ->
                   let uu____777 = err_msg_type_strings env r1 r2 in
                   (match uu____777 with
                    | (s1,s2) ->
                        let uu____788 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2 in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____788)))
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____799 =
        let uu____800 = FStar_TypeChecker_Normalize.term_to_string env f in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____800 in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____799)
let expected_pure_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun c  ->
      let uu____815 =
        let uu____816 = FStar_Syntax_Print.term_to_string e in
        let uu____817 =
          let uu____818 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____818 in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____816 uu____817 in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____815)
let expected_ghost_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun c  ->
      let uu____847 =
        let uu____848 = FStar_Syntax_Print.term_to_string e in
        let uu____849 =
          let uu____850 = name_and_result c in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____850 in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____848 uu____849 in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____847)
let expected_effect_1_got_effect_2:
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun c1  ->
    fun c2  ->
      let uu____875 =
        let uu____876 = FStar_Syntax_Print.lid_to_string c1 in
        let uu____877 = FStar_Syntax_Print.lid_to_string c2 in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____876 uu____877 in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____875)
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun lbls  ->
      let uu____892 =
        let uu____893 = FStar_Syntax_Print.lbname_to_string l in
        let uu____894 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____893 uu____894 in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____892)
let failed_to_prove_specification:
  Prims.string Prims.list ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____909 ->
          let uu____912 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____912 in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
let top_level_effect:
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
let cardinality_constraint_violated:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun a  ->
      let uu____933 =
        let uu____934 = FStar_Syntax_Print.lid_to_string l in
        let uu____935 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____934 uu____935 in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____933)