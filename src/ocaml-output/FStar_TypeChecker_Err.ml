open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string,FStar_Ident.lid) FStar_Util.either *
            FStar_Syntax_Syntax.typ * FStar_Range.range)
            FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun file  ->
      fun row  ->
        fun col  ->
          let uu____59620 =
            let uu____59623 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____59623 file row col
             in
          match uu____59620 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____59682 =
                     let uu____59694 =
                       let uu____59700 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____59700  in
                     let uu____59703 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____59694,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____59703)
                      in
                   FStar_Pervasives_Native.Some uu____59682
               | FStar_Util.Inr fv ->
                   let uu____59721 =
                     let uu____59733 =
                       let uu____59739 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____59739  in
                     let uu____59741 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____59733,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____59741)
                      in
                   FStar_Pervasives_Native.Some uu____59721)
  
let (add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      unit)
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____59834  ->
                match uu____59834 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____59862 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____59862)
                    else
                      (let r' =
                         let uu____59867 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____59867  in
                       let uu____59868 =
                         let uu____59870 = FStar_Range.file_of_range r'  in
                         let uu____59872 =
                           let uu____59874 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____59874  in
                         uu____59870 <> uu____59872  in
                       if uu____59868
                       then
                         let uu____59884 =
                           let uu____59886 =
                             let uu____59888 =
                               let uu____59890 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____59890 ")"  in
                             Prims.op_Hat " (Also see: " uu____59888  in
                           Prims.op_Hat msg uu____59886  in
                         let uu____59894 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____59884, uu____59894)
                       else (e, msg, r))))
         in
      FStar_Errors.add_errors errs1
  
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____59949  ->
               (let uu____59951 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____59953 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____59955 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____59953, uu____59955)))
        else (s1, s2)
  
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let s1 = FStar_TypeChecker_Normalize.comp_to_string env c1  in
        let s2 = FStar_TypeChecker_Normalize.comp_to_string env c2  in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____60013  ->
               (let uu____60015 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____60017 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____60019 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____60017, uu____60019)))
        else (s1, s2)
  
let (exhaustiveness_check : Prims.string) = "Patterns are incomplete" 
let (subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun x  ->
          let uu____60052 = err_msg_type_strings env t1 t2  in
          match uu____60052 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
  
let (ill_kinded_type : Prims.string) = "Ill-kinded type" 
let (totality_check : Prims.string) = "This term may not terminate" 
let (unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____60094 =
          let uu____60096 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____60096
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____60094)
  
let (expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____60128 =
            let uu____60130 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____60132 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____60130 uu____60132 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____60128)
  
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
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____60170 = err_msg_type_strings env t1 t2  in
          match uu____60170 with
          | (s1,s2) ->
              let uu____60188 =
                let uu____60190 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____60190 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____60188)
  
let (expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____60220 = err_msg_type_strings env t1 t2  in
          match uu____60220 with
          | (s1,s2) ->
              let uu____60238 =
                let uu____60240 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____60240 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____60238)
  
let (basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____60274 = err_msg_type_strings env t1 t2  in
          match uu____60274 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____60297 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____60297 s2
                 in
              (FStar_Errors.Error_TypeError, msg)
  
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
  
let (incompatible_kinds :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun k1  ->
      fun k2  ->
        let uu____60330 =
          let uu____60332 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____60334 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____60332 uu____60334
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____60330)
  
let (constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____60364 =
            let uu____60366 = FStar_Syntax_Print.term_to_string d  in
            let uu____60368 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____60370 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____60366 uu____60368 uu____60370
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____60364)
  
let constructor_fails_the_positivity_check :
  'Auu____60383 .
    'Auu____60383 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____60404 =
          let uu____60406 = FStar_Syntax_Print.term_to_string d  in
          let uu____60408 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____60406 uu____60408
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____60404)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____60423 =
      let uu____60425 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____60425
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____60423)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____60450 =
          let uu____60452 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____60454 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____60452 uu____60454
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____60450)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____60474 =
        let uu____60476 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____60476
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____60474)
  
let (expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____60506 =
            let uu____60508 = FStar_Syntax_Print.term_to_string f  in
            let uu____60510 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____60512 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____60508 uu____60510 uu____60512
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____60506)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____60551 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____60551 (FStar_String.concat ", ")  in
      let uu____60566 =
        let uu____60568 = vars v1  in
        let uu____60570 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____60568 uu____60570
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____60566)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____60599) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____60613) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____60627 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____60627, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____60643 .
    FStar_TypeChecker_Env.env ->
      'Auu____60643 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____60677 = name_and_result c  in
          match uu____60677 with
          | (f1,r1) ->
              let uu____60698 = name_and_result c'  in
              (match uu____60698 with
               | (f2,r2) ->
                   let uu____60719 = err_msg_type_strings env r1 r2  in
                   (match uu____60719 with
                    | (s1,s2) ->
                        let uu____60737 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____60737)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____60752 .
    FStar_TypeChecker_Env.env ->
      'Auu____60752 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____60778 = err_msg_comp_strings env c c'  in
          match uu____60778 with
          | (s1,s2) ->
              let uu____60796 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____60796)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____60816 =
        let uu____60818 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____60818
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____60816)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____60842 =
        let uu____60844 = FStar_Syntax_Print.term_to_string e  in
        let uu____60846 =
          let uu____60848 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____60848  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____60844 uu____60846
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____60842)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____60889 =
        let uu____60891 = FStar_Syntax_Print.term_to_string e  in
        let uu____60893 =
          let uu____60895 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____60895  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____60891 uu____60893
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____60889)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____60932 =
        let uu____60934 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____60936 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____60934 uu____60936
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____60932)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____60962 =
        let uu____60964 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____60966 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____60964 uu____60966
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____60962)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____60997 ->
          let uu____61001 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____61001
       in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
  
let (top_level_effect : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
  
let (cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun a  ->
      let uu____61038 =
        let uu____61040 = FStar_Syntax_Print.lid_to_string l  in
        let uu____61042 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____61040 uu____61042
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____61038)
  