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
          let uu____155 =
            let uu____161 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____161 file row col
             in
          match uu____155 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____278 =
                     let uu____298 =
                       let uu____308 = FStar_Syntax_Print.nm_to_string bv  in
                       FStar_Util.Inl uu____308  in
                     let uu____315 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____298,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____315)
                      in
                   FStar_Pervasives_Native.Some uu____278
               | FStar_Util.Inr fv ->
                   let uu____360 =
                     let uu____380 =
                       let uu____390 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____390  in
                     let uu____404 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____380,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____404)
                      in
                   FStar_Pervasives_Native.Some uu____360)
  
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
             (fun uu____621  ->
                match uu____621 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____649 = FStar_TypeChecker_Env.get_range env  in
                      (e, msg, uu____649)
                    else
                      (let r' =
                         let uu____654 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____654  in
                       let uu____655 =
                         let uu____657 = FStar_Range.file_of_range r'  in
                         let uu____659 =
                           let uu____661 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____661  in
                         uu____657 <> uu____659  in
                       if uu____655
                       then
                         let uu____671 =
                           let uu____673 =
                             let uu____675 =
                               let uu____677 =
                                 FStar_Range.string_of_use_range r  in
                               let uu____679 =
                                 let uu____681 =
                                   let uu____683 =
                                     let uu____685 = FStar_Range.use_range r
                                        in
                                     let uu____686 = FStar_Range.def_range r
                                        in
                                     uu____685 <> uu____686  in
                                   if uu____683
                                   then
                                     let uu____689 =
                                       let uu____691 =
                                         FStar_Range.string_of_def_range r
                                          in
                                       Prims.op_Hat uu____691 ")"  in
                                     Prims.op_Hat
                                       "(Other related locations: " uu____689
                                   else ""  in
                                 Prims.op_Hat ")" uu____681  in
                               Prims.op_Hat uu____677 uu____679  in
                             Prims.op_Hat " (Also see: " uu____675  in
                           Prims.op_Hat msg uu____673  in
                         let uu____700 = FStar_TypeChecker_Env.get_range env
                            in
                         (e, uu____671, uu____700)
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
            (fun uu____879  ->
               (let uu____881 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____883 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____885 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____883, uu____885)))
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
            (fun uu____1067  ->
               (let uu____1069 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____1071 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____1073 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____1071, uu____1073)))
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
          let uu____1230 = err_msg_type_strings env t1 t2  in
          match uu____1230 with
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
        let uu____1396 =
          let uu____1398 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____1398
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____1396)
  
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
          let uu____1554 =
            let uu____1556 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1558 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____1556 uu____1558 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____1554)
  
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
          let uu____1728 = err_msg_type_strings env t1 t2  in
          match uu____1728 with
          | (s1,s2) ->
              let uu____1746 =
                let uu____1748 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____1748 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____1746)
  
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
          let uu____1910 = err_msg_type_strings env t1 t2  in
          match uu____1910 with
          | (s1,s2) ->
              let uu____1928 =
                let uu____1930 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____1930 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____1928)
  
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
          let uu____2096 = err_msg_type_strings env t1 t2  in
          match uu____2096 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____2131 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____2131 s2
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
        let uu____2288 =
          let uu____2290 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____2292 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____2290 uu____2292
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____2288)
  
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
          let uu____2454 =
            let uu____2456 = FStar_Syntax_Print.term_to_string d  in
            let uu____2458 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____2460 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____2456 uu____2458 uu____2460
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____2454)
  
let constructor_fails_the_positivity_check :
  'Auu____2473 .
    'Auu____2473 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____2510 =
          let uu____2512 = FStar_Syntax_Print.term_to_string d  in
          let uu____2514 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____2512 uu____2514
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____2510)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____2537 =
      let uu____2539 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____2539
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____2537)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____2690 =
          let uu____2692 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____2694 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____2692 uu____2694
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____2690)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____2830 =
        let uu____2832 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____2832
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____2830)
  
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
          let uu____2994 =
            let uu____2996 = FStar_Syntax_Print.term_to_string f  in
            let uu____2998 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____3000 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____2996 uu____2998 uu____3000
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____2994)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____3069 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____3069 (FStar_String.concat ", ")  in
      let uu____3094 =
        let uu____3096 = vars v1  in
        let uu____3098 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____3096 uu____3098
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____3094)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____3143) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____3169) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____3200 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____3200, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____3220 .
    FStar_TypeChecker_Env.env ->
      'Auu____3220 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____3378 = name_and_result c  in
          match uu____3378 with
          | (f1,r1) ->
              let uu____3411 = name_and_result c'  in
              (match uu____3411 with
               | (f2,r2) ->
                   let uu____3444 = err_msg_type_strings env r1 r2  in
                   (match uu____3444 with
                    | (s1,s2) ->
                        let uu____3462 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____3462)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____3477 .
    FStar_TypeChecker_Env.env ->
      'Auu____3477 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____3627 = err_msg_comp_strings env c c'  in
          match uu____3627 with
          | (s1,s2) ->
              let uu____3645 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____3645)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____3781 =
        let uu____3783 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____3783
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____3781)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____3823 =
        let uu____3825 = FStar_Syntax_Print.term_to_string e  in
        let uu____3827 =
          let uu____3829 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3829  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____3825 uu____3827
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____3823)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____3898 =
        let uu____3900 = FStar_Syntax_Print.term_to_string e  in
        let uu____3902 =
          let uu____3904 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3904  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____3900 uu____3902
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____3898)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____3969 =
        let uu____3971 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____3973 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____3971 uu____3973
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____3969)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____3999 =
        let uu____4001 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____4003 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____4001 uu____4003
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____3999)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____4034 ->
          let uu____4038 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____4038
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
      let uu____4096 =
        let uu____4098 = FStar_Syntax_Print.lid_to_string l  in
        let uu____4100 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____4098 uu____4100
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____4096)
  