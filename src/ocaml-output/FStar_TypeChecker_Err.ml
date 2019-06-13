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
          let uu____39 =
            let uu____42 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____42 file row col  in
          match uu____39 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____101 =
                     let uu____113 =
                       let uu____119 = FStar_Syntax_Print.nm_to_string bv  in
                       FStar_Util.Inl uu____119  in
                     let uu____122 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____113,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____122)
                      in
                   FStar_Pervasives_Native.Some uu____101
               | FStar_Util.Inr fv ->
                   let uu____140 =
                     let uu____152 =
                       let uu____158 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____158  in
                     let uu____160 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____152,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____160)
                      in
                   FStar_Pervasives_Native.Some uu____140)
  
let (add_errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      Prims.string FStar_Pervasives_Native.option -> unit)
  =
  fun env  ->
    fun errs  ->
      fun smt_detail  ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Pervasives_Native.None  -> msg
          | FStar_Pervasives_Native.Some d ->
              Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
           in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu____282  ->
                  match uu____282 with
                  | (e,msg,r) ->
                      let uu____302 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu____318 = FStar_TypeChecker_Env.get_range env
                             in
                          (e, msg, uu____318)
                        else
                          (let r' =
                             let uu____323 = FStar_Range.use_range r  in
                             FStar_Range.set_def_range r uu____323  in
                           let uu____324 =
                             let uu____326 = FStar_Range.file_of_range r'  in
                             let uu____328 =
                               let uu____330 =
                                 FStar_TypeChecker_Env.get_range env  in
                               FStar_Range.file_of_range uu____330  in
                             uu____326 <> uu____328  in
                           if uu____324
                           then
                             let uu____340 =
                               let uu____342 =
                                 let uu____344 =
                                   let uu____346 =
                                     FStar_Range.string_of_use_range r  in
                                   let uu____348 =
                                     let uu____350 =
                                       let uu____352 =
                                         let uu____354 =
                                           FStar_Range.use_range r  in
                                         let uu____355 =
                                           FStar_Range.def_range r  in
                                         uu____354 <> uu____355  in
                                       if uu____352
                                       then
                                         let uu____358 =
                                           let uu____360 =
                                             FStar_Range.string_of_def_range
                                               r
                                              in
                                           Prims.op_Hat uu____360 ")"  in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu____358
                                       else ""  in
                                     Prims.op_Hat ")" uu____350  in
                                   Prims.op_Hat uu____346 uu____348  in
                                 Prims.op_Hat " (Also see: " uu____344  in
                               Prims.op_Hat msg uu____342  in
                             let uu____369 =
                               FStar_TypeChecker_Env.get_range env  in
                             (e, uu____340, uu____369)
                           else (e, msg, r))
                         in
                      (match uu____302 with
                       | (e1,msg1,r1) ->
                           (e1, (maybe_add_smt_detail msg1), r1))))
           in
        FStar_Errors.add_errors errs1
  
let (add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      unit)
  =
  fun env  ->
    fun errs  -> add_errors_smt_detail env errs FStar_Pervasives_Native.None
  
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
            (fun uu____467  ->
               (let uu____469 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____471 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____473 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____471, uu____473)))
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
            (fun uu____531  ->
               (let uu____533 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____535 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____537 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____535, uu____537)))
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
          let uu____570 = err_msg_type_strings env t1 t2  in
          match uu____570 with
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
        let uu____612 =
          let uu____614 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____614
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____612)
  
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
          let uu____646 =
            let uu____648 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____650 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____648 uu____650 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____646)
  
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
          let uu____688 = err_msg_type_strings env t1 t2  in
          match uu____688 with
          | (s1,s2) ->
              let uu____706 =
                let uu____708 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____708 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____706)
  
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
          let uu____738 = err_msg_type_strings env t1 t2  in
          match uu____738 with
          | (s1,s2) ->
              let uu____756 =
                let uu____758 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____758 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____756)
  
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
          let uu____792 = err_msg_type_strings env t1 t2  in
          match uu____792 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____815 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____815 s2
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
        let uu____848 =
          let uu____850 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____852 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____850 uu____852
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____848)
  
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
          let uu____882 =
            let uu____884 = FStar_Syntax_Print.term_to_string d  in
            let uu____886 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____888 = FStar_TypeChecker_Normalize.term_to_string env t'
               in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____884 uu____886 uu____888
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____882)
  
let constructor_fails_the_positivity_check :
  'Auu____901 .
    'Auu____901 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____922 =
          let uu____924 = FStar_Syntax_Print.term_to_string d  in
          let uu____926 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____924 uu____926
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____922)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____941 =
      let uu____943 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____943
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____941)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____968 =
          let uu____970 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____972 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____970 uu____972
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____968)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____992 =
        let uu____994 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____994
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____992)
  
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
          let uu____1024 =
            let uu____1026 = FStar_Syntax_Print.term_to_string f  in
            let uu____1028 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1030 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____1026 uu____1028 uu____1030
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____1024)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____1069 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____1069 (FStar_String.concat ", ")  in
      let uu____1084 =
        let uu____1086 = vars v1  in
        let uu____1088 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____1086 uu____1088
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____1084)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1117) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____1131) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____1145 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____1145, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____1161 .
    FStar_TypeChecker_Env.env ->
      'Auu____1161 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1195 = name_and_result c  in
          match uu____1195 with
          | (f1,r1) ->
              let uu____1216 = name_and_result c'  in
              (match uu____1216 with
               | (f2,r2) ->
                   let uu____1237 = err_msg_type_strings env r1 r2  in
                   (match uu____1237 with
                    | (s1,s2) ->
                        let uu____1255 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1255)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____1270 .
    FStar_TypeChecker_Env.env ->
      'Auu____1270 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1296 = err_msg_comp_strings env c c'  in
          match uu____1296 with
          | (s1,s2) ->
              let uu____1314 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1314)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____1334 =
        let uu____1336 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1336
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1334)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1360 =
        let uu____1362 = FStar_Syntax_Print.term_to_string e  in
        let uu____1364 =
          let uu____1366 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1366  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____1362 uu____1364
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____1360)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1407 =
        let uu____1409 = FStar_Syntax_Print.term_to_string e  in
        let uu____1411 =
          let uu____1413 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1413  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1409 uu____1411
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1407)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____1450 =
        let uu____1452 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____1454 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1452 uu____1454
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1450)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____1480 =
        let uu____1482 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____1484 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1482 uu____1484
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1480)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1515 ->
          let uu____1519 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1519
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
      let uu____1556 =
        let uu____1558 = FStar_Syntax_Print.lid_to_string l  in
        let uu____1560 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1558 uu____1560
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1556)
  