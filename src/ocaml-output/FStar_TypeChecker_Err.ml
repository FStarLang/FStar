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
      (Prims.string,Prims.string) FStar_Util.either -> unit)
  =
  fun env  ->
    fun errs  ->
      fun smt_detail  ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Util.Inr d -> Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
          | FStar_Util.Inl d when (FStar_Util.trim_string d) <> "" ->
              Prims.op_Hat msg (Prims.op_Hat "; " d)
          | uu____245 -> msg  in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu____302  ->
                  match uu____302 with
                  | (e,msg,r) ->
                      let uu____322 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu____338 = FStar_TypeChecker_Env.get_range env
                             in
                          (e, msg, uu____338)
                        else
                          (let r' =
                             let uu____343 = FStar_Range.use_range r  in
                             FStar_Range.set_def_range r uu____343  in
                           let uu____344 =
                             let uu____346 = FStar_Range.file_of_range r'  in
                             let uu____348 =
                               let uu____350 =
                                 FStar_TypeChecker_Env.get_range env  in
                               FStar_Range.file_of_range uu____350  in
                             uu____346 <> uu____348  in
                           if uu____344
                           then
                             let uu____360 =
                               let uu____362 =
                                 let uu____364 =
                                   let uu____366 =
                                     FStar_Range.string_of_use_range r  in
                                   let uu____368 =
                                     let uu____370 =
                                       let uu____372 =
                                         let uu____374 =
                                           FStar_Range.use_range r  in
                                         let uu____375 =
                                           FStar_Range.def_range r  in
                                         uu____374 <> uu____375  in
                                       if uu____372
                                       then
                                         let uu____378 =
                                           let uu____380 =
                                             FStar_Range.string_of_def_range
                                               r
                                              in
                                           Prims.op_Hat uu____380 ")"  in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu____378
                                       else ""  in
                                     Prims.op_Hat ")" uu____370  in
                                   Prims.op_Hat uu____366 uu____368  in
                                 Prims.op_Hat " (Also see: " uu____364  in
                               Prims.op_Hat msg uu____362  in
                             let uu____389 =
                               FStar_TypeChecker_Env.get_range env  in
                             (e, uu____360, uu____389)
                           else (e, msg, r))
                         in
                      (match uu____322 with
                       | (e1,msg1,r1) ->
                           (e1, (maybe_add_smt_detail msg1), r1))))
           in
        FStar_Errors.add_errors errs1
  
let (add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      unit)
  =
  fun env  -> fun errs  -> add_errors_smt_detail env errs (FStar_Util.Inl "") 
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
            (fun uu____489  ->
               (let uu____491 =
                  FStar_Options.set_options
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____493 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____495 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____493, uu____495)))
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
            (fun uu____553  ->
               (let uu____555 =
                  FStar_Options.set_options
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____557 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____559 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____557, uu____559)))
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
          let uu____592 = err_msg_type_strings env t1 t2  in
          match uu____592 with
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
        let uu____634 =
          let uu____636 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____636
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____634)
  
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
          let uu____668 =
            let uu____670 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____672 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____670 uu____672 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____668)
  
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
          let uu____710 = err_msg_type_strings env t1 t2  in
          match uu____710 with
          | (s1,s2) ->
              let uu____728 =
                let uu____730 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____730 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____728)
  
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
          let uu____760 = err_msg_type_strings env t1 t2  in
          match uu____760 with
          | (s1,s2) ->
              let uu____778 =
                let uu____780 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____780 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____778)
  
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
          let uu____814 = err_msg_type_strings env t1 t2  in
          match uu____814 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____837 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____837 s2
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
        let uu____870 =
          let uu____872 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____874 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____872 uu____874
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____870)
  
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
          let uu____904 =
            let uu____906 = FStar_Syntax_Print.term_to_string d  in
            let uu____908 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____910 = FStar_TypeChecker_Normalize.term_to_string env t'
               in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____906 uu____908 uu____910
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____904)
  
let constructor_fails_the_positivity_check :
  'Auu____923 .
    'Auu____923 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____944 =
          let uu____946 = FStar_Syntax_Print.term_to_string d  in
          let uu____948 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____946 uu____948
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____944)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____963 =
      let uu____965 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____965
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____963)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____990 =
          let uu____992 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____994 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____992 uu____994
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____990)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____1014 =
        let uu____1016 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____1016
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____1014)
  
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
          let uu____1046 =
            let uu____1048 = FStar_Syntax_Print.term_to_string f  in
            let uu____1050 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1052 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____1048 uu____1050 uu____1052
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____1046)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____1091 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____1091 (FStar_String.concat ", ")  in
      let uu____1106 =
        let uu____1108 = vars v1  in
        let uu____1110 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____1108 uu____1110
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____1106)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1139) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____1153) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____1167 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____1167, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____1183 .
    FStar_TypeChecker_Env.env ->
      'Auu____1183 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1217 = name_and_result c  in
          match uu____1217 with
          | (f1,r1) ->
              let uu____1238 = name_and_result c'  in
              (match uu____1238 with
               | (f2,r2) ->
                   let uu____1259 = err_msg_type_strings env r1 r2  in
                   (match uu____1259 with
                    | (s1,s2) ->
                        let uu____1277 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1277)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____1292 .
    FStar_TypeChecker_Env.env ->
      'Auu____1292 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1318 = err_msg_comp_strings env c c'  in
          match uu____1318 with
          | (s1,s2) ->
              let uu____1336 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1336)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____1356 =
        let uu____1358 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1358
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1356)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1382 =
        let uu____1384 = FStar_Syntax_Print.term_to_string e  in
        let uu____1386 =
          let uu____1388 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1388  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____1384 uu____1386
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____1382)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1429 =
        let uu____1431 = FStar_Syntax_Print.term_to_string e  in
        let uu____1433 =
          let uu____1435 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1435  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1431 uu____1433
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1429)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____1472 =
        let uu____1474 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____1476 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1474 uu____1476
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1472)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____1502 =
        let uu____1504 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____1506 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1504 uu____1506
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1502)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1537 ->
          let uu____1541 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1541
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
      let uu____1578 =
        let uu____1580 = FStar_Syntax_Print.lid_to_string l  in
        let uu____1582 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1580 uu____1582
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1578)
  