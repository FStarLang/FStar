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
          let uu____64380 =
            let uu____64383 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____64383 file row col
             in
          match uu____64380 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____64442 =
                     let uu____64454 =
                       let uu____64460 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____64460  in
                     let uu____64463 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____64454,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64463)
                      in
                   FStar_Pervasives_Native.Some uu____64442
               | FStar_Util.Inr fv ->
                   let uu____64481 =
                     let uu____64493 =
                       let uu____64499 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____64499  in
                     let uu____64501 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____64493,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64501)
                      in
                   FStar_Pervasives_Native.Some uu____64481)
  
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
             (fun uu____64594  ->
                match uu____64594 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____64622 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____64622)
                    else
                      (let r' =
                         let uu____64627 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____64627  in
                       let uu____64628 =
                         let uu____64630 = FStar_Range.file_of_range r'  in
                         let uu____64632 =
                           let uu____64634 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____64634  in
                         uu____64630 <> uu____64632  in
                       if uu____64628
                       then
                         let uu____64644 =
                           let uu____64646 =
                             let uu____64648 =
                               let uu____64650 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____64650 ")"  in
                             Prims.op_Hat " (Also see: " uu____64648  in
                           Prims.op_Hat msg uu____64646  in
                         let uu____64654 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____64644, uu____64654)
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
            (fun uu____64709  ->
               (let uu____64711 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____64713 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____64715 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____64713, uu____64715)))
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
            (fun uu____64773  ->
               (let uu____64775 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____64777 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____64779 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____64777, uu____64779)))
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
          let uu____64812 = err_msg_type_strings env t1 t2  in
          match uu____64812 with
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
        let uu____64854 =
          let uu____64856 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____64856
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____64854)
  
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
          let uu____64888 =
            let uu____64890 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____64892 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____64890 uu____64892 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____64888)
  
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
          let uu____64930 = err_msg_type_strings env t1 t2  in
          match uu____64930 with
          | (s1,s2) ->
              let uu____64948 =
                let uu____64950 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____64950 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____64948)
  
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
          let uu____64980 = err_msg_type_strings env t1 t2  in
          match uu____64980 with
          | (s1,s2) ->
              let uu____64998 =
                let uu____65000 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____65000 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____64998)
  
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
          let uu____65034 = err_msg_type_strings env t1 t2  in
          match uu____65034 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____65057 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____65057 s2
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
        let uu____65090 =
          let uu____65092 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____65094 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____65092 uu____65094
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____65090)
  
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
          let uu____65124 =
            let uu____65126 = FStar_Syntax_Print.term_to_string d  in
            let uu____65128 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65130 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____65126 uu____65128 uu____65130
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____65124)
  
let constructor_fails_the_positivity_check :
  'Auu____65143 .
    'Auu____65143 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____65164 =
          let uu____65166 = FStar_Syntax_Print.term_to_string d  in
          let uu____65168 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____65166 uu____65168
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____65164)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65183 =
      let uu____65185 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____65185
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____65183)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____65210 =
          let uu____65212 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____65214 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____65212 uu____65214
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____65210)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____65234 =
        let uu____65236 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____65236
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____65234)
  
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
          let uu____65266 =
            let uu____65268 = FStar_Syntax_Print.term_to_string f  in
            let uu____65270 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65272 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____65268 uu____65270 uu____65272
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____65266)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____65311 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____65311 (FStar_String.concat ", ")  in
      let uu____65326 =
        let uu____65328 = vars v1  in
        let uu____65330 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____65328 uu____65330
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____65326)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65359) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____65373) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____65387 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____65387, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____65403 .
    FStar_TypeChecker_Env.env ->
      'Auu____65403 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65437 = name_and_result c  in
          match uu____65437 with
          | (f1,r1) ->
              let uu____65458 = name_and_result c'  in
              (match uu____65458 with
               | (f2,r2) ->
                   let uu____65479 = err_msg_type_strings env r1 r2  in
                   (match uu____65479 with
                    | (s1,s2) ->
                        let uu____65497 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____65497)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____65512 .
    FStar_TypeChecker_Env.env ->
      'Auu____65512 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65538 = err_msg_comp_strings env c c'  in
          match uu____65538 with
          | (s1,s2) ->
              let uu____65556 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____65556)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____65576 =
        let uu____65578 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____65578
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____65576)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65602 =
        let uu____65604 = FStar_Syntax_Print.term_to_string e  in
        let uu____65606 =
          let uu____65608 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65608  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____65604 uu____65606
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____65602)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65649 =
        let uu____65651 = FStar_Syntax_Print.term_to_string e  in
        let uu____65653 =
          let uu____65655 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65655  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____65651 uu____65653
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____65649)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____65692 =
        let uu____65694 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____65696 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____65694 uu____65696
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____65692)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____65722 =
        let uu____65724 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____65726 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____65724 uu____65726
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____65722)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____65757 ->
          let uu____65761 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____65761
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
      let uu____65798 =
        let uu____65800 = FStar_Syntax_Print.lid_to_string l  in
        let uu____65802 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____65800 uu____65802
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____65798)
  