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
          let uu____64444 =
            let uu____64447 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____64447 file row col
             in
          match uu____64444 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____64506 =
                     let uu____64518 =
                       let uu____64524 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____64524  in
                     let uu____64527 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____64518,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64527)
                      in
                   FStar_Pervasives_Native.Some uu____64506
               | FStar_Util.Inr fv ->
                   let uu____64545 =
                     let uu____64557 =
                       let uu____64563 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____64563  in
                     let uu____64565 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____64557,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64565)
                      in
                   FStar_Pervasives_Native.Some uu____64545)
  
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
             (fun uu____64658  ->
                match uu____64658 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____64686 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____64686)
                    else
                      (let r' =
                         let uu____64691 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____64691  in
                       let uu____64692 =
                         let uu____64694 = FStar_Range.file_of_range r'  in
                         let uu____64696 =
                           let uu____64698 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____64698  in
                         uu____64694 <> uu____64696  in
                       if uu____64692
                       then
                         let uu____64708 =
                           let uu____64710 =
                             let uu____64712 =
                               let uu____64714 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____64714 ")"  in
                             Prims.op_Hat " (Also see: " uu____64712  in
                           Prims.op_Hat msg uu____64710  in
                         let uu____64718 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____64708, uu____64718)
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
            (fun uu____64773  ->
               (let uu____64775 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____64777 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____64779 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____64777, uu____64779)))
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
            (fun uu____64837  ->
               (let uu____64839 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____64841 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____64843 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____64841, uu____64843)))
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
          let uu____64876 = err_msg_type_strings env t1 t2  in
          match uu____64876 with
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
        let uu____64918 =
          let uu____64920 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____64920
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____64918)
  
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
          let uu____64952 =
            let uu____64954 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____64956 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____64954 uu____64956 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____64952)
  
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
          let uu____64994 = err_msg_type_strings env t1 t2  in
          match uu____64994 with
          | (s1,s2) ->
              let uu____65012 =
                let uu____65014 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____65014 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____65012)
  
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
          let uu____65044 = err_msg_type_strings env t1 t2  in
          match uu____65044 with
          | (s1,s2) ->
              let uu____65062 =
                let uu____65064 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____65064 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____65062)
  
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
          let uu____65098 = err_msg_type_strings env t1 t2  in
          match uu____65098 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____65121 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____65121 s2
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
        let uu____65154 =
          let uu____65156 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____65158 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____65156 uu____65158
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____65154)
  
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
          let uu____65188 =
            let uu____65190 = FStar_Syntax_Print.term_to_string d  in
            let uu____65192 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65194 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____65190 uu____65192 uu____65194
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____65188)
  
let constructor_fails_the_positivity_check :
  'Auu____65207 .
    'Auu____65207 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____65228 =
          let uu____65230 = FStar_Syntax_Print.term_to_string d  in
          let uu____65232 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____65230 uu____65232
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____65228)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65247 =
      let uu____65249 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____65249
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____65247)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____65274 =
          let uu____65276 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____65278 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____65276 uu____65278
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____65274)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____65298 =
        let uu____65300 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____65300
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____65298)
  
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
          let uu____65330 =
            let uu____65332 = FStar_Syntax_Print.term_to_string f  in
            let uu____65334 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65336 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____65332 uu____65334 uu____65336
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____65330)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____65375 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____65375 (FStar_String.concat ", ")  in
      let uu____65390 =
        let uu____65392 = vars v1  in
        let uu____65394 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____65392 uu____65394
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____65390)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65423) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____65437) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____65451 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____65451, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____65467 .
    FStar_TypeChecker_Env.env ->
      'Auu____65467 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65501 = name_and_result c  in
          match uu____65501 with
          | (f1,r1) ->
              let uu____65522 = name_and_result c'  in
              (match uu____65522 with
               | (f2,r2) ->
                   let uu____65543 = err_msg_type_strings env r1 r2  in
                   (match uu____65543 with
                    | (s1,s2) ->
                        let uu____65561 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____65561)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____65576 .
    FStar_TypeChecker_Env.env ->
      'Auu____65576 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65602 = err_msg_comp_strings env c c'  in
          match uu____65602 with
          | (s1,s2) ->
              let uu____65620 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____65620)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____65640 =
        let uu____65642 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____65642
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____65640)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65666 =
        let uu____65668 = FStar_Syntax_Print.term_to_string e  in
        let uu____65670 =
          let uu____65672 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65672  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____65668 uu____65670
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____65666)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65713 =
        let uu____65715 = FStar_Syntax_Print.term_to_string e  in
        let uu____65717 =
          let uu____65719 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65719  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____65715 uu____65717
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____65713)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____65756 =
        let uu____65758 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____65760 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____65758 uu____65760
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____65756)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____65786 =
        let uu____65788 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____65790 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____65788 uu____65790
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____65786)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____65821 ->
          let uu____65825 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____65825
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
      let uu____65862 =
        let uu____65864 = FStar_Syntax_Print.lid_to_string l  in
        let uu____65866 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____65864 uu____65866
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____65862)
  