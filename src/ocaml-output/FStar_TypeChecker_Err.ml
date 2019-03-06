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
          let uu____64472 =
            let uu____64475 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____64475 file row col
             in
          match uu____64472 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____64534 =
                     let uu____64546 =
                       let uu____64552 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____64552  in
                     let uu____64555 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____64546,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64555)
                      in
                   FStar_Pervasives_Native.Some uu____64534
               | FStar_Util.Inr fv ->
                   let uu____64573 =
                     let uu____64585 =
                       let uu____64591 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____64591  in
                     let uu____64593 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____64585,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64593)
                      in
                   FStar_Pervasives_Native.Some uu____64573)
  
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
             (fun uu____64686  ->
                match uu____64686 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____64714 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____64714)
                    else
                      (let r' =
                         let uu____64719 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____64719  in
                       let uu____64720 =
                         let uu____64722 = FStar_Range.file_of_range r'  in
                         let uu____64724 =
                           let uu____64726 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____64726  in
                         uu____64722 <> uu____64724  in
                       if uu____64720
                       then
                         let uu____64736 =
                           let uu____64738 =
                             let uu____64740 =
                               let uu____64742 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____64742 ")"  in
                             Prims.op_Hat " (Also see: " uu____64740  in
                           Prims.op_Hat msg uu____64738  in
                         let uu____64746 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____64736, uu____64746)
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
            (fun uu____64801  ->
               (let uu____64803 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____64805 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____64807 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____64805, uu____64807)))
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
            (fun uu____64865  ->
               (let uu____64867 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____64869 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____64871 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____64869, uu____64871)))
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
          let uu____64904 = err_msg_type_strings env t1 t2  in
          match uu____64904 with
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
        let uu____64946 =
          let uu____64948 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____64948
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____64946)
  
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
          let uu____64980 =
            let uu____64982 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____64984 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____64982 uu____64984 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____64980)
  
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
          let uu____65022 = err_msg_type_strings env t1 t2  in
          match uu____65022 with
          | (s1,s2) ->
              let uu____65040 =
                let uu____65042 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____65042 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____65040)
  
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
          let uu____65072 = err_msg_type_strings env t1 t2  in
          match uu____65072 with
          | (s1,s2) ->
              let uu____65090 =
                let uu____65092 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____65092 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____65090)
  
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
          let uu____65126 = err_msg_type_strings env t1 t2  in
          match uu____65126 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____65149 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____65149 s2
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
        let uu____65182 =
          let uu____65184 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____65186 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____65184 uu____65186
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____65182)
  
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
          let uu____65216 =
            let uu____65218 = FStar_Syntax_Print.term_to_string d  in
            let uu____65220 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65222 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____65218 uu____65220 uu____65222
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____65216)
  
let constructor_fails_the_positivity_check :
  'Auu____65235 .
    'Auu____65235 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____65256 =
          let uu____65258 = FStar_Syntax_Print.term_to_string d  in
          let uu____65260 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____65258 uu____65260
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____65256)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65275 =
      let uu____65277 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____65277
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____65275)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____65302 =
          let uu____65304 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____65306 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____65304 uu____65306
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____65302)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____65326 =
        let uu____65328 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____65328
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____65326)
  
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
          let uu____65358 =
            let uu____65360 = FStar_Syntax_Print.term_to_string f  in
            let uu____65362 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65364 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____65360 uu____65362 uu____65364
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____65358)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____65403 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____65403 (FStar_String.concat ", ")  in
      let uu____65418 =
        let uu____65420 = vars v1  in
        let uu____65422 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____65420 uu____65422
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____65418)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65451) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____65465) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____65479 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____65479, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____65495 .
    FStar_TypeChecker_Env.env ->
      'Auu____65495 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65529 = name_and_result c  in
          match uu____65529 with
          | (f1,r1) ->
              let uu____65550 = name_and_result c'  in
              (match uu____65550 with
               | (f2,r2) ->
                   let uu____65571 = err_msg_type_strings env r1 r2  in
                   (match uu____65571 with
                    | (s1,s2) ->
                        let uu____65589 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____65589)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____65604 .
    FStar_TypeChecker_Env.env ->
      'Auu____65604 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65630 = err_msg_comp_strings env c c'  in
          match uu____65630 with
          | (s1,s2) ->
              let uu____65648 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____65648)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____65668 =
        let uu____65670 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____65670
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____65668)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65694 =
        let uu____65696 = FStar_Syntax_Print.term_to_string e  in
        let uu____65698 =
          let uu____65700 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65700  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____65696 uu____65698
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____65694)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65741 =
        let uu____65743 = FStar_Syntax_Print.term_to_string e  in
        let uu____65745 =
          let uu____65747 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65747  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____65743 uu____65745
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____65741)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____65784 =
        let uu____65786 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____65788 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____65786 uu____65788
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____65784)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____65814 =
        let uu____65816 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____65818 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____65816 uu____65818
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____65814)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____65849 ->
          let uu____65853 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____65853
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
      let uu____65890 =
        let uu____65892 = FStar_Syntax_Print.lid_to_string l  in
        let uu____65894 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____65892 uu____65894
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____65890)
  