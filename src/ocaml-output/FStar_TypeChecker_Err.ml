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
          let uu____64375 =
            let uu____64378 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____64378 file row col
             in
          match uu____64375 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____64437 =
                     let uu____64449 =
                       let uu____64455 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____64455  in
                     let uu____64458 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____64449,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64458)
                      in
                   FStar_Pervasives_Native.Some uu____64437
               | FStar_Util.Inr fv ->
                   let uu____64476 =
                     let uu____64488 =
                       let uu____64494 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____64494  in
                     let uu____64496 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____64488,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____64496)
                      in
                   FStar_Pervasives_Native.Some uu____64476)
  
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
             (fun uu____64589  ->
                match uu____64589 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____64617 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____64617)
                    else
                      (let r' =
                         let uu____64622 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____64622  in
                       let uu____64623 =
                         let uu____64625 = FStar_Range.file_of_range r'  in
                         let uu____64627 =
                           let uu____64629 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____64629  in
                         uu____64625 <> uu____64627  in
                       if uu____64623
                       then
                         let uu____64639 =
                           let uu____64641 =
                             let uu____64643 =
                               let uu____64645 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____64645 ")"  in
                             Prims.op_Hat " (Also see: " uu____64643  in
                           Prims.op_Hat msg uu____64641  in
                         let uu____64649 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____64639, uu____64649)
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
            (fun uu____64704  ->
               (let uu____64706 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____64708 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____64710 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____64708, uu____64710)))
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
            (fun uu____64768  ->
               (let uu____64770 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____64772 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____64774 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____64772, uu____64774)))
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
          let uu____64807 = err_msg_type_strings env t1 t2  in
          match uu____64807 with
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
        let uu____64849 =
          let uu____64851 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____64851
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____64849)
  
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
          let uu____64883 =
            let uu____64885 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____64887 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____64885 uu____64887 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____64883)
  
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
          let uu____64925 = err_msg_type_strings env t1 t2  in
          match uu____64925 with
          | (s1,s2) ->
              let uu____64943 =
                let uu____64945 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____64945 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____64943)
  
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
          let uu____64975 = err_msg_type_strings env t1 t2  in
          match uu____64975 with
          | (s1,s2) ->
              let uu____64993 =
                let uu____64995 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____64995 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____64993)
  
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
          let uu____65029 = err_msg_type_strings env t1 t2  in
          match uu____65029 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____65052 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____65052 s2
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
        let uu____65085 =
          let uu____65087 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____65089 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____65087 uu____65089
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____65085)
  
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
          let uu____65119 =
            let uu____65121 = FStar_Syntax_Print.term_to_string d  in
            let uu____65123 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65125 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____65121 uu____65123 uu____65125
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____65119)
  
let constructor_fails_the_positivity_check :
  'Auu____65138 .
    'Auu____65138 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____65159 =
          let uu____65161 = FStar_Syntax_Print.term_to_string d  in
          let uu____65163 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____65161 uu____65163
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____65159)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____65178 =
      let uu____65180 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____65180
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____65178)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____65205 =
          let uu____65207 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____65209 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____65207 uu____65209
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____65205)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____65229 =
        let uu____65231 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____65231
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____65229)
  
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
          let uu____65261 =
            let uu____65263 = FStar_Syntax_Print.term_to_string f  in
            let uu____65265 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____65267 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____65263 uu____65265 uu____65267
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____65261)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____65306 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____65306 (FStar_String.concat ", ")  in
      let uu____65321 =
        let uu____65323 = vars v1  in
        let uu____65325 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____65323 uu____65325
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____65321)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65354) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____65368) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____65382 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____65382, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____65398 .
    FStar_TypeChecker_Env.env ->
      'Auu____65398 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65432 = name_and_result c  in
          match uu____65432 with
          | (f1,r1) ->
              let uu____65453 = name_and_result c'  in
              (match uu____65453 with
               | (f2,r2) ->
                   let uu____65474 = err_msg_type_strings env r1 r2  in
                   (match uu____65474 with
                    | (s1,s2) ->
                        let uu____65492 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____65492)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____65507 .
    FStar_TypeChecker_Env.env ->
      'Auu____65507 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____65533 = err_msg_comp_strings env c c'  in
          match uu____65533 with
          | (s1,s2) ->
              let uu____65551 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____65551)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____65571 =
        let uu____65573 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____65573
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____65571)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65597 =
        let uu____65599 = FStar_Syntax_Print.term_to_string e  in
        let uu____65601 =
          let uu____65603 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65603  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____65599 uu____65601
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____65597)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____65644 =
        let uu____65646 = FStar_Syntax_Print.term_to_string e  in
        let uu____65648 =
          let uu____65650 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____65650  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____65646 uu____65648
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____65644)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____65687 =
        let uu____65689 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____65691 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____65689 uu____65691
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____65687)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____65717 =
        let uu____65719 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____65721 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____65719 uu____65721
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____65717)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____65752 ->
          let uu____65756 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____65756
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
      let uu____65793 =
        let uu____65795 = FStar_Syntax_Print.lid_to_string l  in
        let uu____65797 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____65795 uu____65797
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____65793)
  