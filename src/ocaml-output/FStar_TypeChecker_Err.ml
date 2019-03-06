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
          let uu____60357 =
            let uu____60360 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____60360 file row col
             in
          match uu____60357 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____60419 =
                     let uu____60431 =
                       let uu____60437 = FStar_Syntax_Print.nm_to_string bv
                          in
                       FStar_Util.Inl uu____60437  in
                     let uu____60440 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____60431,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____60440)
                      in
                   FStar_Pervasives_Native.Some uu____60419
               | FStar_Util.Inr fv ->
                   let uu____60458 =
                     let uu____60470 =
                       let uu____60476 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____60476  in
                     let uu____60478 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____60470,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____60478)
                      in
                   FStar_Pervasives_Native.Some uu____60458)
  
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
             (fun uu____60571  ->
                match uu____60571 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____60599 = FStar_TypeChecker_Env.get_range env
                         in
                      (e, msg, uu____60599)
                    else
                      (let r' =
                         let uu____60604 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____60604  in
                       let uu____60605 =
                         let uu____60607 = FStar_Range.file_of_range r'  in
                         let uu____60609 =
                           let uu____60611 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____60611  in
                         uu____60607 <> uu____60609  in
                       if uu____60605
                       then
                         let uu____60621 =
                           let uu____60623 =
                             let uu____60625 =
                               let uu____60627 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.op_Hat uu____60627 ")"  in
                             Prims.op_Hat " (Also see: " uu____60625  in
                           Prims.op_Hat msg uu____60623  in
                         let uu____60631 =
                           FStar_TypeChecker_Env.get_range env  in
                         (e, uu____60621, uu____60631)
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
            (fun uu____60686  ->
               (let uu____60688 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____60690 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____60692 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____60690, uu____60692)))
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
            (fun uu____60750  ->
               (let uu____60752 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes --print_effect_args"
                   in
                ());
               (let uu____60754 =
                  FStar_TypeChecker_Normalize.comp_to_string env c1  in
                let uu____60756 =
                  FStar_TypeChecker_Normalize.comp_to_string env c2  in
                (uu____60754, uu____60756)))
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
          let uu____60789 = err_msg_type_strings env t1 t2  in
          match uu____60789 with
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
        let uu____60831 =
          let uu____60833 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____60833
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____60831)
  
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
          let uu____60865 =
            let uu____60867 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____60869 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____60867 uu____60869 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____60865)
  
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
          let uu____60907 = err_msg_type_strings env t1 t2  in
          match uu____60907 with
          | (s1,s2) ->
              let uu____60925 =
                let uu____60927 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____60927 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____60925)
  
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
          let uu____60957 = err_msg_type_strings env t1 t2  in
          match uu____60957 with
          | (s1,s2) ->
              let uu____60975 =
                let uu____60977 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____60977 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____60975)
  
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
          let uu____61011 = err_msg_type_strings env t1 t2  in
          match uu____61011 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____61034 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____61034 s2
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
        let uu____61067 =
          let uu____61069 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____61071 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____61069 uu____61071
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____61067)
  
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
          let uu____61101 =
            let uu____61103 = FStar_Syntax_Print.term_to_string d  in
            let uu____61105 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____61107 =
              FStar_TypeChecker_Normalize.term_to_string env t'  in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____61103 uu____61105 uu____61107
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____61101)
  
let constructor_fails_the_positivity_check :
  'Auu____61120 .
    'Auu____61120 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____61141 =
          let uu____61143 = FStar_Syntax_Print.term_to_string d  in
          let uu____61145 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____61143 uu____61145
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____61141)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____61160 =
      let uu____61162 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____61162
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____61160)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____61187 =
          let uu____61189 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____61191 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____61189 uu____61191
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____61187)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____61211 =
        let uu____61213 = FStar_TypeChecker_Normalize.term_to_string env t
           in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____61213
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____61211)
  
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
          let uu____61243 =
            let uu____61245 = FStar_Syntax_Print.term_to_string f  in
            let uu____61247 =
              FStar_TypeChecker_Normalize.term_to_string env t  in
            let uu____61249 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____61245 uu____61247 uu____61249
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____61243)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____61288 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____61288 (FStar_String.concat ", ")  in
      let uu____61303 =
        let uu____61305 = vars v1  in
        let uu____61307 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____61305 uu____61307
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____61303)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____61336) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____61350) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____61364 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____61364, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____61380 .
    FStar_TypeChecker_Env.env ->
      'Auu____61380 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____61414 = name_and_result c  in
          match uu____61414 with
          | (f1,r1) ->
              let uu____61435 = name_and_result c'  in
              (match uu____61435 with
               | (f2,r2) ->
                   let uu____61456 = err_msg_type_strings env r1 r2  in
                   (match uu____61456 with
                    | (s1,s2) ->
                        let uu____61474 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____61474)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____61489 .
    FStar_TypeChecker_Env.env ->
      'Auu____61489 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____61515 = err_msg_comp_strings env c c'  in
          match uu____61515 with
          | (s1,s2) ->
              let uu____61533 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                uu____61533)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____61553 =
        let uu____61555 = FStar_TypeChecker_Normalize.term_to_string env f
           in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____61555
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____61553)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____61579 =
        let uu____61581 = FStar_Syntax_Print.term_to_string e  in
        let uu____61583 =
          let uu____61585 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____61585  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____61581 uu____61583
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____61579)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____61626 =
        let uu____61628 = FStar_Syntax_Print.term_to_string e  in
        let uu____61630 =
          let uu____61632 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____61632  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____61628 uu____61630
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____61626)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____61669 =
        let uu____61671 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____61673 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____61671 uu____61673
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____61669)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____61699 =
        let uu____61701 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____61703 =
          FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____61701 uu____61703
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____61699)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____61734 ->
          let uu____61738 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____61738
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
      let uu____61775 =
        let uu____61777 = FStar_Syntax_Print.lid_to_string l  in
        let uu____61779 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____61777 uu____61779
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____61775)
  