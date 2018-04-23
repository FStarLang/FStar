open Prims
let info_at_pos :
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
          let uu____33 =
            let uu____36 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____36 file row col  in
          match uu____33 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____96 =
                     let uu____107 =
                       let uu____112 = FStar_Syntax_Print.nm_to_string bv  in
                       FStar_Util.Inl uu____112  in
                     let uu____113 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____107,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____113)
                      in
                   FStar_Pervasives_Native.Some uu____96
               | FStar_Util.Inr fv ->
                   let uu____129 =
                     let uu____140 =
                       let uu____145 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____145  in
                     let uu____146 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____140,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____146)
                      in
                   FStar_Pervasives_Native.Some uu____129)
  
let add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list -> unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____229  ->
                match uu____229 with
                | (e,msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____251 = FStar_TypeChecker_Env.get_range env  in
                      (e, msg, uu____251)
                    else
                      (let r' =
                         let uu____254 = FStar_Range.use_range r  in
                         FStar_Range.set_def_range r uu____254  in
                       let uu____255 =
                         let uu____256 = FStar_Range.file_of_range r'  in
                         let uu____257 =
                           let uu____258 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____258  in
                         uu____256 <> uu____257  in
                       if uu____255
                       then
                         let uu____265 =
                           let uu____266 =
                             let uu____267 =
                               let uu____268 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.strcat uu____268 ")"  in
                             Prims.strcat "(Also see: " uu____267  in
                           Prims.strcat msg uu____266  in
                         let uu____269 = FStar_TypeChecker_Env.get_range env
                            in
                         (e, uu____265, uu____269)
                       else (e, msg, r))))
         in
      FStar_Errors.add_errors errs1
  
let err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____308  ->
               (let uu____310 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____311 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____312 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____311, uu____312)))
        else (s1, s2)
  
let exhaustiveness_check : Prims.string = "Patterns are incomplete" 
let subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun x  ->
          let uu____334 = err_msg_type_strings env t1 t2  in
          match uu____334 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
  
let ill_kinded_type : Prims.string = "Ill-kinded type" 
let totality_check : Prims.string = "This term may not terminate" 
let unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____360 =
          let uu____361 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____361
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____360)
  
let expected_a_term_of_type_t_got_a_function :
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
          let uu____386 =
            let uu____387 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____388 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____387 uu____388 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____386)
  
let unexpected_implicit_argument :
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
  
let expected_expression_of_type :
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
          let uu____417 = err_msg_type_strings env t1 t2  in
          match uu____417 with
          | (s1,s2) ->
              let uu____428 =
                let uu____429 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____429 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____428)
  
let expected_pattern_of_type :
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
          let uu____454 = err_msg_type_strings env t1 t2  in
          match uu____454 with
          | (s1,s2) ->
              let uu____465 =
                let uu____466 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____466 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____465)
  
let basic_type_error :
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
          let uu____495 = err_msg_type_strings env t1 t2  in
          match uu____495 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____508 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____508 s2
                 in
              (FStar_Errors.Error_TypeError, msg)
  
let occurs_check :
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
  
let incompatible_kinds :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun k1  ->
      fun k2  ->
        let uu____532 =
          let uu____533 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____534 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
            uu____533 uu____534
           in
        (FStar_Errors.Fatal_IncompatibleKinds, uu____532)
  
let constructor_builds_the_wrong_type :
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
          let uu____559 =
            let uu____560 = FStar_Syntax_Print.term_to_string d  in
            let uu____561 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____562 = FStar_TypeChecker_Normalize.term_to_string env t'
               in
            FStar_Util.format3
              "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
              uu____560 uu____561 uu____562
             in
          (FStar_Errors.Fatal_ConstsructorBuildWrongType, uu____559)
  
let constructor_fails_the_positivity_check :
  'Auu____571 .
    'Auu____571 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid ->
          (FStar_Errors.raw_error,Prims.string)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____591 =
          let uu____592 = FStar_Syntax_Print.term_to_string d  in
          let uu____593 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____592 uu____593
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____591)
  
let inline_type_annotation_and_val_decl :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____603 =
      let uu____604 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____604
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____603)
  
let inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____624 =
          let uu____625 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____626 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____625 uu____626
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____624)
  
let expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____641 =
        let uu____642 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____642
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____641)
  
let expected_poly_typ :
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
          let uu____667 =
            let uu____668 = FStar_Syntax_Print.term_to_string f  in
            let uu____669 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____670 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____668 uu____669 uu____670
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____667)
  
let nonlinear_pattern_variable :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let m = FStar_Syntax_Print.bv_to_string x  in
    let uu____681 =
      FStar_Util.format1
        "The pattern variable \"%s\" was used more than once" m
       in
    (FStar_Errors.Fatal_NonLinearPatternVars, uu____681)
  
let disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____714 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____714 (FStar_String.concat ", ")  in
      let uu____723 =
        let uu____724 = vars v1  in
        let uu____725 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____724 uu____725
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____723)
  
let name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____748) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____760) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____772 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____772, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____785 .
    FStar_TypeChecker_Env.env ->
      'Auu____785 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error,Prims.string)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____818 = name_and_result c  in
          match uu____818 with
          | (f1,r1) ->
              let uu____835 = name_and_result c'  in
              (match uu____835 with
               | (f2,r2) ->
                   let uu____852 = err_msg_type_strings env r1 r2  in
                   (match uu____852 with
                    | (s1,s2) ->
                        let uu____863 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____863)))
  
let unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____878 =
        let uu____879 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____879
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____878)
  
let expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun c  ->
      let uu____898 =
        let uu____899 = FStar_Syntax_Print.term_to_string e  in
        let uu____900 =
          let uu____901 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____901  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____899 uu____900
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____898)
  
let expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun c  ->
      let uu____934 =
        let uu____935 = FStar_Syntax_Print.term_to_string e  in
        let uu____936 =
          let uu____937 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____937  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____935 uu____936
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____934)
  
let expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun c1  ->
    fun c2  ->
      let uu____966 =
        let uu____967 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____968 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____967 uu____968
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____966)
  
let failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun lbls  ->
      let uu____987 =
        let uu____988 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____989 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____988 uu____989
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____987)
  
let failed_to_prove_specification :
  Prims.string Prims.list ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1006 ->
          let uu____1009 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1009
       in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
  
let top_level_effect :
  (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
  
let cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun a  ->
      let uu____1034 =
        let uu____1035 = FStar_Syntax_Print.lid_to_string l  in
        let uu____1036 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1035 uu____1036
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1034)
  