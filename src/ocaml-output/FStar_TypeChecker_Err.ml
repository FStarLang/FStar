open Prims
let info_at_pos:
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
          let uu____29 =
            let uu____32 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____32 file row col in
          match uu____29 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____79 =
                     let uu____90 =
                       let uu____95 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____95 in
                     let uu____96 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____90,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____96) in
                   FStar_Pervasives_Native.Some uu____79
               | FStar_Util.Inr fv ->
                   let uu____112 =
                     let uu____123 =
                       let uu____128 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____128 in
                     let uu____129 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____123,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____129) in
                   FStar_Pervasives_Native.Some uu____112)
let add_errors:
  FStar_TypeChecker_Env.env ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____195  ->
                match uu____195 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____210 = FStar_TypeChecker_Env.get_range env in
                      (msg, uu____210)
                    else
                      (let r' =
                         let uu___251_213 = r in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___251_213.FStar_Range.use_range)
                         } in
                       let uu____214 =
                         let uu____215 = FStar_Range.file_of_range r' in
                         let uu____216 =
                           let uu____217 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____217 in
                         uu____215 <> uu____216 in
                       if uu____214
                       then
                         let uu____222 =
                           let uu____223 =
                             let uu____224 =
                               let uu____225 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____225 ")" in
                             Prims.strcat "(Also see: " uu____224 in
                           Prims.strcat msg uu____223 in
                         let uu____226 = FStar_TypeChecker_Env.get_range env in
                         (uu____222, uu____226)
                       else (msg, r)))) in
      FStar_Errors.add_errors errs1
let err_msg_type_strings:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        if s1 = s2
        then
          FStar_Options.with_saved_options
            (fun uu____262  ->
               (let uu____264 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____265 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____266 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____265, uu____266)))
        else (s1, s2)
let exhaustiveness_check: Prims.string = "Patterns are incomplete"
let subtyping_failed:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> Prims.unit -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun x  ->
          let uu____284 = err_msg_type_strings env t1 t2 in
          match uu____284 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
let ill_kinded_type: Prims.string = "Ill-kinded type"
let totality_check: Prims.string = "This term may not terminate"
let unexpected_signature_for_monad:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____303 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____303
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____320 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____321 = FStar_Syntax_Print.term_to_string e in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____320 uu____321 msg
let unexpected_implicit_argument: Prims.string =
  "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"
let expected_expression_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____338 = err_msg_type_strings env t1 t2 in
          match uu____338 with
          | (s1,s2) ->
              let uu____345 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                s1 uu____345 s2
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____360 = err_msg_type_strings env t1 t2 in
        match uu____360 with
        | (s1,s2) ->
            FStar_Util.format3
              "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
              s1 s2
let expected_pattern_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____385 = err_msg_type_strings env t1 t2 in
          match uu____385 with
          | (s1,s2) ->
              let uu____392 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                s1 uu____392 s2
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____413 = err_msg_type_strings env t1 t2 in
          match uu____413 with
          | (s1,s2) ->
              (match eopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Util.format2 "Expected type \"%s\"; got type \"%s\""
                     s1 s2
               | FStar_Pervasives_Native.Some e ->
                   let uu____421 =
                     FStar_TypeChecker_Normalize.term_to_string env e in
                   FStar_Util.format3
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                     uu____421 s2)
let occurs_check: Prims.string =
  "Possibly infinite typ (occurs check failed)"
let unification_well_formedness: Prims.string =
  "Term or type of an unexpected sort"
let incompatible_kinds:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun k2  ->
        let uu____434 = FStar_TypeChecker_Normalize.term_to_string env k1 in
        let uu____435 = FStar_TypeChecker_Normalize.term_to_string env k2 in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____434 uu____435
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____452 = FStar_Syntax_Print.term_to_string d in
          let uu____453 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____454 = FStar_TypeChecker_Normalize.term_to_string env t' in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____452 uu____453 uu____454
let constructor_fails_the_positivity_check:
  'Auu____463 .
    'Auu____463 ->
      FStar_Syntax_Syntax.term -> FStar_Ident.lid -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____476 = FStar_Syntax_Print.term_to_string d in
        let uu____477 = FStar_Syntax_Print.lid_to_string l in
        FStar_Util.format2
          "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
          uu____476 uu____477
let inline_type_annotation_and_val_decl: FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____482 = FStar_Syntax_Print.lid_to_string l in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____482
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____495 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____496 = FStar_Syntax_Print.bv_to_string x in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____495 uu____496
let expected_function_typ:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____505 = FStar_TypeChecker_Normalize.term_to_string env t in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____505
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____522 = FStar_Syntax_Print.term_to_string f in
          let uu____523 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____524 = FStar_TypeChecker_Normalize.term_to_string env targ in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____522 uu____523 uu____524
let nonlinear_pattern_variable: FStar_Syntax_Syntax.bv -> Prims.string =
  fun x  ->
    let m = FStar_Syntax_Print.bv_to_string x in
    FStar_Util.format1 "The pattern variable \"%s\" was used more than once"
      m
let disjunctive_pattern_vars:
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list -> Prims.string
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____554 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____554 (FStar_String.concat ", ") in
      let uu____563 = vars v1 in
      let uu____564 = vars v2 in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____563 uu____564
let name_and_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____586) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____598) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____610 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____610, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation:
  'Auu____623 .
    FStar_TypeChecker_Env.env ->
      'Auu____623 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            Prims.string
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____648 = name_and_result c in
          match uu____648 with
          | (f1,r1) ->
              let uu____661 = name_and_result c' in
              (match uu____661 with
               | (f2,r2) ->
                   let uu____674 = err_msg_type_strings env r1 r2 in
                   (match uu____674 with
                    | (s1,s2) ->
                        FStar_Util.format4
                          "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                          s1 f1 s2 f2))
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____689 = FStar_TypeChecker_Normalize.term_to_string env f in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____689
let expected_pure_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.string
  =
  fun e  ->
    fun c  ->
      let uu____702 = FStar_Syntax_Print.term_to_string e in
      let uu____703 =
        let uu____704 = name_and_result c in
        FStar_All.pipe_left FStar_Pervasives_Native.fst uu____704 in
      FStar_Util.format2
        "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
        uu____702 uu____703
let expected_ghost_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.string
  =
  fun e  ->
    fun c  ->
      let uu____731 = FStar_Syntax_Print.term_to_string e in
      let uu____732 =
        let uu____733 = name_and_result c in
        FStar_All.pipe_left FStar_Pervasives_Native.fst uu____733 in
      FStar_Util.format2
        "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
        uu____731 uu____732
let expected_effect_1_got_effect_2:
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____756 = FStar_Syntax_Print.lid_to_string c1 in
      let uu____757 = FStar_Syntax_Print.lid_to_string c2 in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____756 uu____757
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____770 = FStar_Syntax_Print.lbname_to_string l in
      let uu____771 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____770 uu____771
let failed_to_prove_specification: Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____782 ->
        let uu____785 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____785
let top_level_effect: Prims.string =
  "Top-level let-bindings must be total; this term may have effects"
let cardinality_constraint_violated:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun l  ->
    fun a  ->
      let uu____800 = FStar_Syntax_Print.lid_to_string l in
      let uu____801 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
      FStar_Util.format2
        "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
        uu____800 uu____801