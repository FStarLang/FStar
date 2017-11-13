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
          let uu____25 =
            let uu____28 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info in
            FStar_TypeChecker_Common.id_info_at_pos uu____28 file row col in
          match uu____25 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____111 =
                     let uu____122 =
                       let uu____127 = FStar_Syntax_Print.nm_to_string bv in
                       FStar_Util.Inl uu____127 in
                     let uu____128 = FStar_Syntax_Syntax.range_of_bv bv in
                     (uu____122,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____128) in
                   FStar_Pervasives_Native.Some uu____111
               | FStar_Util.Inr fv ->
                   let uu____144 =
                     let uu____155 =
                       let uu____160 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Util.Inr uu____160 in
                     let uu____161 = FStar_Syntax_Syntax.range_of_fv fv in
                     (uu____155,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____161) in
                   FStar_Pervasives_Native.Some uu____144)
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
             (fun uu____225  ->
                match uu____225 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____240 = FStar_TypeChecker_Env.get_range env in
                      (msg, uu____240)
                    else
                      (let r' =
                         let uu____243 = FStar_Range.use_range r in
                         FStar_Range.set_def_range r uu____243 in
                       let uu____244 =
                         let uu____245 = FStar_Range.file_of_range r' in
                         let uu____246 =
                           let uu____247 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____247 in
                         uu____245 <> uu____246 in
                       if uu____244
                       then
                         let uu____252 =
                           let uu____253 =
                             let uu____254 =
                               let uu____255 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____255 ")" in
                             Prims.strcat "(Also see: " uu____254 in
                           Prims.strcat msg uu____253 in
                         let uu____256 = FStar_TypeChecker_Env.get_range env in
                         (uu____252, uu____256)
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
            (fun uu____289  ->
               (let uu____291 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____292 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____293 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____292, uu____293)))
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
          let uu____307 = err_msg_type_strings env t1 t2 in
          match uu____307 with
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
        let uu____323 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____323
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____336 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____337 = FStar_Syntax_Print.term_to_string e in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____336 uu____337 msg
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
          let uu____350 = err_msg_type_strings env t1 t2 in
          match uu____350 with
          | (s1,s2) ->
              let uu____357 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                s1 uu____357 s2
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____369 = err_msg_type_strings env t1 t2 in
        match uu____369 with
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
          let uu____390 = err_msg_type_strings env t1 t2 in
          match uu____390 with
          | (s1,s2) ->
              let uu____397 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                s1 uu____397 s2
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____414 = err_msg_type_strings env t1 t2 in
          match uu____414 with
          | (s1,s2) ->
              (match eopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Util.format2 "Expected type \"%s\"; got type \"%s\""
                     s1 s2
               | FStar_Pervasives_Native.Some e ->
                   let uu____422 =
                     FStar_TypeChecker_Normalize.term_to_string env e in
                   FStar_Util.format3
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                     uu____422 s2)
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
        let uu____432 = FStar_TypeChecker_Normalize.term_to_string env k1 in
        let uu____433 = FStar_TypeChecker_Normalize.term_to_string env k2 in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____432 uu____433
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____446 = FStar_Syntax_Print.term_to_string d in
          let uu____447 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____448 = FStar_TypeChecker_Normalize.term_to_string env t' in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____446 uu____447 uu____448
let constructor_fails_the_positivity_check:
  'Auu____453 .
    'Auu____453 ->
      FStar_Syntax_Syntax.term -> FStar_Ident.lid -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____466 = FStar_Syntax_Print.term_to_string d in
        let uu____467 = FStar_Syntax_Print.lid_to_string l in
        FStar_Util.format2
          "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
          uu____466 uu____467
let inline_type_annotation_and_val_decl: FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____471 = FStar_Syntax_Print.lid_to_string l in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____471
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____481 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____482 = FStar_Syntax_Print.bv_to_string x in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____481 uu____482
let expected_function_typ:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____489 = FStar_TypeChecker_Normalize.term_to_string env t in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____489
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____502 = FStar_Syntax_Print.term_to_string f in
          let uu____503 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____504 = FStar_TypeChecker_Normalize.term_to_string env targ in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____502 uu____503 uu____504
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
        let uu____531 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____531 (FStar_String.concat ", ") in
      let uu____540 = vars v1 in
      let uu____541 = vars v2 in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____540 uu____541
let name_and_result:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string,FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____562) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____574) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____586 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
        (uu____586, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation:
  'Auu____594 .
    FStar_TypeChecker_Env.env ->
      'Auu____594 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            Prims.string
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____619 = name_and_result c in
          match uu____619 with
          | (f1,r1) ->
              let uu____632 = name_and_result c' in
              (match uu____632 with
               | (f2,r2) ->
                   let uu____645 = err_msg_type_strings env r1 r2 in
                   (match uu____645 with
                    | (s1,s2) ->
                        FStar_Util.format4
                          "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                          s1 f1 s2 f2))
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____658 = FStar_TypeChecker_Normalize.term_to_string env f in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____658
let expected_pure_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.string
  =
  fun e  ->
    fun c  ->
      let uu____669 = FStar_Syntax_Print.term_to_string e in
      let uu____670 =
        let uu____671 = name_and_result c in
        FStar_All.pipe_left FStar_Pervasives_Native.fst uu____671 in
      FStar_Util.format2
        "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
        uu____669 uu____670
let expected_ghost_expression:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.string
  =
  fun e  ->
    fun c  ->
      let uu____696 = FStar_Syntax_Print.term_to_string e in
      let uu____697 =
        let uu____698 = name_and_result c in
        FStar_All.pipe_left FStar_Pervasives_Native.fst uu____698 in
      FStar_Util.format2
        "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
        uu____696 uu____697
let expected_effect_1_got_effect_2:
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____719 = FStar_Syntax_Print.lid_to_string c1 in
      let uu____720 = FStar_Syntax_Print.lid_to_string c2 in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____719 uu____720
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____731 = FStar_Syntax_Print.lbname_to_string l in
      let uu____732 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____731 uu____732
let failed_to_prove_specification: Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____742 ->
        let uu____745 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____745
let top_level_effect: Prims.string =
  "Top-level let-bindings must be total; this term may have effects"
let cardinality_constraint_violated:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun l  ->
    fun a  ->
      let uu____758 = FStar_Syntax_Print.lid_to_string l in
      let uu____759 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
      FStar_Util.format2
        "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
        uu____758 uu____759