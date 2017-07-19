open Prims
let info_at_pos env file row col =
  let uu____35 = FStar_TypeChecker_Common.info_at_pos file row col in
  match uu____35 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      (match info.FStar_TypeChecker_Common.identifier with
       | FStar_Util.Inl bv ->
           let uu____74 =
             let uu____85 =
               let uu____90 = FStar_Syntax_Print.nm_to_string bv in
               FStar_Util.Inl uu____90 in
             let uu____91 = FStar_Syntax_Syntax.range_of_bv bv in
             (uu____85, (info.FStar_TypeChecker_Common.identifier_ty),
               uu____91) in
           FStar_Pervasives_Native.Some uu____74
       | FStar_Util.Inr fv ->
           let uu____107 =
             let uu____118 =
               let uu____123 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_Util.Inr uu____123 in
             let uu____124 = FStar_Syntax_Syntax.range_of_fv fv in
             (uu____118, (info.FStar_TypeChecker_Common.identifier_ty),
               uu____124) in
           FStar_Pervasives_Native.Some uu____107)
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
             (fun uu____184  ->
                match uu____184 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____199 = FStar_TypeChecker_Env.get_range env in
                      (msg, uu____199)
                    else
                      (let r' =
                         let uu___201_202 = r in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___201_202.FStar_Range.use_range)
                         } in
                       let uu____203 =
                         let uu____204 = FStar_Range.file_of_range r' in
                         let uu____205 =
                           let uu____206 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____206 in
                         uu____204 <> uu____205 in
                       if uu____203
                       then
                         let uu____211 =
                           let uu____212 =
                             let uu____213 =
                               let uu____214 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____214 ")" in
                             Prims.strcat "(Also see: " uu____213 in
                           Prims.strcat msg uu____212 in
                         let uu____215 = FStar_TypeChecker_Env.get_range env in
                         (uu____211, uu____215)
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
            (fun uu____244  ->
               (let uu____246 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes" in
                ());
               (let uu____247 =
                  FStar_TypeChecker_Normalize.term_to_string env t1 in
                let uu____248 =
                  FStar_TypeChecker_Normalize.term_to_string env t2 in
                (uu____247, uu____248)))
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
          let uu____262 = err_msg_type_strings env t1 t2 in
          match uu____262 with
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
        let uu____278 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____278
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____291 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____292 = FStar_Syntax_Print.term_to_string e in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____291 uu____292 msg
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
          let uu____305 = err_msg_type_strings env t1 t2 in
          match uu____305 with
          | (s1,s2) ->
              let uu____312 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                s1 uu____312 s2
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____324 = err_msg_type_strings env t1 t2 in
        match uu____324 with
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
          let uu____345 = err_msg_type_strings env t1 t2 in
          match uu____345 with
          | (s1,s2) ->
              let uu____352 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format3
                "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                s1 uu____352 s2
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____369 = err_msg_type_strings env t1 t2 in
          match uu____369 with
          | (s1,s2) ->
              (match eopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Util.format2 "Expected type \"%s\"; got type \"%s\""
                     s1 s2
               | FStar_Pervasives_Native.Some e ->
                   let uu____377 = FStar_Syntax_Print.term_to_string e in
                   FStar_Util.format3
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                     uu____377 s2)
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
        let uu____387 = FStar_TypeChecker_Normalize.term_to_string env k1 in
        let uu____388 = FStar_TypeChecker_Normalize.term_to_string env k2 in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____387 uu____388
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____401 = FStar_Syntax_Print.term_to_string d in
          let uu____402 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____403 = FStar_TypeChecker_Normalize.term_to_string env t' in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____401 uu____402 uu____403
let constructor_fails_the_positivity_check env d l =
  let uu____421 = FStar_Syntax_Print.term_to_string d in
  let uu____422 = FStar_Syntax_Print.lid_to_string l in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    uu____421 uu____422
let inline_type_annotation_and_val_decl: FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____426 = FStar_Syntax_Print.lid_to_string l in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____426
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____436 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____437 = FStar_Syntax_Print.bv_to_string x in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____436 uu____437
let expected_function_typ:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____444 = FStar_TypeChecker_Normalize.term_to_string env t in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____444
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____457 = FStar_Syntax_Print.term_to_string f in
          let uu____458 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____459 = FStar_TypeChecker_Normalize.term_to_string env targ in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____457 uu____458 uu____459
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
        let uu____486 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____486 (FStar_String.concat ", ") in
      let uu____495 = vars v1 in
      let uu____496 = vars v2 in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____495 uu____496
let name_and_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____521) -> ("Tot", t)
  | FStar_Syntax_Syntax.GTotal (t,uu____539) -> ("GTot", t)
  | FStar_Syntax_Syntax.Comp ct ->
      let uu____557 =
        FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
      (uu____557, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____604 = name_and_result c in
  match uu____604 with
  | (f1,r1) ->
      let uu____623 = name_and_result c' in
      (match uu____623 with
       | (f2,r2) ->
           let uu____642 = err_msg_type_strings env r1 r2 in
           (match uu____642 with
            | (s1,s2) ->
                FStar_Util.format4
                  "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                  s1 f1 s2 f2))
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____655 = FStar_TypeChecker_Normalize.term_to_string env f in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____655
let expected_pure_expression e c =
  let uu____676 = FStar_Syntax_Print.term_to_string e in
  let uu____677 =
    let uu____678 = name_and_result c in
    FStar_All.pipe_left FStar_Pervasives_Native.fst uu____678 in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    uu____676 uu____677
let expected_ghost_expression e c =
  let uu____719 = FStar_Syntax_Print.term_to_string e in
  let uu____720 =
    let uu____721 = name_and_result c in
    FStar_All.pipe_left FStar_Pervasives_Native.fst uu____721 in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    uu____719 uu____720
let expected_effect_1_got_effect_2:
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____748 = FStar_Syntax_Print.lid_to_string c1 in
      let uu____749 = FStar_Syntax_Print.lid_to_string c2 in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____748 uu____749
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____760 = FStar_Syntax_Print.lbname_to_string l in
      let uu____761 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____760 uu____761
let failed_to_prove_specification: Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____771 ->
        let uu____774 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____774
let top_level_effect: Prims.string =
  "Top-level let-bindings must be total; this term may have effects"
let cardinality_constraint_violated l a =
  let uu____797 = FStar_Syntax_Print.lid_to_string l in
  let uu____798 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    uu____797 uu____798