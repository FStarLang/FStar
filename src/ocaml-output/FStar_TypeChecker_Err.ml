open Prims
let format_info:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Range.range -> Prims.string
  =
  fun env  ->
    fun name  ->
      fun typ  ->
        fun range  ->
          let uu____13 = FStar_Range.string_of_range range in
          let uu____14 = FStar_TypeChecker_Normalize.term_to_string env typ in
          FStar_Util.format3 "(defined at %s) %s : %s" uu____13 name uu____14
let info_as_string:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.identifier_info -> Prims.string
  =
  fun env  ->
    fun info  ->
      let uu____21 =
        match info.FStar_TypeChecker_Common.identifier with
        | FStar_Util.Inl bv ->
            let uu____27 = FStar_Syntax_Print.nm_to_string bv in
            let uu____28 = FStar_Syntax_Syntax.range_of_bv bv in
            (uu____27, uu____28)
        | FStar_Util.Inr fv ->
            let uu____30 =
              let uu____31 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_Syntax_Print.lid_to_string uu____31 in
            let uu____32 = FStar_Syntax_Syntax.range_of_fv fv in
            (uu____30, uu____32) in
      match uu____21 with
      | (id_string,range) ->
          format_info env id_string
            info.FStar_TypeChecker_Common.identifier_ty range
let info_at_pos:
  FStar_TypeChecker_Env.env ->
    Prims.string -> Prims.int -> Prims.int -> Prims.string Prims.option
  =
  fun env  ->
    fun file  ->
      fun row  ->
        fun col  ->
          let uu____48 = FStar_TypeChecker_Common.info_at_pos file row col in
          match uu____48 with
          | None  -> None
          | Some i -> let uu____52 = info_as_string env i in Some uu____52
let add_errors:
  FStar_TypeChecker_Env.env ->
    (Prims.string* FStar_Range.range) Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____79  ->
                match uu____79 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____88 = FStar_TypeChecker_Env.get_range env in
                      (msg, uu____88)
                    else
                      (let r' =
                         let uu___194_91 = r in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___194_91.FStar_Range.use_range)
                         } in
                       let uu____92 =
                         let uu____93 = FStar_Range.file_of_range r' in
                         let uu____94 =
                           let uu____95 = FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____95 in
                         uu____93 <> uu____94 in
                       if uu____92
                       then
                         let uu____98 =
                           let uu____99 =
                             let uu____100 =
                               let uu____101 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____101 ")" in
                             Prims.strcat "(Also see: " uu____100 in
                           Prims.strcat msg uu____99 in
                         let uu____102 = FStar_TypeChecker_Env.get_range env in
                         (uu____98, uu____102)
                       else (msg, r)))) in
      FStar_Errors.add_errors errs1
let possibly_verbose_message:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string* Prims.string* Prims.string)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        let extra =
          if s1 = s2
          then
            let uu____119 =
              FStar_Options.set_options FStar_Options.Set
                "--prn --print_universes" in
            let s11 = FStar_TypeChecker_Normalize.term_to_string env t1 in
            let s21 = FStar_TypeChecker_Normalize.term_to_string env t2 in
            FStar_Util.format2
              "\nMore precisely: expected type:\n%s\ngot:\n%s\n" s11 s21
          else "" in
        (s1, s2, extra)
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
          let uu____135 = possibly_verbose_message env t2 t1 in
          match uu____135 with
          | (s2,s1,extra) ->
              FStar_Util.format3
                "Subtyping check failed; expected type %s; got type %s%s" s2
                s1 extra
let ill_kinded_type: Prims.string = "Ill-kinded type"
let totality_check: Prims.string = "This term may not terminate"
let unexpected_signature_for_monad:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____151 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____151
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____164 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____165 = FStar_Syntax_Print.term_to_string e in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____164 uu____165 msg
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
          let uu____178 = FStar_TypeChecker_Normalize.term_to_string env t1 in
          let uu____179 = FStar_Syntax_Print.term_to_string e in
          let uu____180 = FStar_TypeChecker_Normalize.term_to_string env t2 in
          FStar_Util.format3
            "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
            uu____178 uu____179 uu____180
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____192 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let uu____193 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        FStar_Util.format3
          "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
          uu____192 uu____193
let expected_pattern_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____206 = FStar_TypeChecker_Normalize.term_to_string env t1 in
          let uu____207 = FStar_Syntax_Print.term_to_string e in
          let uu____208 = FStar_TypeChecker_Normalize.term_to_string env t2 in
          FStar_Util.format3
            "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
            uu____206 uu____207 uu____208
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____223 = possibly_verbose_message env t1 t2 in
          match uu____223 with
          | (s1,s2,extra) ->
              (match eopt with
               | None  ->
                   FStar_Util.format3
                     "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra
               | Some e ->
                   let uu____231 = FStar_Syntax_Print.term_to_string e in
                   FStar_Util.format4
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1
                     uu____231 s2 extra)
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
        let uu____241 = FStar_TypeChecker_Normalize.term_to_string env k1 in
        let uu____242 = FStar_TypeChecker_Normalize.term_to_string env k2 in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____241 uu____242
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____255 = FStar_Syntax_Print.term_to_string d in
          let uu____256 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____257 = FStar_TypeChecker_Normalize.term_to_string env t' in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____255 uu____256 uu____257
let constructor_fails_the_positivity_check env d l =
  let uu____275 = FStar_Syntax_Print.term_to_string d in
  let uu____276 = FStar_Syntax_Print.lid_to_string l in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    uu____275 uu____276
let inline_type_annotation_and_val_decl: FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____280 = FStar_Syntax_Print.lid_to_string l in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____280
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____290 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____291 = FStar_Syntax_Print.bv_to_string x in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____290 uu____291
let expected_typ_of_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun t  ->
        fun k2  ->
          let uu____304 = FStar_TypeChecker_Normalize.term_to_string env k1 in
          let uu____305 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____306 = FStar_TypeChecker_Normalize.term_to_string env k2 in
          FStar_Util.format3
            "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\""
            uu____304 uu____305 uu____306
let expected_tcon_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____316 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____317 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____316 uu____317
let expected_dcon_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____327 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____328 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____327 uu____328
let expected_function_typ:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____335 = FStar_TypeChecker_Normalize.term_to_string env t in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____335
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____348 = FStar_Syntax_Print.term_to_string f in
          let uu____349 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____350 = FStar_TypeChecker_Normalize.term_to_string env targ in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____348 uu____349 uu____350
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
        let uu____371 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____371 (FStar_String.concat ", ") in
      let uu____376 = vars v1 in
      let uu____377 = vars v2 in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____376 uu____377
let name_and_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____394) -> ("Tot", t)
  | FStar_Syntax_Syntax.GTotal (t,uu____404) -> ("GTot", t)
  | FStar_Syntax_Syntax.Comp ct ->
      let uu____414 =
        FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
      (uu____414, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____451 = name_and_result c in
  match uu____451 with
  | (f1,r1) ->
      let uu____462 = name_and_result c' in
      (match uu____462 with
       | (f2,r2) ->
           let uu____473 = FStar_TypeChecker_Normalize.term_to_string env r1 in
           let uu____474 = FStar_TypeChecker_Normalize.term_to_string env r2 in
           FStar_Util.format4
             "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
             uu____473 f1 uu____474 f2)
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____481 = FStar_TypeChecker_Normalize.term_to_string env f in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____481
let expected_pure_expression e c =
  let uu____498 = FStar_Syntax_Print.term_to_string e in
  let uu____499 =
    let uu____500 = name_and_result c in
    FStar_All.pipe_left Prims.fst uu____500 in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    uu____498 uu____499
let expected_ghost_expression e c =
  let uu____527 = FStar_Syntax_Print.term_to_string e in
  let uu____528 =
    let uu____529 = name_and_result c in
    FStar_All.pipe_left Prims.fst uu____529 in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    uu____527 uu____528
let expected_effect_1_got_effect_2:
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____546 = FStar_Syntax_Print.lid_to_string c1 in
      let uu____547 = FStar_Syntax_Print.lid_to_string c2 in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____546 uu____547
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____556 = FStar_Syntax_Print.lbname_to_string l in
      let uu____557 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____556 uu____557
let failed_to_prove_specification: Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____564 ->
        let uu____566 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____566
let top_level_effect: Prims.string =
  "Top-level let-bindings must be total; this term may have effects"
let cardinality_constraint_violated l a =
  let uu____584 = FStar_Syntax_Print.lid_to_string l in
  let uu____585 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    uu____584 uu____585