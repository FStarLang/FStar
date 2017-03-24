open Prims
let info_as_string:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.identifier_info -> Prims.string
  =
  fun env  ->
    fun info  ->
      let uu____7 =
        match info.FStar_TypeChecker_Common.identifier with
        | FStar_Util.Inl bv ->
            let uu____13 = FStar_Syntax_Print.nm_to_string bv in
            let uu____14 = FStar_Syntax_Syntax.range_of_bv bv in
            (uu____13, uu____14)
        | FStar_Util.Inr fv ->
            let uu____16 =
              let uu____17 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_Syntax_Print.lid_to_string uu____17 in
            let uu____18 = FStar_Syntax_Syntax.range_of_fv fv in
            (uu____16, uu____18) in
      match uu____7 with
      | (id_string,range) ->
          let uu____21 = FStar_Range.string_of_range range in
          let uu____22 =
            FStar_TypeChecker_Normalize.term_to_string env
              info.FStar_TypeChecker_Common.identifier_ty in
          FStar_Util.format3 "(defined at %s) %s : %s" uu____21 id_string
            uu____22
let info_at_pos:
  FStar_TypeChecker_Env.env ->
    Prims.string -> Prims.int -> Prims.int -> Prims.string Prims.option
  =
  fun env  ->
    fun file  ->
      fun row  ->
        fun col  ->
          let uu____36 = FStar_TypeChecker_Common.info_at_pos file row col in
          match uu____36 with
          | None  -> None
          | Some i -> let uu____40 = info_as_string env i in Some uu____40
let add_errors:
  FStar_TypeChecker_Env.env ->
    (Prims.string* FStar_Range.range) Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____67  ->
                match uu____67 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____76 = FStar_TypeChecker_Env.get_range env in
                      (msg, uu____76)
                    else
                      (let r' =
                         let uu___185_79 = r in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___185_79.FStar_Range.use_range)
                         } in
                       let uu____80 =
                         let uu____81 = FStar_Range.file_of_range r' in
                         let uu____82 =
                           let uu____83 = FStar_TypeChecker_Env.get_range env in
                           FStar_Range.file_of_range uu____83 in
                         uu____81 <> uu____82 in
                       if uu____80
                       then
                         let uu____86 =
                           let uu____87 =
                             let uu____88 =
                               let uu____89 =
                                 FStar_Range.string_of_use_range r in
                               Prims.strcat uu____89 ")" in
                             Prims.strcat "(Also see: " uu____88 in
                           Prims.strcat msg uu____87 in
                         let uu____90 = FStar_TypeChecker_Env.get_range env in
                         (uu____86, uu____90)
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
            let uu____107 =
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
          let uu____123 = possibly_verbose_message env t2 t1 in
          match uu____123 with
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
        let uu____139 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____139
let expected_a_term_of_type_t_got_a_function:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____152 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____153 = FStar_Syntax_Print.term_to_string e in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____152 uu____153 msg
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
          let uu____166 = FStar_TypeChecker_Normalize.term_to_string env t1 in
          let uu____167 = FStar_Syntax_Print.term_to_string e in
          let uu____168 = FStar_TypeChecker_Normalize.term_to_string env t2 in
          FStar_Util.format3
            "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
            uu____166 uu____167 uu____168
let expected_function_with_parameter_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____180 = FStar_TypeChecker_Normalize.term_to_string env t1 in
        let uu____181 = FStar_TypeChecker_Normalize.term_to_string env t2 in
        FStar_Util.format3
          "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
          uu____180 uu____181
let expected_pattern_of_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____194 = FStar_TypeChecker_Normalize.term_to_string env t1 in
          let uu____195 = FStar_Syntax_Print.term_to_string e in
          let uu____196 = FStar_TypeChecker_Normalize.term_to_string env t2 in
          FStar_Util.format3
            "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
            uu____194 uu____195 uu____196
let basic_type_error:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____211 = possibly_verbose_message env t1 t2 in
          match uu____211 with
          | (s1,s2,extra) ->
              (match eopt with
               | None  ->
                   FStar_Util.format3
                     "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra
               | Some e ->
                   let uu____219 = FStar_Syntax_Print.term_to_string e in
                   FStar_Util.format4
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1
                     uu____219 s2 extra)
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
        let uu____229 = FStar_TypeChecker_Normalize.term_to_string env k1 in
        let uu____230 = FStar_TypeChecker_Normalize.term_to_string env k2 in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____229 uu____230
let constructor_builds_the_wrong_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____243 = FStar_Syntax_Print.term_to_string d in
          let uu____244 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____245 = FStar_TypeChecker_Normalize.term_to_string env t' in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____243 uu____244 uu____245
let constructor_fails_the_positivity_check env d l =
  let uu____263 = FStar_Syntax_Print.term_to_string d in
  let uu____264 = FStar_Syntax_Print.lid_to_string l in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    uu____263 uu____264
let inline_type_annotation_and_val_decl: FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____268 = FStar_Syntax_Print.lid_to_string l in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____268
let inferred_type_causes_variable_to_escape:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____278 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____279 = FStar_Syntax_Print.bv_to_string x in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____278 uu____279
let expected_typ_of_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun t  ->
        fun k2  ->
          let uu____292 = FStar_TypeChecker_Normalize.term_to_string env k1 in
          let uu____293 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____294 = FStar_TypeChecker_Normalize.term_to_string env k2 in
          FStar_Util.format3
            "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\""
            uu____292 uu____293 uu____294
let expected_tcon_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____304 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____305 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____304 uu____305
let expected_dcon_kind:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____315 = FStar_TypeChecker_Normalize.term_to_string env t in
        let uu____316 = FStar_TypeChecker_Normalize.term_to_string env k in
        FStar_Util.format2
          "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____315 uu____316
let expected_function_typ:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____323 = FStar_TypeChecker_Normalize.term_to_string env t in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____323
let expected_poly_typ:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____336 = FStar_Syntax_Print.term_to_string f in
          let uu____337 = FStar_TypeChecker_Normalize.term_to_string env t in
          let uu____338 = FStar_TypeChecker_Normalize.term_to_string env targ in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____336 uu____337 uu____338
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
        let uu____359 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string) in
        FStar_All.pipe_right uu____359 (FStar_String.concat ", ") in
      let uu____364 = vars v1 in
      let uu____365 = vars v2 in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____364 uu____365
let name_and_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____382) -> ("Tot", t)
  | FStar_Syntax_Syntax.GTotal (t,uu____392) -> ("GTot", t)
  | FStar_Syntax_Syntax.Comp ct ->
      let uu____402 =
        FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name in
      (uu____402, (ct.FStar_Syntax_Syntax.result_typ))
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____439 = name_and_result c in
  match uu____439 with
  | (f1,r1) ->
      let uu____450 = name_and_result c' in
      (match uu____450 with
       | (f2,r2) ->
           let uu____461 = FStar_TypeChecker_Normalize.term_to_string env r1 in
           let uu____462 = FStar_TypeChecker_Normalize.term_to_string env r2 in
           FStar_Util.format4
             "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
             uu____461 f1 uu____462 f2)
let unexpected_non_trivial_precondition_on_term:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____469 = FStar_TypeChecker_Normalize.term_to_string env f in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____469
let expected_pure_expression e c =
  let uu____486 = FStar_Syntax_Print.term_to_string e in
  let uu____487 =
    let uu____488 = name_and_result c in
    FStar_All.pipe_left Prims.fst uu____488 in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    uu____486 uu____487
let expected_ghost_expression e c =
  let uu____515 = FStar_Syntax_Print.term_to_string e in
  let uu____516 =
    let uu____517 = name_and_result c in
    FStar_All.pipe_left Prims.fst uu____517 in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    uu____515 uu____516
let expected_effect_1_got_effect_2:
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____534 = FStar_Syntax_Print.lid_to_string c1 in
      let uu____535 = FStar_Syntax_Print.lid_to_string c2 in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____534 uu____535
let failed_to_prove_specification_of:
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____544 = FStar_Syntax_Print.lbname_to_string l in
      let uu____545 = FStar_All.pipe_right lbls (FStar_String.concat ", ") in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____544 uu____545
let failed_to_prove_specification: Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____552 ->
        let uu____554 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t") in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____554
let top_level_effect: Prims.string =
  "Top-level let-bindings must be total; this term may have effects"
let cardinality_constraint_violated l a =
  let uu____572 = FStar_Syntax_Print.lid_to_string l in
  let uu____573 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    uu____572 uu____573