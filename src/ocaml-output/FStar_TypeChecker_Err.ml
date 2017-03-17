open Prims
let add_errors :
  FStar_TypeChecker_Env.env ->
    (Prims.string * FStar_Range.range) Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____134  ->
                match uu____134 with
                | (msg,r) ->
                    (match r = FStar_Range.dummyRange with
                     | true  ->
                         let _0_525 = FStar_TypeChecker_Env.get_range env  in
                         (msg, _0_525)
                     | uu____36 ->
                         let r' =
                           let uu___184_38 = r  in
                           {
                             FStar_Range.def_range =
                               (r.FStar_Range.use_range);
                             FStar_Range.use_range =
                               (uu___184_38.FStar_Range.use_range)
                           }  in
                         let uu____39 =
                           let _0_527 = FStar_Range.file_of_range r'  in
                           let _0_526 =
                             FStar_Range.file_of_range
                               (FStar_TypeChecker_Env.get_range env)
                              in
                           _0_527 <> _0_526  in
                         (match uu____39 with
                          | true  ->
                              let _0_532 =
                                let _0_530 =
                                  let _0_529 =
                                    let _0_528 =
                                      FStar_Range.string_of_use_range r  in
                                    Prims.strcat _0_528 ")"  in
                                  Prims.strcat "(Also see: " _0_529  in
                                Prims.strcat msg _0_530  in
                              let _0_531 =
                                FStar_TypeChecker_Env.get_range env  in
                              (_0_532, _0_531)
                          | uu____42 -> (msg, r)))))
         in
      FStar_Errors.add_errors errs
  
let exhaustiveness_check : Prims.string = "Patterns are incomplete" 
let subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> Prims.unit -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun x  ->
          let _0_534 = FStar_TypeChecker_Normalize.term_to_string env t2  in
          let _0_533 = FStar_TypeChecker_Normalize.term_to_string env t1  in
          FStar_Util.format2
            "Subtyping check failed; expected type %s; got type %s" _0_534
            _0_533
  
let ill_kinded_type : Prims.string = "Ill-kinded type" 
let totality_check : Prims.string = "This term may not terminate" 
let unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let _0_535 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str _0_535
  
let expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let _0_537 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_536 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            _0_537 _0_536 msg
  
let unexpected_implicit_argument : Prims.string =
  "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"
  
let expected_expression_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let _0_540 = FStar_TypeChecker_Normalize.term_to_string env t1  in
          let _0_539 = FStar_Syntax_Print.term_to_string e  in
          let _0_538 = FStar_TypeChecker_Normalize.term_to_string env t2  in
          FStar_Util.format3
            "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
            _0_540 _0_539 _0_538
  
let expected_function_with_parameter_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let _0_542 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let _0_541 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        FStar_Util.format3
          "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
          _0_542 _0_541
  
let expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let _0_545 = FStar_TypeChecker_Normalize.term_to_string env t1  in
          let _0_544 = FStar_Syntax_Print.term_to_string e  in
          let _0_543 = FStar_TypeChecker_Normalize.term_to_string env t2  in
          FStar_Util.format3
            "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
            _0_545 _0_544 _0_543
  
let basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          match eopt with
          | None  ->
              let _0_547 = FStar_TypeChecker_Normalize.term_to_string env t1
                 in
              let _0_546 = FStar_TypeChecker_Normalize.term_to_string env t2
                 in
              FStar_Util.format2 "Expected type \"%s\"; got type \"%s\""
                _0_547 _0_546
          | Some e ->
              let _0_550 = FStar_TypeChecker_Normalize.term_to_string env t1
                 in
              let _0_549 = FStar_Syntax_Print.term_to_string e  in
              let _0_548 = FStar_TypeChecker_Normalize.term_to_string env t2
                 in
              FStar_Util.format3
                "Expected type \"%s\"; but \"%s\" has type \"%s\"" _0_550
                _0_549 _0_548
  
let occurs_check : Prims.string =
  "Possibly infinite typ (occurs check failed)" 
let unification_well_formedness : Prims.string =
  "Term or type of an unexpected sort" 
let incompatible_kinds :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun k2  ->
        let _0_552 = FStar_TypeChecker_Normalize.term_to_string env k1  in
        let _0_551 = FStar_TypeChecker_Normalize.term_to_string env k2  in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _0_552
          _0_551
  
let constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let _0_555 = FStar_Syntax_Print.term_to_string d  in
          let _0_554 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_553 = FStar_TypeChecker_Normalize.term_to_string env t'  in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            _0_555 _0_554 _0_553
  
let constructor_fails_the_positivity_check env d l =
  let _0_557 = FStar_Syntax_Print.term_to_string d  in
  let _0_556 = FStar_Syntax_Print.lid_to_string l  in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    _0_557 _0_556
  
let inline_type_annotation_and_val_decl : FStar_Ident.lid -> Prims.string =
  fun l  ->
    let _0_558 = FStar_Syntax_Print.lid_to_string l  in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      _0_558
  
let inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let _0_560 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_559 = FStar_Syntax_Print.bv_to_string x  in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          _0_560 _0_559
  
let expected_typ_of_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun t  ->
        fun k2  ->
          let _0_563 = FStar_TypeChecker_Normalize.term_to_string env k1  in
          let _0_562 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_561 = FStar_TypeChecker_Normalize.term_to_string env k2  in
          FStar_Util.format3
            "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _0_563
            _0_562 _0_561
  
let expected_tcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_565 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_564 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          _0_565 _0_564
  
let expected_dcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_567 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_566 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          _0_567 _0_566
  
let expected_function_typ :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let _0_568 = FStar_TypeChecker_Normalize.term_to_string env t  in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" _0_568
  
let expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let _0_571 = FStar_Syntax_Print.term_to_string f  in
          let _0_570 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_569 = FStar_TypeChecker_Normalize.term_to_string env targ
             in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            _0_571 _0_570 _0_569
  
let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv -> Prims.string =
  fun x  ->
    let m = FStar_Syntax_Print.bv_to_string x  in
    FStar_Util.format1 "The pattern variable \"%s\" was used more than once"
      m
  
let disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list -> Prims.string
  =
  fun v1  ->
    fun v2  ->
      let vars v =
        let _0_572 =
          FStar_All.pipe_right v
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right _0_572 (FStar_String.concat ", ")  in
      let _0_574 = vars v1  in
      let _0_573 = vars v2  in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        _0_574 _0_573
  
let name_and_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____449) -> ("Tot", t)
  | FStar_Syntax_Syntax.GTotal (t,uu____459) -> ("GTot", t)
  | FStar_Syntax_Syntax.Comp ct ->
      let _0_575 =
        FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
         in
      (_0_575, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____319 = name_and_result c  in
  match uu____319 with
  | (f1,r1) ->
      let uu____330 = name_and_result c'  in
      (match uu____330 with
       | (f2,r2) ->
           let _0_577 = FStar_TypeChecker_Normalize.term_to_string env r1  in
           let _0_576 = FStar_TypeChecker_Normalize.term_to_string env r2  in
           FStar_Util.format4
             "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
             _0_577 f1 _0_576 f2)
  
let unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let _0_578 = FStar_TypeChecker_Normalize.term_to_string env f  in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" _0_578
  
let expected_pure_expression e c =
  let _0_581 = FStar_Syntax_Print.term_to_string e  in
  let _0_580 =
    let _0_579 = name_and_result c  in FStar_All.pipe_left Prims.fst _0_579
     in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    _0_581 _0_580
  
let expected_ghost_expression e c =
  let _0_584 = FStar_Syntax_Print.term_to_string e  in
  let _0_583 =
    let _0_582 = name_and_result c  in FStar_All.pipe_left Prims.fst _0_582
     in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    _0_584 _0_583
  
let expected_effect_1_got_effect_2 :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let _0_586 = FStar_Syntax_Print.lid_to_string c1  in
      let _0_585 = FStar_Syntax_Print.lid_to_string c2  in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s" _0_586
        _0_585
  
let failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let _0_588 = FStar_Syntax_Print.lbname_to_string l  in
      let _0_587 = FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        _0_588 _0_587
  
let failed_to_prove_specification : Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____411 ->
        let _0_589 = FStar_All.pipe_right lbls (FStar_String.concat "\n\t")
           in
        FStar_Util.format1 "The following problems were found:\n\t%s" _0_589
  
let top_level_effect : Prims.string =
  "Top-level let-bindings must be total; this term may have effects" 
let cardinality_constraint_violated l a =
  let _0_591 = FStar_Syntax_Print.lid_to_string l  in
  let _0_590 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    _0_591 _0_590
  