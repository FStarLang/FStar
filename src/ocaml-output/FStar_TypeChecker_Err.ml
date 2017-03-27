open Prims
let add_errors :
  FStar_TypeChecker_Env.env ->
    (Prims.string * FStar_Range.range) Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____27  ->
                match uu____27 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let _0_547 = FStar_TypeChecker_Env.get_range env  in
                      (msg, _0_547)
                    else
                      (let r' =
                         let uu___187_38 = r  in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___187_38.FStar_Range.use_range)
                         }  in
                       let uu____39 =
                         let _0_549 = FStar_Range.file_of_range r'  in
                         let _0_548 =
                           FStar_Range.file_of_range
                             (FStar_TypeChecker_Env.get_range env)
                            in
                         _0_549 <> _0_548  in
                       if uu____39
                       then
                         let _0_554 =
                           let _0_552 =
                             let _0_551 =
                               let _0_550 = FStar_Range.string_of_use_range r
                                  in
                               Prims.strcat _0_550 ")"  in
                             Prims.strcat "(Also see: " _0_551  in
                           Prims.strcat msg _0_552  in
                         let _0_553 = FStar_TypeChecker_Env.get_range env  in
                         (_0_554, _0_553)
                       else (msg, r))))
         in
      FStar_Errors.add_errors errs
  
let possibly_verbose_message :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (Prims.string * Prims.string * Prims.string)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let s1 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let s2 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        let extra =
          if s1 = s2
          then
            let uu____58 =
              FStar_Options.set_options FStar_Options.Set
                "--prn --print_universes"
               in
            let s1 = FStar_TypeChecker_Normalize.term_to_string env t1  in
            let s2 = FStar_TypeChecker_Normalize.term_to_string env t2  in
            FStar_Util.format2
              "\nMore precisely: expected type:\n%s\ngot:\n%s\n" s1 s2
          else ""  in
        (s1, s2, extra)
  
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
          let uu____74 = possibly_verbose_message env t2 t1  in
          match uu____74 with
          | (s2,s1,extra) ->
              FStar_Util.format3
                "Subtyping check failed; expected type %s; got type %s%s" s2
                s1 extra
  
let ill_kinded_type : Prims.string = "Ill-kinded type" 
let totality_check : Prims.string = "This term may not terminate" 
let unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let _0_555 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str _0_555
  
let expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let _0_557 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_556 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            _0_557 _0_556 msg
  
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
          let _0_560 = FStar_TypeChecker_Normalize.term_to_string env t1  in
          let _0_559 = FStar_Syntax_Print.term_to_string e  in
          let _0_558 = FStar_TypeChecker_Normalize.term_to_string env t2  in
          FStar_Util.format3
            "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
            _0_560 _0_559 _0_558
  
let expected_function_with_parameter_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let _0_562 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let _0_561 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        FStar_Util.format3
          "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
          _0_562 _0_561
  
let expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let _0_565 = FStar_TypeChecker_Normalize.term_to_string env t1  in
          let _0_564 = FStar_Syntax_Print.term_to_string e  in
          let _0_563 = FStar_TypeChecker_Normalize.term_to_string env t2  in
          FStar_Util.format3
            "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
            _0_565 _0_564 _0_563
  
let basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____151 = possibly_verbose_message env t1 t2  in
          match uu____151 with
          | (s1,s2,extra) ->
              (match eopt with
               | None  ->
                   FStar_Util.format3
                     "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra
               | Some e ->
                   let _0_566 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.format4
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1
                     _0_566 s2 extra)
  
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
        let _0_568 = FStar_TypeChecker_Normalize.term_to_string env k1  in
        let _0_567 = FStar_TypeChecker_Normalize.term_to_string env k2  in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _0_568
          _0_567
  
let constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let _0_571 = FStar_Syntax_Print.term_to_string d  in
          let _0_570 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_569 = FStar_TypeChecker_Normalize.term_to_string env t'  in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            _0_571 _0_570 _0_569
  
let constructor_fails_the_positivity_check env d l =
  let _0_573 = FStar_Syntax_Print.term_to_string d  in
  let _0_572 = FStar_Syntax_Print.lid_to_string l  in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    _0_573 _0_572
  
let inline_type_annotation_and_val_decl : FStar_Ident.lid -> Prims.string =
  fun l  ->
    let _0_574 = FStar_Syntax_Print.lid_to_string l  in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      _0_574
  
let inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let _0_576 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_575 = FStar_Syntax_Print.bv_to_string x  in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          _0_576 _0_575
  
let expected_typ_of_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun t  ->
        fun k2  ->
          let _0_579 = FStar_TypeChecker_Normalize.term_to_string env k1  in
          let _0_578 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_577 = FStar_TypeChecker_Normalize.term_to_string env k2  in
          FStar_Util.format3
            "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _0_579
            _0_578 _0_577
  
let expected_tcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_581 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_580 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          _0_581 _0_580
  
let expected_dcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_583 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let _0_582 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          _0_583 _0_582
  
let expected_function_typ :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let _0_584 = FStar_TypeChecker_Normalize.term_to_string env t  in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" _0_584
  
let expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let _0_587 = FStar_Syntax_Print.term_to_string f  in
          let _0_586 = FStar_TypeChecker_Normalize.term_to_string env t  in
          let _0_585 = FStar_TypeChecker_Normalize.term_to_string env targ
             in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            _0_587 _0_586 _0_585
  
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
        let _0_588 =
          FStar_All.pipe_right v
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right _0_588 (FStar_String.concat ", ")  in
      let _0_590 = vars v1  in
      let _0_589 = vars v2  in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        _0_590 _0_589
  
let name_and_result :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (Prims.string * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____299) -> ("Tot", t)
      | FStar_Syntax_Syntax.GTotal (t,uu____309) -> ("GTot", t)
      | FStar_Syntax_Syntax.Comp ct ->
          let _0_592 =
            FStar_Syntax_Print.lid_to_string
              ct.FStar_Syntax_Syntax.comp_typ_name
             in
          let _0_591 = FStar_TypeChecker_Env.result_typ env c  in
          (_0_592, _0_591)
  
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____349 = name_and_result env c  in
  match uu____349 with
  | (f1,r1) ->
      let uu____360 = name_and_result env c'  in
      (match uu____360 with
       | (f2,r2) ->
           let _0_594 = FStar_TypeChecker_Normalize.term_to_string env r1  in
           let _0_593 = FStar_TypeChecker_Normalize.term_to_string env r2  in
           FStar_Util.format4
             "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
             _0_594 f1 _0_593 f2)
  
let unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let _0_595 = FStar_TypeChecker_Normalize.term_to_string env f  in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" _0_595
  
let expected_pure_expression e c =
  let _0_597 = FStar_Syntax_Print.term_to_string e  in
  let _0_596 =
    FStar_Ident.string_of_lid (FStar_Syntax_Util.comp_effect_name c)  in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    _0_597 _0_596
  
let expected_ghost_expression e c =
  let _0_599 = FStar_Syntax_Print.term_to_string e  in
  let _0_598 =
    FStar_Ident.string_of_lid (FStar_Syntax_Util.comp_effect_name c)  in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    _0_599 _0_598
  
let expected_effect_1_got_effect_2 :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let _0_601 = FStar_Syntax_Print.lid_to_string c1  in
      let _0_600 = FStar_Syntax_Print.lid_to_string c2  in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s" _0_601
        _0_600
  
let failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let _0_603 = FStar_Syntax_Print.lbname_to_string l  in
      let _0_602 = FStar_All.pipe_right lbls (FStar_String.concat ", ")  in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        _0_603 _0_602
  
let failed_to_prove_specification : Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____429 ->
        let _0_604 = FStar_All.pipe_right lbls (FStar_String.concat "\n\t")
           in
        FStar_Util.format1 "The following problems were found:\n\t%s" _0_604
  
let top_level_effect : Prims.string =
  "Top-level let-bindings must be total; this term may have effects" 
let cardinality_constraint_violated l a =
  let _0_606 = FStar_Syntax_Print.lid_to_string l  in
  let _0_605 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    _0_606 _0_605
  