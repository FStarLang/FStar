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
             (fun uu____27  ->
                match uu____27 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____36 = FStar_TypeChecker_Env.get_range env  in
                      (msg, uu____36)
                    else
                      (let r' =
                         let uu___187_39 = r  in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___187_39.FStar_Range.use_range)
                         }  in
                       let uu____40 =
                         let uu____41 = FStar_Range.file_of_range r'  in
                         let uu____42 =
                           let uu____43 = FStar_TypeChecker_Env.get_range env
                              in
                           FStar_Range.file_of_range uu____43  in
                         uu____41 <> uu____42  in
                       if uu____40
                       then
                         let uu____46 =
                           let uu____47 =
                             let uu____48 =
                               let uu____49 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.strcat uu____49 ")"  in
                             Prims.strcat "(Also see: " uu____48  in
                           Prims.strcat msg uu____47  in
                         let uu____50 = FStar_TypeChecker_Env.get_range env
                            in
                         (uu____46, uu____50)
                       else (msg, r))))
         in
      FStar_Errors.add_errors errs1
  
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
            let uu____67 =
              FStar_Options.set_options FStar_Options.Set
                "--prn --print_universes"
               in
            let s11 = FStar_TypeChecker_Normalize.term_to_string env t1  in
            let s21 = FStar_TypeChecker_Normalize.term_to_string env t2  in
            FStar_Util.format2
              "\nMore precisely: expected type:\n%s\ngot:\n%s\n" s11 s21
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
          let uu____83 = possibly_verbose_message env t2 t1  in
          match uu____83 with
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
        let uu____99 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____99
  
let expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____112 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____113 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____112 uu____113 msg
  
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
          let uu____126 = FStar_TypeChecker_Normalize.term_to_string env t1
             in
          let uu____127 = FStar_Syntax_Print.term_to_string e  in
          let uu____128 = FStar_TypeChecker_Normalize.term_to_string env t2
             in
          FStar_Util.format3
            "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
            uu____126 uu____127 uu____128
  
let expected_function_with_parameter_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____140 = FStar_TypeChecker_Normalize.term_to_string env t1  in
        let uu____141 = FStar_TypeChecker_Normalize.term_to_string env t2  in
        FStar_Util.format3
          "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
          uu____140 uu____141
  
let expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____154 = FStar_TypeChecker_Normalize.term_to_string env t1
             in
          let uu____155 = FStar_Syntax_Print.term_to_string e  in
          let uu____156 = FStar_TypeChecker_Normalize.term_to_string env t2
             in
          FStar_Util.format3
            "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
            uu____154 uu____155 uu____156
  
let basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____171 = possibly_verbose_message env t1 t2  in
          match uu____171 with
          | (s1,s2,extra) ->
              (match eopt with
               | None  ->
                   FStar_Util.format3
                     "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra
               | Some e ->
                   let uu____179 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.format4
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1
                     uu____179 s2 extra)
  
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
        let uu____189 = FStar_TypeChecker_Normalize.term_to_string env k1  in
        let uu____190 = FStar_TypeChecker_Normalize.term_to_string env k2  in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____189 uu____190
  
let constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____203 = FStar_Syntax_Print.term_to_string d  in
          let uu____204 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____205 = FStar_TypeChecker_Normalize.term_to_string env t'
             in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____203 uu____204 uu____205
  
let constructor_fails_the_positivity_check env d l =
  let uu____223 = FStar_Syntax_Print.term_to_string d  in
  let uu____224 = FStar_Syntax_Print.lid_to_string l  in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    uu____223 uu____224
  
let inline_type_annotation_and_val_decl : FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____228 = FStar_Syntax_Print.lid_to_string l  in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____228
  
let inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____238 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let uu____239 = FStar_Syntax_Print.bv_to_string x  in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____238 uu____239
  
let expected_typ_of_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun k1  ->
      fun t  ->
        fun k2  ->
          let uu____252 = FStar_TypeChecker_Normalize.term_to_string env k1
             in
          let uu____253 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____254 = FStar_TypeChecker_Normalize.term_to_string env k2
             in
          FStar_Util.format3
            "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\""
            uu____252 uu____253 uu____254
  
let expected_tcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____264 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let uu____265 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____264 uu____265
  
let expected_dcon_kind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____275 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let uu____276 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\""
          uu____275 uu____276
  
let expected_function_typ :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____283 = FStar_TypeChecker_Normalize.term_to_string env t  in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____283
  
let expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____296 = FStar_Syntax_Print.term_to_string f  in
          let uu____297 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____298 = FStar_TypeChecker_Normalize.term_to_string env targ
             in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____296 uu____297 uu____298
  
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
      let vars v3 =
        let uu____319 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____319 (FStar_String.concat ", ")  in
      let uu____324 = vars v1  in
      let uu____325 = vars v2  in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____324 uu____325
  
let name_and_result :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (Prims.string * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____345) -> ("Tot", t)
      | FStar_Syntax_Syntax.GTotal (t,uu____355) -> ("GTot", t)
      | FStar_Syntax_Syntax.Comp ct ->
          let uu____365 =
            FStar_Syntax_Print.lid_to_string
              ct.FStar_Syntax_Syntax.comp_typ_name
             in
          let uu____366 = FStar_TypeChecker_Env.result_typ env c  in
          (uu____365, uu____366)
  
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____397 = name_and_result env c  in
  match uu____397 with
  | (f1,r1) ->
      let uu____408 = name_and_result env c'  in
      (match uu____408 with
       | (f2,r2) ->
           let uu____419 = FStar_TypeChecker_Normalize.term_to_string env r1
              in
           let uu____420 = FStar_TypeChecker_Normalize.term_to_string env r2
              in
           FStar_Util.format4
             "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
             uu____419 f1 uu____420 f2)
  
let unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____427 = FStar_TypeChecker_Normalize.term_to_string env f  in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____427
  
let expected_pure_expression e c =
  let uu____444 = FStar_Syntax_Print.term_to_string e  in
  let uu____445 =
    FStar_Ident.string_of_lid (FStar_Syntax_Util.comp_effect_name c)  in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    uu____444 uu____445
  
let expected_ghost_expression e c =
  let uu____462 = FStar_Syntax_Print.term_to_string e  in
  let uu____463 =
    FStar_Ident.string_of_lid (FStar_Syntax_Util.comp_effect_name c)  in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    uu____462 uu____463
  
let expected_effect_1_got_effect_2 :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____470 = FStar_Syntax_Print.lid_to_string c1  in
      let uu____471 = FStar_Syntax_Print.lid_to_string c2  in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____470 uu____471
  
let failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____480 = FStar_Syntax_Print.lbname_to_string l  in
      let uu____481 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
         in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____480 uu____481
  
let failed_to_prove_specification : Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____488 ->
        let uu____490 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____490
  
let top_level_effect : Prims.string =
  "Top-level let-bindings must be total; this term may have effects" 
let cardinality_constraint_violated l a =
  let uu____508 = FStar_Syntax_Print.lid_to_string l  in
  let uu____509 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
  FStar_Util.format2
    "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
    uu____508 uu____509
  