open Prims
let info_at_pos env file row col =
  let uu____34 = FStar_TypeChecker_Common.info_at_pos file row col  in
  match uu____34 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some info ->
      (match info.FStar_TypeChecker_Common.identifier with
       | FStar_Util.Inl bv ->
           let uu____55 =
             let uu____61 =
               let uu____64 = FStar_Syntax_Print.nm_to_string bv  in
               FStar_Util.Inl uu____64  in
             let uu____65 = FStar_Syntax_Syntax.range_of_bv bv  in
             (uu____61, (info.FStar_TypeChecker_Common.identifier_ty),
               uu____65)
              in
           FStar_Pervasives_Native.Some uu____55
       | FStar_Util.Inr fv ->
           let uu____74 =
             let uu____80 =
               let uu____83 = FStar_Syntax_Syntax.lid_of_fv fv  in
               FStar_Util.Inr uu____83  in
             let uu____84 = FStar_Syntax_Syntax.range_of_fv fv  in
             (uu____80, (info.FStar_TypeChecker_Common.identifier_ty),
               uu____84)
              in
           FStar_Pervasives_Native.Some uu____74)
  
let add_errors :
  FStar_TypeChecker_Env.env ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.unit
  =
  fun env  ->
    fun errs  ->
      let errs1 =
        FStar_All.pipe_right errs
          (FStar_List.map
             (fun uu____124  ->
                match uu____124 with
                | (msg,r) ->
                    if r = FStar_Range.dummyRange
                    then
                      let uu____133 = FStar_TypeChecker_Env.get_range env  in
                      (msg, uu____133)
                    else
                      (let r' =
                         let uu___235_136 = r  in
                         {
                           FStar_Range.def_range = (r.FStar_Range.use_range);
                           FStar_Range.use_range =
                             (uu___235_136.FStar_Range.use_range)
                         }  in
                       let uu____137 =
                         let uu____138 = FStar_Range.file_of_range r'  in
                         let uu____139 =
                           let uu____140 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.file_of_range uu____140  in
                         uu____138 <> uu____139  in
                       if uu____137
                       then
                         let uu____143 =
                           let uu____144 =
                             let uu____145 =
                               let uu____146 =
                                 FStar_Range.string_of_use_range r  in
                               Prims.strcat uu____146 ")"  in
                             Prims.strcat "(Also see: " uu____145  in
                           Prims.strcat msg uu____144  in
                         let uu____147 = FStar_TypeChecker_Env.get_range env
                            in
                         (uu____143, uu____147)
                       else (msg, r))))
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
            (fun uu____175  ->
               (let uu____177 =
                  FStar_Options.set_options FStar_Options.Set
                    "--print_full_names --print_universes"
                   in
                ());
               (let uu____178 =
                  FStar_TypeChecker_Normalize.term_to_string env t1  in
                let uu____179 =
                  FStar_TypeChecker_Normalize.term_to_string env t2  in
                (uu____178, uu____179)))
        else (s1, s2)
  
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
          let uu____197 = err_msg_type_strings env t1 t2  in
          match uu____197 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
  
let ill_kinded_type : Prims.string = "Ill-kinded type" 
let totality_check : Prims.string = "This term may not terminate" 
let unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____214 = FStar_TypeChecker_Normalize.term_to_string env k  in
        FStar_Util.format2
          "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
          m.FStar_Ident.str uu____214
  
let expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____231 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____232 = FStar_Syntax_Print.term_to_string e  in
          FStar_Util.format3
            "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
            uu____231 uu____232 msg
  
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
          let uu____249 = err_msg_type_strings env t1 t2  in
          match uu____249 with
          | (s1,s2) ->
              let uu____254 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format3
                "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                s1 uu____254 s2
  
let expected_function_with_parameter_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.string -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____269 = err_msg_type_strings env t1 t2  in
        match uu____269 with
        | (s1,s2) ->
            FStar_Util.format3
              "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\""
              s1 s2
  
let expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____292 = err_msg_type_strings env t1 t2  in
          match uu____292 with
          | (s1,s2) ->
              let uu____297 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format3
                "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                s1 uu____297 s2
  
let basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____316 = err_msg_type_strings env t1 t2  in
          match uu____316 with
          | (s1,s2) ->
              (match eopt with
               | FStar_Pervasives_Native.None  ->
                   FStar_Util.format2 "Expected type \"%s\"; got type \"%s\""
                     s1 s2
               | FStar_Pervasives_Native.Some e ->
                   let uu____322 = FStar_Syntax_Print.term_to_string e  in
                   FStar_Util.format3
                     "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                     uu____322 s2)
  
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
        let uu____335 = FStar_TypeChecker_Normalize.term_to_string env k1  in
        let uu____336 = FStar_TypeChecker_Normalize.term_to_string env k2  in
        FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible"
          uu____335 uu____336
  
let constructor_builds_the_wrong_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun t  ->
        fun t'  ->
          let uu____353 = FStar_Syntax_Print.term_to_string d  in
          let uu____354 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____355 = FStar_TypeChecker_Normalize.term_to_string env t'
             in
          FStar_Util.format3
            "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\""
            uu____353 uu____354 uu____355
  
let constructor_fails_the_positivity_check env d l =
  let uu____377 = FStar_Syntax_Print.term_to_string d  in
  let uu____378 = FStar_Syntax_Print.lid_to_string l  in
  FStar_Util.format2
    "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
    uu____377 uu____378
  
let inline_type_annotation_and_val_decl : FStar_Ident.lid -> Prims.string =
  fun l  ->
    let uu____383 = FStar_Syntax_Print.lid_to_string l  in
    FStar_Util.format1
      "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
      uu____383
  
let inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv -> Prims.string
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____396 = FStar_TypeChecker_Normalize.term_to_string env t  in
        let uu____397 = FStar_Syntax_Print.bv_to_string x  in
        FStar_Util.format2
          "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
          uu____396 uu____397
  
let expected_function_typ :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let uu____406 = FStar_TypeChecker_Normalize.term_to_string env t  in
      FStar_Util.format1
        "Expected a function; got an expression of type \"%s\"" uu____406
  
let expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.string
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____423 = FStar_Syntax_Print.term_to_string f  in
          let uu____424 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____425 = FStar_TypeChecker_Normalize.term_to_string env targ
             in
          FStar_Util.format3
            "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
            uu____423 uu____424 uu____425
  
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
        let uu____449 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____449 (FStar_String.concat ", ")  in
      let uu____454 = vars v1  in
      let uu____455 = vars v2  in
      FStar_Util.format2
        "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
        uu____454 uu____455
  
let name_and_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____474) -> ("Tot", t)
  | FStar_Syntax_Syntax.GTotal (t,uu____484) -> ("GTot", t)
  | FStar_Syntax_Syntax.Comp ct ->
      let uu____494 =
        FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
         in
      (uu____494, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation env e c c' =
  let uu____538 = name_and_result c  in
  match uu____538 with
  | (f1,r1) ->
      let uu____549 = name_and_result c'  in
      (match uu____549 with
       | (f2,r2) ->
           let uu____560 = err_msg_type_strings env r1 r2  in
           (match uu____560 with
            | (s1,s2) ->
                FStar_Util.format4
                  "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                  s1 f1 s2 f2))
  
let unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun f  ->
      let uu____573 = FStar_TypeChecker_Normalize.term_to_string env f  in
      FStar_Util.format1
        "Term has an unexpected non-trivial pre-condition: %s" uu____573
  
let expected_pure_expression e c =
  let uu____593 = FStar_Syntax_Print.term_to_string e  in
  let uu____594 =
    let uu____595 = name_and_result c  in
    FStar_All.pipe_left FStar_Pervasives_Native.fst uu____595  in
  FStar_Util.format2
    "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
    uu____593 uu____594
  
let expected_ghost_expression e c =
  let uu____625 = FStar_Syntax_Print.term_to_string e  in
  let uu____626 =
    let uu____627 = name_and_result c  in
    FStar_All.pipe_left FStar_Pervasives_Native.fst uu____627  in
  FStar_Util.format2
    "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
    uu____625 uu____626
  
let expected_effect_1_got_effect_2 :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.string =
  fun c1  ->
    fun c2  ->
      let uu____646 = FStar_Syntax_Print.lid_to_string c1  in
      let uu____647 = FStar_Syntax_Print.lid_to_string c2  in
      FStar_Util.format2
        "Expected a computation with effect %s; but it has effect %s"
        uu____646 uu____647
  
let failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname -> Prims.string Prims.list -> Prims.string =
  fun l  ->
    fun lbls  ->
      let uu____658 = FStar_Syntax_Print.lbname_to_string l  in
      let uu____659 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
         in
      FStar_Util.format2
        "Failed to prove specification of %s; assertions at [%s] may fail"
        uu____658 uu____659
  
let failed_to_prove_specification : Prims.string Prims.list -> Prims.string =
  fun lbls  ->
    match lbls with
    | [] ->
        "An unknown assertion in the term at this location was not provable"
    | uu____667 ->
        let uu____669 =
          FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
        FStar_Util.format1 "The following problems were found:\n\t%s"
          uu____669
  
let top_level_effect : Prims.string =
  "Top-level let-bindings must be total; this term may have effects" 
let cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun l  ->
    fun a  ->
      let uu____681 = FStar_Syntax_Print.lid_to_string l  in
      let uu____682 = FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v
         in
      FStar_Util.format2
        "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
        uu____681 uu____682
  