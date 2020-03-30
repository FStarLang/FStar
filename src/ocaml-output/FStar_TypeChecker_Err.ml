open Prims
let (info_at_pos :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.int ->
        Prims.int ->
          ((Prims.string,FStar_Ident.lid) FStar_Util.either *
            FStar_Syntax_Syntax.typ * FStar_Range.range)
            FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun file  ->
      fun row  ->
        fun col  ->
          let uu____39 =
            let uu____42 =
              FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info  in
            FStar_TypeChecker_Common.id_info_at_pos uu____42 file row col  in
          match uu____39 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some info ->
              (match info.FStar_TypeChecker_Common.identifier with
               | FStar_Util.Inl bv ->
                   let uu____101 =
                     let uu____113 =
                       let uu____119 = FStar_Syntax_Print.nm_to_string bv  in
                       FStar_Util.Inl uu____119  in
                     let uu____122 = FStar_Syntax_Syntax.range_of_bv bv  in
                     (uu____113,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____122)
                      in
                   FStar_Pervasives_Native.Some uu____101
               | FStar_Util.Inr fv ->
                   let uu____140 =
                     let uu____152 =
                       let uu____158 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Util.Inr uu____158  in
                     let uu____160 = FStar_Syntax_Syntax.range_of_fv fv  in
                     (uu____152,
                       (info.FStar_TypeChecker_Common.identifier_ty),
                       uu____160)
                      in
                   FStar_Pervasives_Native.Some uu____140)
  
let print_discrepancy :
  'a . ('a -> Prims.string) -> 'a -> 'a -> (Prims.string * Prims.string) =
  fun f  ->
    fun x  ->
      fun y  ->
        let print7 uu____229 =
          let xs = f x  in let ys = f y  in (xs, ys, (xs <> ys))  in
        let rec blist_leq l1 l2 =
          match (l1, l2) with
          | (h1::t1,h2::t2) ->
              ((Prims.op_Negation h1) || h2) && (blist_leq t1 t2)
          | ([],[]) -> true
          | uu____307 -> failwith "print_discrepancy: bad lists"  in
        let rec succ l =
          match l with
          | (false )::t -> true :: t
          | (true )::t -> let uu____352 = succ t  in false :: uu____352
          | [] -> failwith ""  in
        let full l = FStar_List.for_all (fun b  -> b) l  in
        let get_bool_option s =
          let uu____391 = FStar_Options.get_option s  in
          match uu____391 with
          | FStar_Options.Bool b -> b
          | uu____395 -> failwith "print_discrepancy: impossible"  in
        let set_bool_option s b =
          FStar_Options.set_option s (FStar_Options.Bool b)  in
        let get1 uu____421 =
          let pi = get_bool_option "print_implicits"  in
          let pu = get_bool_option "print_universes"  in
          let pea = get_bool_option "print_effect_args"  in
          let pf = get_bool_option "print_full_names"  in [pi; pu; pea; pf]
           in
        let set1 l =
          let uu____454 = l  in
          match uu____454 with
          | pi::pu::pea::pf::[] ->
              (set_bool_option "print_implicits" pi;
               set_bool_option "print_universes" pu;
               set_bool_option "print_effect_args" pea;
               set_bool_option "print_full_names " pf)
           in
        let bas = get1 ()  in
        let rec go cur =
          match () with
          | () when full cur ->
              let uu____506 = print7 ()  in
              (match uu____506 with | (xs,ys,uu____524) -> (xs, ys))
          | () when
              let uu____533 = blist_leq bas cur  in
              Prims.op_Negation uu____533 ->
              let uu____535 = succ cur  in go uu____535
          | () ->
              (set1 cur;
               (let uu____540 = print7 ()  in
                match uu____540 with
                | (xs,ys,true ) -> (xs, ys)
                | uu____566 -> let uu____576 = succ cur  in go uu____576))
           in
        FStar_Options.with_saved_options (fun uu____587  -> go bas)
  
let errors_smt_detail :
  'Auu____597 .
    FStar_TypeChecker_Env.env ->
      ('Auu____597 * Prims.string * FStar_Range.range) Prims.list ->
        (Prims.string,Prims.string) FStar_Util.either ->
          ('Auu____597 * Prims.string * FStar_Range.range) Prims.list
  =
  fun env  ->
    fun errs  ->
      fun smt_detail  ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Util.Inr d -> Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
          | FStar_Util.Inl d when (FStar_Util.trim_string d) <> "" ->
              Prims.op_Hat msg (Prims.op_Hat "; " d)
          | uu____674 -> msg  in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu____731  ->
                  match uu____731 with
                  | (e,msg,r) ->
                      let uu____751 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu____767 = FStar_TypeChecker_Env.get_range env
                             in
                          (e, msg, uu____767)
                        else
                          (let r' =
                             let uu____772 = FStar_Range.use_range r  in
                             FStar_Range.set_def_range r uu____772  in
                           let uu____773 =
                             let uu____775 = FStar_Range.file_of_range r'  in
                             let uu____777 =
                               let uu____779 =
                                 FStar_TypeChecker_Env.get_range env  in
                               FStar_Range.file_of_range uu____779  in
                             uu____775 <> uu____777  in
                           if uu____773
                           then
                             let uu____789 =
                               let uu____791 =
                                 let uu____793 =
                                   let uu____795 =
                                     FStar_Range.string_of_use_range r  in
                                   let uu____797 =
                                     let uu____799 =
                                       let uu____801 =
                                         let uu____803 =
                                           FStar_Range.use_range r  in
                                         let uu____804 =
                                           FStar_Range.def_range r  in
                                         uu____803 <> uu____804  in
                                       if uu____801
                                       then
                                         let uu____807 =
                                           let uu____809 =
                                             FStar_Range.string_of_def_range
                                               r
                                              in
                                           Prims.op_Hat uu____809 ")"  in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu____807
                                       else ""  in
                                     Prims.op_Hat ")" uu____799  in
                                   Prims.op_Hat uu____795 uu____797  in
                                 Prims.op_Hat " (Also see: " uu____793  in
                               Prims.op_Hat msg uu____791  in
                             let uu____818 =
                               FStar_TypeChecker_Env.get_range env  in
                             (e, uu____789, uu____818)
                           else (e, msg, r))
                         in
                      (match uu____751 with
                       | (e1,msg1,r1) ->
                           (e1, (maybe_add_smt_detail msg1), r1))))
           in
        errs1
  
let (add_errors_smt_detail :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      (Prims.string,Prims.string) FStar_Util.either -> unit)
  =
  fun env  ->
    fun errs  ->
      fun smt_detail  ->
        let uu____882 = errors_smt_detail env errs smt_detail  in
        FStar_Errors.add_errors uu____882
  
let (add_errors :
  FStar_TypeChecker_Env.env ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list ->
      unit)
  =
  fun env  -> fun errs  -> add_errors_smt_detail env errs (FStar_Util.Inl "") 
let (err_msg_type_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> (Prims.string * Prims.string))
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        print_discrepancy (FStar_TypeChecker_Normalize.term_to_string env) t1
          t2
  
let (err_msg_comp_strings :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> (Prims.string * Prims.string))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        print_discrepancy (FStar_TypeChecker_Normalize.comp_to_string env) c1
          c2
  
let (exhaustiveness_check : Prims.string) = "Patterns are incomplete" 
let (subtyping_failed :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> unit -> Prims.string)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun uu____1004  ->
          let uu____1005 = err_msg_type_strings env t1 t2  in
          match uu____1005 with
          | (s1,s2) ->
              FStar_Util.format2
                "Subtyping check failed; expected type %s; got type %s" s2 s1
  
let (ill_kinded_type : Prims.string) = "Ill-kinded type" 
let (totality_check : Prims.string) = "This term may not terminate" 
let (unexpected_signature_for_monad :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun m  ->
      fun k  ->
        let uu____1047 =
          let uu____1049 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____1049
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____1047)
  
let (expected_a_term_of_type_t_got_a_function :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun msg  ->
      fun t  ->
        fun e  ->
          let uu____1081 =
            let uu____1083 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1085 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____1083 uu____1085 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____1081)
  
let (unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string))
  =
  (FStar_Errors.Fatal_UnexpectedImplicitArgument,
    "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments")
  
let (expected_expression_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____1123 = err_msg_type_strings env t1 t2  in
          match uu____1123 with
          | (s1,s2) ->
              let uu____1141 =
                let uu____1143 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____1143 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____1141)
  
let (expected_pattern_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t1  ->
      fun e  ->
        fun t2  ->
          let uu____1173 = err_msg_type_strings env t1 t2  in
          match uu____1173 with
          | (s1,s2) ->
              let uu____1191 =
                let uu____1193 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____1193 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____1191)
  
let (basic_type_error :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun eopt  ->
      fun t1  ->
        fun t2  ->
          let uu____1227 = err_msg_type_strings env t1 t2  in
          match uu____1227 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____1250 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____1250 s2
                 in
              (FStar_Errors.Error_TypeError, msg)
  
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
  
let constructor_fails_the_positivity_check :
  'Auu____1271 .
    'Auu____1271 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____1292 =
          let uu____1294 = FStar_Syntax_Print.term_to_string d  in
          let uu____1296 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____1294 uu____1296
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____1292)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____1311 =
      let uu____1313 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____1313
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____1311)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____1338 =
          let uu____1340 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____1342 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____1340 uu____1342
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____1338)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____1362 =
        let uu____1364 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____1364
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____1362)
  
let (expected_poly_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      fun t  ->
        fun targ  ->
          let uu____1394 =
            let uu____1396 = FStar_Syntax_Print.term_to_string f  in
            let uu____1398 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1400 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____1396 uu____1398 uu____1400
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____1394)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____1439 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____1439 (FStar_String.concat ", ")  in
      let uu____1454 =
        let uu____1456 = vars v1  in
        let uu____1458 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____1456 uu____1458
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____1454)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1487) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____1501) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____1515 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____1515, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____1531 .
    FStar_TypeChecker_Env.env ->
      'Auu____1531 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1565 = name_and_result c  in
          match uu____1565 with
          | (f1,r1) ->
              let uu____1586 = name_and_result c'  in
              (match uu____1586 with
               | (f2,r2) ->
                   let uu____1607 = err_msg_type_strings env r1 r2  in
                   (match uu____1607 with
                    | (s1,s2) ->
                        let uu____1625 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1625)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____1640 .
    FStar_TypeChecker_Env.env ->
      'Auu____1640 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1666 = err_msg_comp_strings env c c'  in
          match uu____1666 with
          | (s1,s2) ->
              let uu____1684 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1684)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____1704 =
        let uu____1706 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1706
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1704)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1730 =
        let uu____1732 = FStar_Syntax_Print.term_to_string e  in
        let uu____1734 =
          let uu____1736 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1736  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____1732 uu____1734
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____1730)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1777 =
        let uu____1779 = FStar_Syntax_Print.term_to_string e  in
        let uu____1781 =
          let uu____1783 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1783  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1779 uu____1781
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1777)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____1820 =
        let uu____1822 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____1824 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1822 uu____1824
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1820)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____1850 =
        let uu____1852 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____1854 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1852 uu____1854
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1850)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1885 ->
          let uu____1889 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1889
       in
    (FStar_Errors.Error_TypeCheckerFailToProve, msg)
  
let (top_level_effect : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Warning_TopLevelEffect,
    "Top-level let-bindings must be total; this term may have effects")
  
let (cardinality_constraint_violated :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun a  ->
      let uu____1926 =
        let uu____1928 = FStar_Syntax_Print.lid_to_string l  in
        let uu____1930 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1928 uu____1930
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1926)
  