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
          match l with
          | pi::pu::pea::pf::[] ->
              (set_bool_option "print_implicits" pi;
               set_bool_option "print_universes" pu;
               set_bool_option "print_effect_args" pea;
               set_bool_option "print_full_names " pf)
          | uu____474 -> failwith "impossible: print_discrepancy"  in
        let bas = get1 ()  in
        let rec go cur =
          match () with
          | () when full cur ->
              let uu____507 = print7 ()  in
              (match uu____507 with | (xs,ys,uu____525) -> (xs, ys))
          | () when
              let uu____534 = blist_leq bas cur  in
              Prims.op_Negation uu____534 ->
              let uu____536 = succ cur  in go uu____536
          | () ->
              (set1 cur;
               (let uu____541 = print7 ()  in
                match uu____541 with
                | (xs,ys,true ) -> (xs, ys)
                | uu____567 -> let uu____577 = succ cur  in go uu____577))
           in
        FStar_Options.with_saved_options (fun uu____588  -> go bas)
  
let errors_smt_detail :
  'Auu____598 .
    FStar_TypeChecker_Env.env ->
      ('Auu____598 * Prims.string * FStar_Range.range) Prims.list ->
        (Prims.string,Prims.string) FStar_Util.either ->
          ('Auu____598 * Prims.string * FStar_Range.range) Prims.list
  =
  fun env  ->
    fun errs  ->
      fun smt_detail  ->
        let maybe_add_smt_detail msg =
          match smt_detail with
          | FStar_Util.Inr d -> Prims.op_Hat msg (Prims.op_Hat "\n\t" d)
          | FStar_Util.Inl d when (FStar_Util.trim_string d) <> "" ->
              Prims.op_Hat msg (Prims.op_Hat "; " d)
          | uu____675 -> msg  in
        let errs1 =
          FStar_All.pipe_right errs
            (FStar_List.map
               (fun uu____732  ->
                  match uu____732 with
                  | (e,msg,r) ->
                      let uu____752 =
                        if r = FStar_Range.dummyRange
                        then
                          let uu____768 = FStar_TypeChecker_Env.get_range env
                             in
                          (e, msg, uu____768)
                        else
                          (let r' =
                             let uu____773 = FStar_Range.use_range r  in
                             FStar_Range.set_def_range r uu____773  in
                           let uu____774 =
                             let uu____776 = FStar_Range.file_of_range r'  in
                             let uu____778 =
                               let uu____780 =
                                 FStar_TypeChecker_Env.get_range env  in
                               FStar_Range.file_of_range uu____780  in
                             uu____776 <> uu____778  in
                           if uu____774
                           then
                             let uu____790 =
                               let uu____792 =
                                 let uu____794 =
                                   let uu____796 =
                                     FStar_Range.string_of_use_range r  in
                                   let uu____798 =
                                     let uu____800 =
                                       let uu____802 =
                                         let uu____804 =
                                           FStar_Range.use_range r  in
                                         let uu____805 =
                                           FStar_Range.def_range r  in
                                         uu____804 <> uu____805  in
                                       if uu____802
                                       then
                                         let uu____808 =
                                           let uu____810 =
                                             FStar_Range.string_of_def_range
                                               r
                                              in
                                           Prims.op_Hat uu____810 ")"  in
                                         Prims.op_Hat
                                           "(Other related locations: "
                                           uu____808
                                       else ""  in
                                     Prims.op_Hat ")" uu____800  in
                                   Prims.op_Hat uu____796 uu____798  in
                                 Prims.op_Hat " (Also see: " uu____794  in
                               Prims.op_Hat msg uu____792  in
                             let uu____819 =
                               FStar_TypeChecker_Env.get_range env  in
                             (e, uu____790, uu____819)
                           else (e, msg, r))
                         in
                      (match uu____752 with
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
        let uu____883 = errors_smt_detail env errs smt_detail  in
        FStar_Errors.add_errors uu____883
  
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
        fun uu____1005  ->
          let uu____1006 = err_msg_type_strings env t1 t2  in
          match uu____1006 with
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
        let uu____1048 =
          let uu____1050 = FStar_TypeChecker_Normalize.term_to_string env k
             in
          FStar_Util.format2
            "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s"
            m.FStar_Ident.str uu____1050
           in
        (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____1048)
  
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
          let uu____1082 =
            let uu____1084 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1086 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Expected a term of type \"%s\"; got a function \"%s\" (%s)"
              uu____1084 uu____1086 msg
             in
          (FStar_Errors.Fatal_ExpectTermGotFunction, uu____1082)
  
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
          let uu____1124 = err_msg_type_strings env t1 t2  in
          match uu____1124 with
          | (s1,s2) ->
              let uu____1142 =
                let uu____1144 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\""
                  s1 uu____1144 s2
                 in
              (FStar_Errors.Fatal_UnexpectedExpressionType, uu____1142)
  
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
          let uu____1174 = err_msg_type_strings env t1 t2  in
          match uu____1174 with
          | (s1,s2) ->
              let uu____1192 =
                let uu____1194 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format3
                  "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\""
                  s1 uu____1194 s2
                 in
              (FStar_Errors.Fatal_UnexpectedPattern, uu____1192)
  
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
          let uu____1228 = err_msg_type_strings env t1 t2  in
          match uu____1228 with
          | (s1,s2) ->
              let msg =
                match eopt with
                | FStar_Pervasives_Native.None  ->
                    FStar_Util.format2
                      "Expected type \"%s\"; got type \"%s\"" s1 s2
                | FStar_Pervasives_Native.Some e ->
                    let uu____1251 =
                      FStar_TypeChecker_Normalize.term_to_string env e  in
                    FStar_Util.format3
                      "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1
                      uu____1251 s2
                 in
              (FStar_Errors.Error_TypeError, msg)
  
let (occurs_check : (FStar_Errors.raw_error * Prims.string)) =
  (FStar_Errors.Fatal_PossibleInfiniteTyp,
    "Possibly infinite typ (occurs check failed)")
  
let constructor_fails_the_positivity_check :
  'Auu____1272 .
    'Auu____1272 ->
      FStar_Syntax_Syntax.term ->
        FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun d  ->
      fun l  ->
        let uu____1293 =
          let uu____1295 = FStar_Syntax_Print.term_to_string d  in
          let uu____1297 = FStar_Syntax_Print.lid_to_string l  in
          FStar_Util.format2
            "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type"
            uu____1295 uu____1297
           in
        (FStar_Errors.Fatal_ConstructorFailedCheck, uu____1293)
  
let (inline_type_annotation_and_val_decl :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____1312 =
      let uu____1314 = FStar_Syntax_Print.lid_to_string l  in
      FStar_Util.format1
        "\"%s\" has a val declaration as well as an inlined type annotation; remove one"
        uu____1314
       in
    (FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl, uu____1312)
  
let (inferred_type_causes_variable_to_escape :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        let uu____1339 =
          let uu____1341 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          let uu____1343 = FStar_Syntax_Print.bv_to_string x  in
          FStar_Util.format2
            "Inferred type \"%s\" causes variable \"%s\" to escape its scope"
            uu____1341 uu____1343
           in
        (FStar_Errors.Fatal_InferredTypeCauseVarEscape, uu____1339)
  
let (expected_function_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun t  ->
      let uu____1363 =
        let uu____1365 = FStar_TypeChecker_Normalize.term_to_string env t  in
        FStar_Util.format1
          "Expected a function; got an expression of type \"%s\"" uu____1365
         in
      (FStar_Errors.Fatal_FunctionTypeExpected, uu____1363)
  
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
          let uu____1395 =
            let uu____1397 = FStar_Syntax_Print.term_to_string f  in
            let uu____1399 = FStar_TypeChecker_Normalize.term_to_string env t
               in
            let uu____1401 =
              FStar_TypeChecker_Normalize.term_to_string env targ  in
            FStar_Util.format3
              "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\""
              uu____1397 uu____1399 uu____1401
             in
          (FStar_Errors.Fatal_PolyTypeExpected, uu____1395)
  
let (disjunctive_pattern_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.bv Prims.list ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun v1  ->
    fun v2  ->
      let vars v3 =
        let uu____1440 =
          FStar_All.pipe_right v3
            (FStar_List.map FStar_Syntax_Print.bv_to_string)
           in
        FStar_All.pipe_right uu____1440 (FStar_String.concat ", ")  in
      let uu____1455 =
        let uu____1457 = vars v1  in
        let uu____1459 = vars v2  in
        FStar_Util.format2
          "Every alternative of an 'or' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")"
          uu____1457 uu____1459
         in
      (FStar_Errors.Fatal_DisjuctivePatternVarsMismatch, uu____1455)
  
let (name_and_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax))
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1488) -> ("Tot", t)
    | FStar_Syntax_Syntax.GTotal (t,uu____1502) -> ("GTot", t)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____1516 =
          FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name
           in
        (uu____1516, (ct.FStar_Syntax_Syntax.result_typ))
  
let computed_computation_type_does_not_match_annotation :
  'Auu____1532 .
    FStar_TypeChecker_Env.env ->
      'Auu____1532 ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
            (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1566 = name_and_result c  in
          match uu____1566 with
          | (f1,r1) ->
              let uu____1587 = name_and_result c'  in
              (match uu____1587 with
               | (f2,r2) ->
                   let uu____1608 = err_msg_type_strings env r1 r2  in
                   (match uu____1608 with
                    | (s1,s2) ->
                        let uu____1626 =
                          FStar_Util.format4
                            "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\""
                            s1 f1 s2 f2
                           in
                        (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation,
                          uu____1626)))
  
let computed_computation_type_does_not_match_annotation_eq :
  'Auu____1641 .
    FStar_TypeChecker_Env.env ->
      'Auu____1641 ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.comp -> (FStar_Errors.raw_error * Prims.string)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____1667 = err_msg_comp_strings env c c'  in
          match uu____1667 with
          | (s1,s2) ->
              let uu____1685 =
                FStar_Util.format2
                  "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed"
                  s1 s2
                 in
              (FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation, uu____1685)
  
let (unexpected_non_trivial_precondition_on_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> (FStar_Errors.raw_error * Prims.string))
  =
  fun env  ->
    fun f  ->
      let uu____1705 =
        let uu____1707 = FStar_TypeChecker_Normalize.term_to_string env f  in
        FStar_Util.format1
          "Term has an unexpected non-trivial pre-condition: %s" uu____1707
         in
      (FStar_Errors.Fatal_UnExpectedPreCondition, uu____1705)
  
let (expected_pure_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1731 =
        let uu____1733 = FStar_Syntax_Print.term_to_string e  in
        let uu____1735 =
          let uu____1737 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1737  in
        FStar_Util.format2
          "Expected a pure expression; got an expression \"%s\" with effect \"%s\""
          uu____1733 uu____1735
         in
      (FStar_Errors.Fatal_ExpectedPureExpression, uu____1731)
  
let (expected_ghost_expression :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      (FStar_Errors.raw_error * Prims.string))
  =
  fun e  ->
    fun c  ->
      let uu____1778 =
        let uu____1780 = FStar_Syntax_Print.term_to_string e  in
        let uu____1782 =
          let uu____1784 = name_and_result c  in
          FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1784  in
        FStar_Util.format2
          "Expected a ghost expression; got an expression \"%s\" with effect \"%s\""
          uu____1780 uu____1782
         in
      (FStar_Errors.Fatal_ExpectedGhostExpression, uu____1778)
  
let (expected_effect_1_got_effect_2 :
  FStar_Ident.lident ->
    FStar_Ident.lident -> (FStar_Errors.raw_error * Prims.string))
  =
  fun c1  ->
    fun c2  ->
      let uu____1821 =
        let uu____1823 = FStar_Syntax_Print.lid_to_string c1  in
        let uu____1825 = FStar_Syntax_Print.lid_to_string c2  in
        FStar_Util.format2
          "Expected a computation with effect %s; but it has effect %s"
          uu____1823 uu____1825
         in
      (FStar_Errors.Fatal_UnexpectedEffect, uu____1821)
  
let (failed_to_prove_specification_of :
  FStar_Syntax_Syntax.lbname ->
    Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string))
  =
  fun l  ->
    fun lbls  ->
      let uu____1851 =
        let uu____1853 = FStar_Syntax_Print.lbname_to_string l  in
        let uu____1855 = FStar_All.pipe_right lbls (FStar_String.concat ", ")
           in
        FStar_Util.format2
          "Failed to prove specification of %s; assertions at [%s] may fail"
          uu____1853 uu____1855
         in
      (FStar_Errors.Error_TypeCheckerFailToProve, uu____1851)
  
let (failed_to_prove_specification :
  Prims.string Prims.list -> (FStar_Errors.raw_error * Prims.string)) =
  fun lbls  ->
    let msg =
      match lbls with
      | [] ->
          "An unknown assertion in the term at this location was not provable"
      | uu____1886 ->
          let uu____1890 =
            FStar_All.pipe_right lbls (FStar_String.concat "\n\t")  in
          FStar_Util.format1 "The following problems were found:\n\t%s"
            uu____1890
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
      let uu____1927 =
        let uu____1929 = FStar_Syntax_Print.lid_to_string l  in
        let uu____1931 =
          FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format2
          "Constructor %s violates the cardinality of Type at parameter '%s'; type arguments are not allowed"
          uu____1929 uu____1931
         in
      (FStar_Errors.Fatal_CardinalityConstraintViolated, uu____1927)
  