open Prims
let (filter_trigger :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun names1  ->
    fun t  ->
      let bvs = FStar_Syntax_Free.names t  in
      let uu____19 = FStar_Util.set_is_subset_of names1 bvs  in
      if uu____19
      then FStar_Pervasives_Native.Some t
      else FStar_Pervasives_Native.None
  
let (has_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun e  ->
      let uu____38 =
        let uu____39 = FStar_Syntax_Subst.compress e  in
        uu____39.FStar_Syntax_Syntax.n  in
      match uu____38 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_TypeChecker_Env.fv_has_attr env fv
            FStar_Parser_Const.smt_theory_symbol_attr_lid
          -> false
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____46;
             FStar_Syntax_Syntax.vars = uu____47;_},uu____48)
          when
          FStar_TypeChecker_Env.fv_has_attr env fv
            FStar_Parser_Const.smt_theory_symbol_attr_lid
          -> false
      | uu____54 -> true
  
let rec (find_trigger :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv FStar_Util.set ->
      FStar_Syntax_Syntax.term ->
        (Prims.bool * FStar_Syntax_Syntax.term Prims.list))
  =
  fun env  ->
    fun names1  ->
      fun t  ->
        let uu____90 =
          let uu____91 = FStar_Syntax_Subst.compress t  in
          uu____91.FStar_Syntax_Syntax.n  in
        match uu____90 with
        | FStar_Syntax_Syntax.Tm_bvar uu____101 -> (false, [])
        | FStar_Syntax_Syntax.Tm_uvar uu____106 -> (false, [])
        | FStar_Syntax_Syntax.Tm_name uu____123 -> (false, [])
        | FStar_Syntax_Syntax.Tm_constant uu____128 -> (false, [])
        | FStar_Syntax_Syntax.Tm_type uu____133 -> (false, [])
        | FStar_Syntax_Syntax.Tm_lazy uu____138 -> (false, [])
        | FStar_Syntax_Syntax.Tm_unknown  -> (false, [])
        | FStar_Syntax_Syntax.Tm_abs uu____147 -> (true, [])
        | FStar_Syntax_Syntax.Tm_arrow uu____170 -> (true, [])
        | FStar_Syntax_Syntax.Tm_refine uu____189 -> (true, [])
        | FStar_Syntax_Syntax.Tm_match uu____200 -> (true, [])
        | FStar_Syntax_Syntax.Tm_let uu____227 -> (true, [])
        | FStar_Syntax_Syntax.Tm_quoted uu____245 -> (true, [])
        | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____257,uu____258) ->
            find_trigger env names1 t1
        | FStar_Syntax_Syntax.Tm_uinst (t1,uu____300) ->
            find_trigger env names1 t1
        | FStar_Syntax_Syntax.Tm_meta (t1,uu____306) ->
            find_trigger env names1 t1
        | FStar_Syntax_Syntax.Tm_fvar uu____311 ->
            let trigger_killer =
              let uu____314 = has_no_smt_theory_symbols env t  in
              Prims.op_Negation uu____314  in
            (trigger_killer, [])
        | FStar_Syntax_Syntax.Tm_app (e,args) ->
            let uu____345 =
              let uu____346 = FStar_Syntax_Subst.compress e  in
              uu____346.FStar_Syntax_Syntax.n  in
            (match uu____345 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.forall_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.exists_lid)
                 -> (true, [])
             | FStar_Syntax_Syntax.Tm_uinst
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____362;
                    FStar_Syntax_Syntax.vars = uu____363;_},uu____364)
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.forall_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.exists_lid)
                 -> (true, [])
             | uu____373 ->
                 let uu____374 = find_trigger env names1 e  in
                 (match uu____374 with
                  | (trigger_killer,uu____390) ->
                      let uu____397 =
                        FStar_List.fold_left
                          (fun uu____427  ->
                             fun uu____428  ->
                               match (uu____427, uu____428) with
                               | ((k,l),(e1,q)) ->
                                   let uu____489 = find_trigger env names1 e1
                                      in
                                   (match uu____489 with
                                    | (b,c) ->
                                        ((k || b), (FStar_List.append l c))))
                          (trigger_killer, []) args
                         in
                      (match uu____397 with
                       | (trigger_killer1,c) ->
                           let c1 =
                             FStar_All.pipe_right c
                               (FStar_List.choose
                                  (fun t1  -> filter_trigger names1 t1))
                              in
                           let c2 =
                             match c1 with
                             | [] ->
                                 if Prims.op_Negation trigger_killer1
                                 then FStar_List.append c1 [t]
                                 else c1
                             | uu____552 -> c1  in
                           (trigger_killer1, c2))))
        | FStar_Syntax_Syntax.Tm_delayed uu____558 ->
            failwith "Tm_delayed is impossible after compress"
  
let (terms_to_bvs :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun names1  ->
    match names1 with
    | [] -> failwith "Empty bound vars"
    | hd1::tl1 ->
        let uu____610 = FStar_Syntax_Free.names hd1  in
        FStar_List.fold_left
          (fun out  ->
             fun x  ->
               let uu____622 = FStar_Syntax_Free.names x  in
               FStar_Util.set_union out uu____622) uu____610 tl1
  
let (infer_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args Prims.list)
  =
  fun env  ->
    fun names1  ->
      fun t  ->
        (let uu____650 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "PatternInference")
            in
         if uu____650
         then
           let uu____655 = FStar_Syntax_Print.term_to_string t  in
           let uu____657 =
             let uu____659 = FStar_Syntax_Subst.compress t  in
             FStar_Syntax_Print.tag_of_term uu____659  in
           let uu____660 =
             let uu____662 =
               FStar_All.pipe_right names1
                 (FStar_List.map FStar_Syntax_Print.term_to_string)
                in
             FStar_All.pipe_right uu____662 (FStar_String.concat ", ")  in
           FStar_Util.print3 "Infer pattern for : %s (%s) with names: (%s)\n"
             uu____655 uu____657 uu____660
         else ());
        (let bvs = terms_to_bvs names1  in
         let uu____683 = find_trigger env bvs t  in
         match uu____683 with
         | (uu____693,p) ->
             let pats =
               FStar_All.pipe_right p
                 (FStar_List.choose (fun t1  -> filter_trigger bvs t1))
                in
             ((let uu____711 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "PatternInference")
                  in
               if uu____711
               then
                 let uu____716 =
                   let uu____718 =
                     FStar_All.pipe_right pats
                       (FStar_List.map FStar_Syntax_Print.term_to_string)
                      in
                   FStar_All.pipe_right uu____718 (FStar_String.concat "; ")
                    in
                 FStar_Util.print1 "Found patterns: %s\n" uu____716
               else ());
              FStar_List.fold_left
                (fun l  ->
                   fun t1  ->
                     let uu____749 =
                       let uu____754 =
                         let uu____757 = FStar_Syntax_Syntax.as_arg t1  in
                         [uu____757]  in
                       [uu____754]  in
                     FStar_List.append l uu____749) [] pats))
  
let (remove_invalid_pattern :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Syntax_Syntax.args Prims.list ->
      FStar_Syntax_Syntax.args Prims.list)
  =
  fun names1  ->
    fun pats  ->
      match names1 with
      | [] -> pats
      | uu____789 ->
          let bvs = terms_to_bvs names1  in
          let pats1 =
            FStar_List.fold_left
              (fun l  ->
                 fun p  ->
                   let p1 =
                     FStar_List.choose
                       (fun uu____835  ->
                          match uu____835 with
                          | (t,uu____845) -> filter_trigger bvs t) p
                      in
                   FStar_List.append l p1) [] pats
             in
          FStar_List.fold_left
            (fun l  ->
               fun t  ->
                 let uu____863 =
                   let uu____868 =
                     let uu____871 = FStar_Syntax_Syntax.as_arg t  in
                     [uu____871]  in
                   [uu____868]  in
                 FStar_List.append l uu____863) [] pats1
  