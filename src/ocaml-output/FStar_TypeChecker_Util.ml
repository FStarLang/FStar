open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____21 = FStar_TypeChecker_Env.get_range env  in
      let uu____22 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____21 uu____22
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____74 =
          let uu____75 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____75  in
        if uu____74
        then g
        else
          (let uu____77 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____123  ->
                     match uu____123 with
                     | (uu____128,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____77 with
           | (solve_now,defer) ->
               ((let uu____157 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____157
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____168  ->
                         match uu____168 with
                         | (s,p) ->
                             let uu____175 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____175)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____186  ->
                         match uu____186 with
                         | (s,p) ->
                             let uu____193 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____193) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___339_197 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___339_197.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___339_197.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___339_197.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___340_199 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___340_199.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___340_199.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___340_199.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____213 =
        let uu____214 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____214  in
      if uu____213
      then
        let us =
          let uu____216 =
            let uu____219 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____219
             in
          FStar_All.pipe_right uu____216 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____230 =
            let uu____235 =
              let uu____236 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____236
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____235)  in
          FStar_Errors.log_issue r uu____230);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____253  ->
      match uu____253 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____263;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____265;
          FStar_Syntax_Syntax.lbpos = uu____266;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____299 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____299 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____336) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____343) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____398) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____434 = FStar_Options.ml_ish ()  in
                                if uu____434
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____453 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____453
                            then
                              let uu____454 = FStar_Range.string_of_range r
                                 in
                              let uu____455 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____454 uu____455
                            else ());
                           FStar_Util.Inl t2)
                      | uu____457 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____459 = aux e1  in
                      match uu____459 with
                      | FStar_Util.Inr c ->
                          let uu____465 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____465
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____467 =
                               let uu____472 =
                                 let uu____473 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____473
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____472)
                                in
                             FStar_Errors.raise_error uu____467 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____477 ->
               let uu____478 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____478 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____539,FStar_Syntax_Syntax.Tm_uinst (e2,uu____541)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____546,uu____547) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____551 =
                    let uu____552 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____553 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____552 uu____553
                     in
                  failwith uu____551)
               else ();
               (let uu____556 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____556
                then
                  let uu____557 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____558 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____557
                    uu____558
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___341_562 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___341_562.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___341_562.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____566 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____566
                then
                  let uu____567 =
                    let uu____568 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____569 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____568 uu____569
                     in
                  failwith uu____567
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___342_573 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___342_573.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___342_573.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____575),uu____576) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____600 =
                  let uu____601 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____601  in
                if uu____600
                then
                  let uu____602 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____602
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____621;
                FStar_Syntax_Syntax.vars = uu____622;_},args))
              ->
              ((let uu____665 =
                  let uu____666 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____666 Prims.op_Negation  in
                if uu____665
                then
                  let uu____667 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____667
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____809)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____884) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____921) ->
                           let pat =
                             let uu____945 = aux argpat e2  in
                             let uu____948 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____945, uu____948)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____957 ->
                      let uu____980 =
                        let uu____981 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____982 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____981 uu____982
                         in
                      failwith uu____980
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____994;
                     FStar_Syntax_Syntax.vars = uu____995;_},uu____996);
                FStar_Syntax_Syntax.pos = uu____997;
                FStar_Syntax_Syntax.vars = uu____998;_},args))
              ->
              ((let uu____1045 =
                  let uu____1046 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____1046 Prims.op_Negation  in
                if uu____1045
                then
                  let uu____1047 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____1047
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1189)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1264) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____1301) ->
                           let pat =
                             let uu____1325 = aux argpat e2  in
                             let uu____1328 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____1325, uu____1328)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1337 ->
                      let uu____1360 =
                        let uu____1361 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____1362 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1361 uu____1362
                         in
                      failwith uu____1360
                   in
                match_args [] args argpats))
          | uu____1371 ->
              let uu____1376 =
                let uu____1377 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____1378 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____1379 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____1377 uu____1378 uu____1379
                 in
              failwith uu____1376
           in
        aux p exp
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____1422 =
      match uu____1422 with
      | (p,i) ->
          let uu____1439 = decorated_pattern_as_term p  in
          (match uu____1439 with
           | (vars,te) ->
               let uu____1462 =
                 let uu____1467 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____1467)  in
               (vars, uu____1462))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____1481 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____1481)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____1485 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1485)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____1489 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1489)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____1510 =
          let uu____1529 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____1529 FStar_List.unzip  in
        (match uu____1510 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____1665 =
               let uu____1666 =
                 let uu____1667 =
                   let uu____1684 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____1684, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____1667  in
               mk1 uu____1666  in
             (vars1, uu____1665))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____1722,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____1732,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____1746 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1768)::[] -> wp
      | uu____1793 ->
          let uu____1804 =
            let uu____1805 =
              let uu____1806 =
                FStar_List.map
                  (fun uu____1818  ->
                     match uu____1818 with
                     | (x,uu____1826) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____1806 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1805
             in
          failwith uu____1804
       in
    let uu____1833 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1833, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1849 = destruct_comp c  in
        match uu____1849 with
        | (u,uu____1857,wp) ->
            let uu____1859 =
              let uu____1870 =
                let uu____1879 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1879  in
              [uu____1870]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1859;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1911 =
          let uu____1918 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1919 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1918 uu____1919  in
        match uu____1911 with | (m,uu____1921,uu____1922) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1938 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1938
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____1981 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1981 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____2018 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____2018 with
             | (a,kwp) ->
                 let uu____2049 = destruct_comp m1  in
                 let uu____2056 = destruct_comp m2  in
                 ((md, a, kwp), uu____2049, uu____2056))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____2136 =
              let uu____2137 =
                let uu____2148 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2148]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2137;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2136
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          let uu____2230 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2230
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____2242 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____2242
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2245  ->
           let uu____2246 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____2246)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2252 =
      let uu____2253 = FStar_Syntax_Subst.compress t  in
      uu____2253.FStar_Syntax_Syntax.n  in
    match uu____2252 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2256 -> true
    | uu____2271 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____2328 =
                let uu____2329 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2329  in
              if uu____2328
              then f
              else (let uu____2331 = reason1 ()  in label uu____2331 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___343_2348 = g  in
            let uu____2349 =
              let uu____2350 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2350  in
            {
              FStar_TypeChecker_Env.guard_f = uu____2349;
              FStar_TypeChecker_Env.deferred =
                (uu___343_2348.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___343_2348.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___343_2348.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2370 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2370
        then c
        else
          (let uu____2372 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2372
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2433 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2433]  in
                       let us =
                         let uu____2455 =
                           let uu____2458 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2458]  in
                         u_res :: uu____2455  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2464 =
                         let uu____2469 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____2470 =
                           let uu____2471 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____2480 =
                             let uu____2491 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____2500 =
                               let uu____2511 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____2511]  in
                             uu____2491 :: uu____2500  in
                           uu____2471 :: uu____2480  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2469 uu____2470
                          in
                       uu____2464 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2555 = destruct_comp c1  in
              match uu____2555 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____2590  ->
             let uu____2591 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____2591)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___321_2600  ->
            match uu___321_2600 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2601 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____2623 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____2623))
               &&
               (let uu____2630 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2630 with
                | (head1,uu____2646) ->
                    let uu____2667 =
                      let uu____2668 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2668.FStar_Syntax_Syntax.n  in
                    (match uu____2667 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2672 =
                           let uu____2673 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2673
                            in
                         Prims.op_Negation uu____2672
                     | uu____2674 -> true)))
              &&
              (let uu____2676 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2676)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____2710 =
              let uu____2711 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2711  in
            if uu____2710
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2713 = FStar_Syntax_Util.is_unit t  in
               if uu____2713
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____2719 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2719
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2721 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2721 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2731 =
                             let uu____2732 =
                               let uu____2737 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2738 =
                                 let uu____2739 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2748 =
                                   let uu____2759 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2759]  in
                                 uu____2739 :: uu____2748  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2737
                                 uu____2738
                                in
                             uu____2732 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____2731)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2795 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2795
           then
             let uu____2796 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2797 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2798 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2796 uu____2797 uu____2798
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____2811 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___322_2815  ->
              match uu___322_2815 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2816 -> false))
       in
    if uu____2811
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___323_2825  ->
              match uu___323_2825 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____2844 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2844
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2847 = destruct_comp c1  in
           match uu____2847 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____2861 =
                   let uu____2866 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____2867 =
                     let uu____2868 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____2877 =
                       let uu____2888 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____2897 =
                         let uu____2908 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____2908]  in
                       uu____2888 :: uu____2897  in
                     uu____2868 :: uu____2877  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____2866 uu____2867  in
                 uu____2861 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____2951 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____2951)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2974 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2976 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2976
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2979 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2979 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____3022 = destruct_comp c1  in
               match uu____3022 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____3036 =
                       let uu____3041 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____3042 =
                         let uu____3043 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____3052 =
                           let uu____3063 =
                             let uu____3072 =
                               let uu____3073 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____3073 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____3072
                              in
                           let uu____3082 =
                             let uu____3093 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____3093]  in
                           uu____3063 :: uu____3082  in
                         uu____3043 :: uu____3052  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3041 uu____3042
                        in
                     uu____3036 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____3178 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____3178
            then (lc, g0)
            else
              (let flags1 =
                 let uu____3187 =
                   let uu____3194 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____3194
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____3187 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____3214 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___324_3222  ->
                               match uu___324_3222 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____3225 -> []))
                        in
                     FStar_List.append flags1 uu____3214
                  in
               let strengthen uu____3231 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____3235 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____3235 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____3238 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____3238
                          then
                            let uu____3239 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____3240 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____3239 uu____3240
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____3242 =
                 let uu____3243 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____3243
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____3242,
                 (let uu___344_3245 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___344_3245.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___344_3245.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___344_3245.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___325_3252  ->
            match uu___325_3252 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3253 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____3280 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3280
          then e
          else
            (let uu____3284 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3286 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3286)
                in
             if uu____3284
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____3336  ->
            match uu____3336 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3356 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3356 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3364 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3364
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____3371 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____3371
                       then
                         let uu____3374 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____3374
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3378 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____3378
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3383 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____3383
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3387 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3387
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____3396 =
                  let uu____3397 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3397
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____3411  ->
                          let uu____3412 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3413 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3415 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3412 uu____3413 uu____3415);
                     (let aux uu____3429 =
                        let uu____3430 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3430
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3451 ->
                              let uu____3452 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3452
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____3471 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____3471
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____3542 =
                              let uu____3547 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____3547, reason)  in
                            FStar_Util.Inl uu____3542
                        | uu____3554 -> aux ()  in
                      let try_simplify uu____3578 =
                        let rec maybe_close t x c =
                          let uu____3595 =
                            let uu____3596 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____3596.FStar_Syntax_Syntax.n  in
                          match uu____3595 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____3600) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____3606 -> c  in
                        let uu____3607 =
                          let uu____3608 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____3608  in
                        if uu____3607
                        then
                          let uu____3619 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____3619
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3633 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3633))
                        else
                          (let uu____3643 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____3643
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____3653 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____3653
                              then
                                let uu____3662 =
                                  let uu____3667 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____3667, "both gtot")  in
                                FStar_Util.Inl uu____3662
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____3691 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____3693 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____3693)
                                        in
                                     if uu____3691
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___345_3706 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___345_3706.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___345_3706.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____3707 =
                                         let uu____3712 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____3712, "c1 Tot")  in
                                       FStar_Util.Inl uu____3707
                                     else aux ()
                                 | uu____3718 -> aux ())))
                         in
                      let uu____3727 = try_simplify ()  in
                      match uu____3727 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____3747  ->
                                let uu____3748 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3748);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3757  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3778 = lift_and_destruct env c11 c21
                                 in
                              match uu____3778 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3831 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____3831]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____3851 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____3851]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____3898 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3907 =
                                      let uu____3918 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3927 =
                                        let uu____3938 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3947 =
                                          let uu____3958 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3967 =
                                            let uu____3978 =
                                              let uu____3987 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3987
                                               in
                                            [uu____3978]  in
                                          uu____3958 :: uu____3967  in
                                        uu____3938 :: uu____3947  in
                                      uu____3918 :: uu____3927  in
                                    uu____3898 :: uu____3907  in
                                  let wp =
                                    let uu____4039 =
                                      let uu____4044 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____4044 wp_args
                                       in
                                    uu____4039 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____4069 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____4069 with
                              | (m,uu____4077,lift2) ->
                                  let c23 =
                                    let uu____4080 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____4080
                                     in
                                  let uu____4081 = destruct_comp c12  in
                                  (match uu____4081 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____4095 =
                                           let uu____4100 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____4101 =
                                             let uu____4102 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____4111 =
                                               let uu____4122 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____4122]  in
                                             uu____4102 :: uu____4111  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____4100 uu____4101
                                            in
                                         uu____4095
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____4161 = destruct_comp c1_typ  in
                            match uu____4161 with
                            | (u_res_t1,res_t1,uu____4170) ->
                                let uu____4171 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____4171
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____4174 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____4174
                                   then
                                     (debug1
                                        (fun uu____4182  ->
                                           let uu____4183 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____4184 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____4183 uu____4184);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____4189 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____4191 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____4191)
                                         in
                                      if uu____4189
                                      then
                                        let e1' =
                                          let uu____4211 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____4211
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____4220  ->
                                              let uu____4221 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____4222 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____4221 uu____4222);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____4234  ->
                                              let uu____4235 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____4236 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____4235 uu____4236);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____4241 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____4241
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____4257 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____4279 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____4279)
           in
        let flags1 =
          if should_return1
          then
            let uu____4285 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____4285
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____4297 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____4301 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____4301
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____4305 =
              let uu____4306 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____4306  in
            (if uu____4305
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___346_4311 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___346_4311.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___346_4311.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___346_4311.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____4322 =
                 let uu____4323 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____4323
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4322
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____4326 =
               let uu____4327 =
                 let uu____4328 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____4328
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____4327  in
             FStar_Syntax_Util.comp_set_flags uu____4326 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____4363  ->
              match uu____4363 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____4375 =
                      ((let uu____4378 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____4378) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____4375
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____4392 =
        let uu____4393 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____4393  in
      FStar_Syntax_Syntax.fvar uu____4392 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____4459  ->
                 match uu____4459 with
                 | (uu____4472,eff_label,uu____4474,uu____4475) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____4486 =
          let uu____4493 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____4527  ->
                    match uu____4527 with
                    | (uu____4540,uu____4541,flags1,uu____4543) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___326_4557  ->
                                match uu___326_4557 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____4558 -> false))))
             in
          if uu____4493
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____4486 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____4581 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____4583 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4583
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____4621 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____4622 =
                     let uu____4627 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____4628 =
                       let uu____4629 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____4638 =
                         let uu____4649 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____4658 =
                           let uu____4669 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____4678 =
                             let uu____4689 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____4689]  in
                           uu____4669 :: uu____4678  in
                         uu____4649 :: uu____4658  in
                       uu____4629 :: uu____4638  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____4627 uu____4628  in
                   uu____4622 FStar_Pervasives_Native.None uu____4621  in
                 let default_case =
                   let post_k =
                     let uu____4744 =
                       let uu____4753 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____4753]  in
                     let uu____4772 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4744 uu____4772  in
                   let kwp =
                     let uu____4778 =
                       let uu____4787 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____4787]  in
                     let uu____4806 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4778 uu____4806  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____4813 =
                       let uu____4814 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____4814]  in
                     let uu____4833 =
                       let uu____4836 =
                         let uu____4843 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____4843
                          in
                       let uu____4844 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____4836 uu____4844  in
                     FStar_Syntax_Util.abs uu____4813 uu____4833
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____4866 =
                     should_not_inline_whole_match ||
                       (let uu____4868 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____4868)
                      in
                   if uu____4866 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4901  ->
                        fun celse  ->
                          match uu____4901 with
                          | (g,eff_label,uu____4917,cthen) ->
                              let uu____4929 =
                                let uu____4954 =
                                  let uu____4955 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4955
                                   in
                                lift_and_destruct env uu____4954 celse  in
                              (match uu____4929 with
                               | ((md,uu____4957,uu____4958),(uu____4959,uu____4960,wp_then),
                                  (uu____4962,uu____4963,wp_else)) ->
                                   let uu____4983 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4983 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4997::[] -> comp
                 | uu____5037 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____5055 = destruct_comp comp1  in
                     (match uu____5055 with
                      | (uu____5062,uu____5063,wp) ->
                          let wp1 =
                            let uu____5068 =
                              let uu____5073 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____5074 =
                                let uu____5075 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____5084 =
                                  let uu____5095 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____5095]  in
                                uu____5075 :: uu____5084  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____5073
                                uu____5074
                               in
                            uu____5068 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____5162 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____5162 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____5177 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____5182 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____5177 uu____5182
              else
                (let uu____5190 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____5195 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____5190 uu____5195)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          if env.FStar_TypeChecker_Env.is_pattern
          then (e, lc)
          else
            (let is_type1 t1 =
               let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
               let uu____5239 =
                 let uu____5240 = FStar_Syntax_Subst.compress t2  in
                 uu____5240.FStar_Syntax_Syntax.n  in
               match uu____5239 with
               | FStar_Syntax_Syntax.Tm_type uu____5243 -> true
               | uu____5244 -> false  in
             let uu____5245 =
               let uu____5246 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____5246.FStar_Syntax_Syntax.n  in
             match uu____5245 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____5254 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____5264 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____5264
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____5266 =
                     let uu____5267 =
                       let uu____5268 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5268
                        in
                     (FStar_Pervasives_Native.None, uu____5267)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____5266
                    in
                 let e1 =
                   let uu____5274 =
                     let uu____5279 =
                       let uu____5280 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____5280]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5279  in
                   uu____5274 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____5307 -> (e, lc))
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____5341 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____5341
           then
             let uu____5342 = FStar_Syntax_Print.term_to_string e  in
             let uu____5343 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____5344 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____5342 uu____5343 uu____5344
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____5350 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____5350 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____5373 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____5395 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____5395, false)
             else
               (let uu____5401 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____5401, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____5412) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____5421 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____5421
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___347_5435 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___347_5435.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___347_5435.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___347_5435.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____5440 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____5440 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____5447 = FStar_Syntax_Util.set_result_typ_lc lc t
                       in
                    (e, uu____5447, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___348_5450 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___348_5450.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___348_5450.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___348_5450.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____5456 =
                      let uu____5457 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____5457
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.Simplify;
                             FStar_TypeChecker_Normalize.Primops] env f
                            in
                         let uu____5460 =
                           let uu____5461 = FStar_Syntax_Subst.compress f1
                              in
                           uu____5461.FStar_Syntax_Syntax.n  in
                         match uu____5460 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____5464,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____5466;
                                           FStar_Syntax_Syntax.vars =
                                             uu____5467;_},uu____5468)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___349_5494 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___349_5494.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___349_5494.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___349_5494.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5495 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____5498 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____5498
                               then
                                 let uu____5499 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____5500 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____5501 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____5502 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5499 uu____5500 uu____5501
                                   uu____5502
                               else ());
                              (let u_t_opt = comp_univ_opt c  in
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (t.FStar_Syntax_Syntax.pos)) t
                                  in
                               let xexp = FStar_Syntax_Syntax.bv_to_name x
                                  in
                               let cret = return_value env u_t_opt t xexp  in
                               let guard =
                                 if apply_guard1
                                 then
                                   let uu____5511 =
                                     let uu____5516 =
                                       let uu____5517 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____5517]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5516
                                      in
                                   uu____5511 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____5545 =
                                 let uu____5550 =
                                   FStar_All.pipe_left
                                     (fun _0_16  ->
                                        FStar_Pervasives_Native.Some _0_16)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____5567 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____5568 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____5569 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____5550
                                   uu____5567 e uu____5568 uu____5569
                                  in
                               match uu____5545 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___350_5573 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___350_5573.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___350_5573.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____5575 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5575
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____5580 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____5580
                                     then
                                       let uu____5581 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5581
                                     else ());
                                    c2))))
                       in
                    let flags1 =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___327_5591  ->
                              match uu___327_5591 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____5594 -> []))
                       in
                    let lc1 =
                      let uu____5596 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____5596 t flags1
                        strengthen
                       in
                    let g2 =
                      let uu___351_5598 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___351_5598.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___351_5598.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___351_5598.FStar_TypeChecker_Env.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____5633 =
          let uu____5636 =
            let uu____5641 =
              let uu____5642 =
                let uu____5651 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____5651  in
              [uu____5642]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____5641  in
          uu____5636 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____5633  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____5676 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____5676
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____5692 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____5707 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____5723 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____5723
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____5737)::(ens,uu____5739)::uu____5740 ->
                    let uu____5783 =
                      let uu____5786 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____5786  in
                    let uu____5787 =
                      let uu____5788 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____5788  in
                    (uu____5783, uu____5787)
                | uu____5791 ->
                    let uu____5802 =
                      let uu____5807 =
                        let uu____5808 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____5808
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____5807)
                       in
                    FStar_Errors.raise_error uu____5802
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____5824)::uu____5825 ->
                    let uu____5852 =
                      let uu____5857 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5857
                       in
                    (match uu____5852 with
                     | (us_r,uu____5889) ->
                         let uu____5890 =
                           let uu____5895 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5895
                            in
                         (match uu____5890 with
                          | (us_e,uu____5927) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____5930 =
                                  let uu____5931 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5931
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5930
                                  us_r
                                 in
                              let as_ens =
                                let uu____5933 =
                                  let uu____5934 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5934
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5933
                                  us_e
                                 in
                              let req =
                                let uu____5938 =
                                  let uu____5943 =
                                    let uu____5944 =
                                      let uu____5955 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5955]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5944
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5943
                                   in
                                uu____5938 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____5997 =
                                  let uu____6002 =
                                    let uu____6003 =
                                      let uu____6014 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____6014]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____6003
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____6002
                                   in
                                uu____5997 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____6053 =
                                let uu____6056 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____6056  in
                              let uu____6057 =
                                let uu____6058 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____6058  in
                              (uu____6053, uu____6057)))
                | uu____6061 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____6093 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____6093
       then
         let uu____6094 = FStar_Syntax_Print.term_to_string tm  in
         let uu____6095 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____6094 uu____6095
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____6145 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____6145
         then
           let uu____6146 = FStar_Syntax_Print.term_to_string tm  in
           let uu____6147 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____6146
             uu____6147
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____6154 =
      let uu____6155 =
        let uu____6156 = FStar_Syntax_Subst.compress t  in
        uu____6156.FStar_Syntax_Syntax.n  in
      match uu____6155 with
      | FStar_Syntax_Syntax.Tm_app uu____6159 -> false
      | uu____6176 -> true  in
    if uu____6154
    then t
    else
      (let uu____6178 = FStar_Syntax_Util.head_and_args t  in
       match uu____6178 with
       | (head1,args) ->
           let uu____6221 =
             let uu____6222 =
               let uu____6223 = FStar_Syntax_Subst.compress head1  in
               uu____6223.FStar_Syntax_Syntax.n  in
             match uu____6222 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____6226 -> false  in
           if uu____6221
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____6256 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____6303 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____6303 with
             | (formals,uu____6319) ->
                 let n_implicits =
                   let uu____6341 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6419  ->
                             match uu____6419 with
                             | (uu____6426,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____6341 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____6561 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____6561 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____6585 =
                     let uu____6590 =
                       let uu____6591 = FStar_Util.string_of_int n_expected
                          in
                       let uu____6598 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6599 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____6591 uu____6598 uu____6599
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____6590)
                      in
                   let uu____6606 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____6585 uu____6606
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___328_6629 =
             match uu___328_6629 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____6663 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____6663 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_17,uu____6778) when
                          _0_17 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Env.trivial_guard)
                      | (uu____6821,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____6854 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____6854 with
                           | (v1,uu____6894,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____6913 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____6913 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7006 =
                                      FStar_TypeChecker_Env.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____7006)))
                      | (uu____7033,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Meta tau))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____7068 =
                            new_implicit_var "Instantiation of meta argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____7068 with
                           | (v1,uu____7108,g) ->
                               let mark_meta_implicits tau1 g1 =
                                 let uu___352_7133 = g1  in
                                 let uu____7134 =
                                   FStar_List.map
                                     (fun imp  ->
                                        let uu___353_7140 = imp  in
                                        {
                                          FStar_TypeChecker_Env.imp_reason =
                                            (uu___353_7140.FStar_TypeChecker_Env.imp_reason);
                                          FStar_TypeChecker_Env.imp_uvar =
                                            (uu___353_7140.FStar_TypeChecker_Env.imp_uvar);
                                          FStar_TypeChecker_Env.imp_tm =
                                            (uu___353_7140.FStar_TypeChecker_Env.imp_tm);
                                          FStar_TypeChecker_Env.imp_range =
                                            (uu___353_7140.FStar_TypeChecker_Env.imp_range);
                                          FStar_TypeChecker_Env.imp_meta =
                                            (FStar_Pervasives_Native.Some
                                               (env, tau1))
                                        }) g1.FStar_TypeChecker_Env.implicits
                                    in
                                 {
                                   FStar_TypeChecker_Env.guard_f =
                                     (uu___352_7133.FStar_TypeChecker_Env.guard_f);
                                   FStar_TypeChecker_Env.deferred =
                                     (uu___352_7133.FStar_TypeChecker_Env.deferred);
                                   FStar_TypeChecker_Env.univ_ineqs =
                                     (uu___352_7133.FStar_TypeChecker_Env.univ_ineqs);
                                   FStar_TypeChecker_Env.implicits =
                                     uu____7134
                                 }  in
                               let g1 = mark_meta_implicits tau g  in
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____7151 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____7151 with
                                | (args,bs3,subst3,g') ->
                                    let uu____7244 =
                                      FStar_TypeChecker_Env.conj_guard g1 g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                              false))) :: args), bs3, subst3,
                                      uu____7244)))
                      | (uu____7271,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Env.trivial_guard)
                       in
                    let uu____7317 =
                      let uu____7344 = inst_n_binders t  in
                      aux [] uu____7344 bs1  in
                    (match uu____7317 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____7415) -> (e, torig, guard)
                          | (uu____7446,[]) when
                              let uu____7477 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____7477 ->
                              (e, torig, FStar_TypeChecker_Env.trivial_guard)
                          | uu____7478 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____7506 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____7519 -> (e, t, FStar_TypeChecker_Env.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____7529 =
      let uu____7532 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____7532
        (FStar_List.map
           (fun u  ->
              let uu____7542 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____7542 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____7529 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____7563 = FStar_Util.set_is_empty x  in
      if uu____7563
      then []
      else
        (let s =
           let uu____7578 =
             let uu____7581 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____7581  in
           FStar_All.pipe_right uu____7578 FStar_Util.set_elements  in
         (let uu____7597 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____7597
          then
            let uu____7598 =
              let uu____7599 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____7599  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____7598
          else ());
         (let r =
            let uu____7606 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____7606  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____7645 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____7645
                     then
                       let uu____7646 =
                         let uu____7647 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7647
                          in
                       let uu____7648 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____7649 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7646 uu____7648 uu____7649
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____7675 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____7675 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____7713) -> generalized_univ_names
        | (uu____7720,[]) -> explicit_univ_names
        | uu____7727 ->
            let uu____7736 =
              let uu____7741 =
                let uu____7742 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7742
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____7741)
               in
            FStar_Errors.raise_error uu____7736 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____7760 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____7760
       then
         let uu____7761 = FStar_Syntax_Print.term_to_string t  in
         let uu____7762 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____7761 uu____7762
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____7768 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____7768
        then
          let uu____7769 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____7769
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____7775 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____7775
         then
           let uu____7776 = FStar_Syntax_Print.term_to_string t  in
           let uu____7777 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____7776 uu____7777
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____7855 =
          let uu____7856 =
            FStar_Util.for_all
              (fun uu____7869  ->
                 match uu____7869 with
                 | (uu____7878,uu____7879,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____7856  in
        if uu____7855
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7927 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____7927
              then
                let uu____7928 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7928
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____7932 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____7932
               then
                 let uu____7933 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7933
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____7948 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____7948 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____7982 =
             match uu____7982 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____8019 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____8019
                   then
                     let uu____8020 =
                       let uu____8021 =
                         let uu____8024 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____8024
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____8021
                         (FStar_String.concat ", ")
                        in
                     let uu____8067 =
                       let uu____8068 =
                         let uu____8071 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____8071
                           (FStar_List.map
                              (fun u  ->
                                 let uu____8082 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____8083 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____8082
                                   uu____8083))
                          in
                       FStar_All.pipe_right uu____8068
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____8020
                       uu____8067
                   else ());
                  (let univs2 =
                     let uu____8090 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____8102 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____8102) univs1
                       uu____8090
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____8109 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____8109
                    then
                      let uu____8110 =
                        let uu____8111 =
                          let uu____8114 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____8114
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____8111
                          (FStar_String.concat ", ")
                         in
                      let uu____8157 =
                        let uu____8158 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____8169 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____8170 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____8169
                                    uu____8170))
                           in
                        FStar_All.pipe_right uu____8158
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____8110
                        uu____8157
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____8184 =
             let uu____8201 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____8201  in
           match uu____8184 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____8291 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____8291
                 then ()
                 else
                   (let uu____8293 = lec_hd  in
                    match uu____8293 with
                    | (lb1,uu____8301,uu____8302) ->
                        let uu____8303 = lec2  in
                        (match uu____8303 with
                         | (lb2,uu____8311,uu____8312) ->
                             let msg =
                               let uu____8314 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8315 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____8314 uu____8315
                                in
                             let uu____8316 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____8316))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u  ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u'  ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head))))
                    in
                 let uu____8380 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____8380
                 then ()
                 else
                   (let uu____8382 = lec_hd  in
                    match uu____8382 with
                    | (lb1,uu____8390,uu____8391) ->
                        let uu____8392 = lec2  in
                        (match uu____8392 with
                         | (lb2,uu____8400,uu____8401) ->
                             let msg =
                               let uu____8403 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____8404 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____8403 uu____8404
                                in
                             let uu____8405 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____8405))
                  in
               let lecs1 =
                 let uu____8415 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____8468 = univs_and_uvars_of_lec this_lec  in
                        match uu____8468 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____8415 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____8569 = lec_hd  in
                   match uu____8569 with
                   | (lbname,e,c) ->
                       let uu____8579 =
                         let uu____8584 =
                           let uu____8585 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____8586 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____8587 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____8585 uu____8586 uu____8587
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____8584)
                          in
                       let uu____8588 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____8579 uu____8588
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____8609 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____8609 with
                         | FStar_Pervasives_Native.Some uu____8618 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____8625 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____8629 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____8629 with
                              | (bs,kres) ->
                                  ((let uu____8673 =
                                      let uu____8674 =
                                        let uu____8677 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____8677
                                         in
                                      uu____8674.FStar_Syntax_Syntax.n  in
                                    match uu____8673 with
                                    | FStar_Syntax_Syntax.Tm_type uu____8678
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____8682 =
                                          let uu____8683 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____8683  in
                                        if uu____8682 then fail1 kres else ()
                                    | uu____8685 -> fail1 kres);
                                   (let a =
                                      let uu____8687 =
                                        let uu____8690 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_18  ->
                                             FStar_Pervasives_Native.Some
                                               _0_18) uu____8690
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____8687
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____8700 ->
                                          let uu____8709 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____8709
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres))
                                       in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____8816  ->
                         match uu____8816 with
                         | (lbname,e,c) ->
                             let uu____8864 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____8939 ->
                                   let uu____8954 = (e, c)  in
                                   (match uu____8954 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____8997  ->
                                                   match uu____8997 with
                                                   | (x,uu____9005) ->
                                                       let uu____9010 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____9010)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____9028 =
                                                let uu____9029 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____9029
                                                 in
                                              if uu____9028
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____9035 =
                                            let uu____9036 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____9036.FStar_Syntax_Syntax.n
                                             in
                                          match uu____9035 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____9061 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____9061 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____9074 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____9078 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____9078, gen_tvars))
                                in
                             (match uu____8864 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____9232 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9232
         then
           let uu____9233 =
             let uu____9234 =
               FStar_List.map
                 (fun uu____9247  ->
                    match uu____9247 with
                    | (lb,uu____9255,uu____9256) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____9234 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____9233
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____9277  ->
                match uu____9277 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____9306 = gen env is_rec lecs  in
           match uu____9306 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____9405  ->
                       match uu____9405 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____9467 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____9467
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____9513  ->
                           match uu____9513 with
                           | (l,us,e,c,gvs) ->
                               let uu____9547 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____9548 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____9549 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____9550 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____9551 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____9547 uu____9548 uu____9549 uu____9550
                                 uu____9551))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____9592  ->
                match uu____9592 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____9636 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____9636, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____9693 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____9693 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9699 = FStar_TypeChecker_Env.apply_guard f e  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____9699)
             in
          let is_var e1 =
            let uu____9708 =
              let uu____9709 = FStar_Syntax_Subst.compress e1  in
              uu____9709.FStar_Syntax_Syntax.n  in
            match uu____9708 with
            | FStar_Syntax_Syntax.Tm_name uu____9712 -> true
            | uu____9713 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___354_9733 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___354_9733.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___354_9733.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9734 -> e2  in
          let env2 =
            let uu___355_9736 = env1  in
            let uu____9737 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___355_9736.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___355_9736.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___355_9736.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___355_9736.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___355_9736.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___355_9736.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___355_9736.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___355_9736.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___355_9736.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___355_9736.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___355_9736.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___355_9736.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___355_9736.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___355_9736.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___355_9736.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___355_9736.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___355_9736.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9737;
              FStar_TypeChecker_Env.is_iface =
                (uu___355_9736.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___355_9736.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___355_9736.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___355_9736.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___355_9736.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___355_9736.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___355_9736.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___355_9736.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___355_9736.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___355_9736.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___355_9736.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___355_9736.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___355_9736.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___355_9736.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___355_9736.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___355_9736.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___355_9736.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___355_9736.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___355_9736.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___355_9736.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___355_9736.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___355_9736.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___355_9736.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____9738 = check1 env2 t1 t2  in
          match uu____9738 with
          | FStar_Pervasives_Native.None  ->
              let uu____9745 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____9750 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____9745 uu____9750
          | FStar_Pervasives_Native.Some g ->
              ((let uu____9757 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____9757
                then
                  let uu____9758 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____9758
                else ());
               (let uu____9760 = decorate e t2  in (uu____9760, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____9785 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9785
         then
           let uu____9786 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____9786
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____9796 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____9796
         then
           let uu____9801 = discharge g1  in
           let uu____9802 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____9801, uu____9802)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.NoFullNorm;
              FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____9809 =
                let uu____9810 =
                  let uu____9811 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____9811 FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____9810
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____9809
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____9813 = destruct_comp c1  in
            match uu____9813 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____9830 = FStar_TypeChecker_Env.get_range env  in
                  let uu____9831 =
                    let uu____9836 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____9837 =
                      let uu____9838 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____9847 =
                        let uu____9858 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____9858]  in
                      uu____9838 :: uu____9847  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9836 uu____9837  in
                  uu____9831 FStar_Pervasives_Native.None uu____9830  in
                ((let uu____9894 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____9894
                  then
                    let uu____9895 = FStar_Syntax_Print.term_to_string vc  in
                    FStar_Util.print1 "top-level VC: %s\n" uu____9895
                  else ());
                 (let g2 =
                    let uu____9898 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____9898  in
                  let uu____9899 = discharge g2  in
                  let uu____9900 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____9899, uu____9900)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___329_9932 =
        match uu___329_9932 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____9942)::[] -> f fst1
        | uu____9967 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____9978 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____9978
          (fun _0_20  -> FStar_TypeChecker_Common.NonTrivial _0_20)
         in
      let op_or_e e =
        let uu____9989 =
          let uu____9990 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____9990  in
        FStar_All.pipe_right uu____9989
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_or_t t =
        let uu____10009 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____10009
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let short_op_ite uu___330_10023 =
        match uu___330_10023 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____10033)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____10060)::[] ->
            let uu____10101 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____10101
              (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
        | uu____10102 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____10113 =
          let uu____10121 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____10121)  in
        let uu____10129 =
          let uu____10139 =
            let uu____10147 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____10147)  in
          let uu____10155 =
            let uu____10165 =
              let uu____10173 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____10173)  in
            let uu____10181 =
              let uu____10191 =
                let uu____10199 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____10199)  in
              let uu____10207 =
                let uu____10217 =
                  let uu____10225 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____10225)  in
                [uu____10217; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____10191 :: uu____10207  in
            uu____10165 :: uu____10181  in
          uu____10139 :: uu____10155  in
        uu____10113 :: uu____10129  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____10287 =
            FStar_Util.find_map table
              (fun uu____10302  ->
                 match uu____10302 with
                 | (x,mk1) ->
                     let uu____10319 = FStar_Ident.lid_equals x lid  in
                     if uu____10319
                     then
                       let uu____10322 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____10322
                     else FStar_Pervasives_Native.None)
             in
          (match uu____10287 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____10325 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____10331 =
      let uu____10332 = FStar_Syntax_Util.un_uinst l  in
      uu____10332.FStar_Syntax_Syntax.n  in
    match uu____10331 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____10336 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____10370)::uu____10371 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____10390 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____10399,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____10400))::uu____10401 -> bs
      | uu____10418 ->
          let uu____10419 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____10419 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____10423 =
                 let uu____10424 = FStar_Syntax_Subst.compress t  in
                 uu____10424.FStar_Syntax_Syntax.n  in
               (match uu____10423 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____10428) ->
                    let uu____10449 =
                      FStar_Util.prefix_until
                        (fun uu___331_10489  ->
                           match uu___331_10489 with
                           | (uu____10496,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____10497)) ->
                               false
                           | uu____10500 -> true) bs'
                       in
                    (match uu____10449 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____10535,uu____10536) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____10608,uu____10609) ->
                         let uu____10682 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10700  ->
                                   match uu____10700 with
                                   | (x,uu____10708) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____10682
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10755  ->
                                     match uu____10755 with
                                     | (x,i) ->
                                         let uu____10774 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____10774, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10784 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            let uu____10812 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____10812
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____10839 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____10839
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____10874 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____10874
         then
           ((let uu____10876 = FStar_Ident.text_of_lid lident  in
             d uu____10876);
            (let uu____10877 = FStar_Ident.text_of_lid lident  in
             let uu____10878 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____10877 uu____10878))
         else ());
        (let fv =
           let uu____10881 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10881
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____10891 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___356_10893 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___356_10893.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___356_10893.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___356_10893.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___356_10893.FStar_Syntax_Syntax.sigattrs)
           }), uu____10891))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___332_10909 =
        match uu___332_10909 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10910 -> false  in
      let reducibility uu___333_10916 =
        match uu___333_10916 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10917 -> false  in
      let assumption uu___334_10923 =
        match uu___334_10923 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10924 -> false  in
      let reification uu___335_10930 =
        match uu___335_10930 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10931 -> true
        | uu____10932 -> false  in
      let inferred uu___336_10938 =
        match uu___336_10938 with
        | FStar_Syntax_Syntax.Discriminator uu____10939 -> true
        | FStar_Syntax_Syntax.Projector uu____10940 -> true
        | FStar_Syntax_Syntax.RecordType uu____10945 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____10954 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____10963 -> false  in
      let has_eq uu___337_10969 =
        match uu___337_10969 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____10970 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____11034 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____11039 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____11049 =
        let uu____11050 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___338_11054  ->
                  match uu___338_11054 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____11055 -> false))
           in
        FStar_All.pipe_right uu____11050 Prims.op_Negation  in
      if uu____11049
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____11070 =
            let uu____11075 =
              let uu____11076 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____11076 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____11075)  in
          FStar_Errors.raise_error uu____11070 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____11088 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____11092 =
            let uu____11093 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____11093  in
          if uu____11092 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____11098),uu____11099) ->
              ((let uu____11109 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____11109
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____11113 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____11113
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____11119 ->
              let uu____11128 =
                let uu____11129 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____11129  in
              if uu____11128 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____11135 ->
              let uu____11142 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____11142 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____11146 ->
              let uu____11153 =
                let uu____11154 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____11154  in
              if uu____11153 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____11160 ->
              let uu____11161 =
                let uu____11162 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11162  in
              if uu____11161 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____11168 ->
              let uu____11169 =
                let uu____11170 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____11170  in
              if uu____11169 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____11176 ->
              let uu____11189 =
                let uu____11190 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____11190  in
              if uu____11189 then err'1 () else ()
          | uu____11196 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____11230 =
          let uu____11231 = FStar_Syntax_Subst.compress t1  in
          uu____11231.FStar_Syntax_Syntax.n  in
        match uu____11230 with
        | FStar_Syntax_Syntax.Tm_type uu____11234 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____11237 =
                 let uu____11242 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____11242
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____11237
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____11260 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____11260
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____11277 =
                                 let uu____11278 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____11278.FStar_Syntax_Syntax.n  in
                               match uu____11277 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____11282 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____11283 ->
            let uu____11298 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____11298 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____11330 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____11330
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____11332;
               FStar_Syntax_Syntax.index = uu____11333;
               FStar_Syntax_Syntax.sort = t2;_},uu____11335)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____11343,uu____11344) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____11386::[]) ->
            let uu____11425 =
              let uu____11426 = FStar_Syntax_Util.un_uinst head1  in
              uu____11426.FStar_Syntax_Syntax.n  in
            (match uu____11425 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____11430 -> false)
        | uu____11431 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____11439 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____11439
         then
           let uu____11440 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____11440
         else ());
        res
       in aux g t
  