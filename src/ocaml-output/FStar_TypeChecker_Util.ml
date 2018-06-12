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
                     (let uu___338_197 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___338_197.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___338_197.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___338_197.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___339_199 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___339_199.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___339_199.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___339_199.FStar_TypeChecker_Env.implicits)
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
                                let uu____430 = FStar_Options.ml_ish ()  in
                                if uu____430
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____447 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____447
                            then
                              let uu____448 = FStar_Range.string_of_range r
                                 in
                              let uu____449 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____448 uu____449
                            else ());
                           FStar_Util.Inl t2)
                      | uu____451 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____453 = aux e1  in
                      match uu____453 with
                      | FStar_Util.Inr c ->
                          let uu____459 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____459
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____461 =
                               let uu____466 =
                                 let uu____467 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____467
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____466)
                                in
                             FStar_Errors.raise_error uu____461 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____471 ->
               let uu____472 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____472 with
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
          | (uu____533,FStar_Syntax_Syntax.Tm_uinst (e2,uu____535)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____540,uu____541) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____545 =
                    let uu____546 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____547 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____546 uu____547
                     in
                  failwith uu____545)
               else ();
               (let uu____550 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____550
                then
                  let uu____551 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____552 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____551
                    uu____552
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___340_556 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___340_556.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___340_556.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____560 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____560
                then
                  let uu____561 =
                    let uu____562 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____563 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____562 uu____563
                     in
                  failwith uu____561
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___341_567 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___341_567.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___341_567.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____569),uu____570) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____594 =
                  let uu____595 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____595  in
                if uu____594
                then
                  let uu____596 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____596
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____615;
                FStar_Syntax_Syntax.vars = uu____616;_},args))
              ->
              ((let uu____655 =
                  let uu____656 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____656 Prims.op_Negation  in
                if uu____655
                then
                  let uu____657 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____657
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____799)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____874) ->
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
                       | ((e2,imp),uu____911) ->
                           let pat =
                             let uu____935 = aux argpat e2  in
                             let uu____938 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____935, uu____938)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____947 ->
                      let uu____970 =
                        let uu____971 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____972 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____971 uu____972
                         in
                      failwith uu____970
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____984;
                     FStar_Syntax_Syntax.vars = uu____985;_},uu____986);
                FStar_Syntax_Syntax.pos = uu____987;
                FStar_Syntax_Syntax.vars = uu____988;_},args))
              ->
              ((let uu____1031 =
                  let uu____1032 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____1032 Prims.op_Negation  in
                if uu____1031
                then
                  let uu____1033 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____1033
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____1175)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____1250) ->
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
                       | ((e2,imp),uu____1287) ->
                           let pat =
                             let uu____1311 = aux argpat e2  in
                             let uu____1314 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____1311, uu____1314)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____1323 ->
                      let uu____1346 =
                        let uu____1347 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____1348 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____1347 uu____1348
                         in
                      failwith uu____1346
                   in
                match_args [] args argpats))
          | uu____1357 ->
              let uu____1362 =
                let uu____1363 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____1364 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____1365 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____1363 uu____1364 uu____1365
                 in
              failwith uu____1362
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
    let pat_as_arg uu____1408 =
      match uu____1408 with
      | (p,i) ->
          let uu____1425 = decorated_pattern_as_term p  in
          (match uu____1425 with
           | (vars,te) ->
               let uu____1448 =
                 let uu____1453 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____1453)  in
               (vars, uu____1448))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____1467 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____1467)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____1471 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1471)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____1475 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____1475)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____1496 =
          let uu____1513 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____1513 FStar_List.unzip  in
        (match uu____1496 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____1635 =
               let uu____1636 =
                 let uu____1637 =
                   let uu____1652 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____1652, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____1637  in
               mk1 uu____1636  in
             (vars1, uu____1635))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____1688,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____1698,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____1712 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____1734)::[] -> wp
      | uu____1751 ->
          let uu____1760 =
            let uu____1761 =
              let uu____1762 =
                FStar_List.map
                  (fun uu____1772  ->
                     match uu____1772 with
                     | (x,uu____1778) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____1762 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____1761
             in
          failwith uu____1760
       in
    let uu____1781 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____1781, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____1797 = destruct_comp c  in
        match uu____1797 with
        | (u,uu____1805,wp) ->
            let uu____1807 =
              let uu____1816 =
                let uu____1823 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____1823  in
              [uu____1816]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____1807;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____1851 =
          let uu____1858 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____1859 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____1858 uu____1859  in
        match uu____1851 with | (m,uu____1861,uu____1862) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____1878 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____1878
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
        let uu____1921 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____1921 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____1958 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____1958 with
             | (a,kwp) ->
                 let uu____1989 = destruct_comp m1  in
                 let uu____1996 = destruct_comp m2  in
                 ((md, a, kwp), uu____1989, uu____1996))
  
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
            let uu____2076 =
              let uu____2077 =
                let uu____2086 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____2086]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____2077;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____2076
  
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
          let uu____2162 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2162
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
      let uu____2174 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____2174
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____2177  ->
           let uu____2178 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____2178)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2184 =
      let uu____2185 = FStar_Syntax_Subst.compress t  in
      uu____2185.FStar_Syntax_Syntax.n  in
    match uu____2184 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2188 -> true
    | uu____2201 -> false
  
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
              let uu____2258 =
                let uu____2259 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2259  in
              if uu____2258
              then f
              else (let uu____2261 = reason1 ()  in label uu____2261 r f)
  
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
            let uu___342_2278 = g  in
            let uu____2279 =
              let uu____2280 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2280  in
            {
              FStar_TypeChecker_Env.guard_f = uu____2279;
              FStar_TypeChecker_Env.deferred =
                (uu___342_2278.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___342_2278.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___342_2278.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____2300 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2300
        then c
        else
          (let uu____2302 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____2302
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____2361 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____2361]  in
                       let us =
                         let uu____2377 =
                           let uu____2380 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____2380]  in
                         u_res :: uu____2377  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____2386 =
                         let uu____2391 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____2392 =
                           let uu____2393 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____2400 =
                             let uu____2409 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____2416 =
                               let uu____2425 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____2425]  in
                             uu____2409 :: uu____2416  in
                           uu____2393 :: uu____2400  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____2391 uu____2392
                          in
                       uu____2386 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____2459 = destruct_comp c1  in
              match uu____2459 with
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
          (fun uu____2494  ->
             let uu____2495 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____2495)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___320_2504  ->
            match uu___320_2504 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____2505 -> false))
  
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
                (let uu____2527 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____2527))
               &&
               (let uu____2534 = FStar_Syntax_Util.head_and_args' e  in
                match uu____2534 with
                | (head1,uu____2548) ->
                    let uu____2565 =
                      let uu____2566 = FStar_Syntax_Util.un_uinst head1  in
                      uu____2566.FStar_Syntax_Syntax.n  in
                    (match uu____2565 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____2570 =
                           let uu____2571 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____2571
                            in
                         Prims.op_Negation uu____2570
                     | uu____2572 -> true)))
              &&
              (let uu____2574 = should_not_inline_lc lc  in
               Prims.op_Negation uu____2574)
  
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
            let uu____2608 =
              let uu____2609 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____2609  in
            if uu____2608
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____2611 = FStar_Syntax_Util.is_unit t  in
               if uu____2611
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
                    let uu____2617 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____2617
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____2619 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____2619 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____2629 =
                             let uu____2630 =
                               let uu____2635 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____2636 =
                                 let uu____2637 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____2644 =
                                   let uu____2653 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____2653]  in
                                 uu____2637 :: uu____2644  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____2635
                                 uu____2636
                                in
                             uu____2630 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____2629)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____2681 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____2681
           then
             let uu____2682 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____2683 = FStar_Syntax_Print.term_to_string v1  in
             let uu____2684 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____2682 uu____2683 uu____2684
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____2697 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___321_2701  ->
              match uu___321_2701 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____2702 -> false))
       in
    if uu____2697
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___322_2711  ->
              match uu___322_2711 with
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
        let uu____2730 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____2730
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____2733 = destruct_comp c1  in
           match uu____2733 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____2747 =
                   let uu____2752 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____2753 =
                     let uu____2754 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____2761 =
                       let uu____2770 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____2777 =
                         let uu____2786 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____2786]  in
                       uu____2770 :: uu____2777  in
                     uu____2754 :: uu____2761  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____2752 uu____2753  in
                 uu____2747 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____2819 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____2819)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____2842 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____2844 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____2844
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____2847 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____2847 weaken
  
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
               let uu____2890 = destruct_comp c1  in
               match uu____2890 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____2904 =
                       let uu____2909 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____2910 =
                         let uu____2911 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____2918 =
                           let uu____2927 =
                             let uu____2934 =
                               let uu____2935 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____2935 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____2934
                              in
                           let uu____2942 =
                             let uu____2951 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____2951]  in
                           uu____2927 :: uu____2942  in
                         uu____2911 :: uu____2918  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____2909 uu____2910
                        in
                     uu____2904 FStar_Pervasives_Native.None
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
            let uu____3026 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____3026
            then (lc, g0)
            else
              (let flags1 =
                 let uu____3035 =
                   let uu____3042 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____3042
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____3035 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____3062 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___323_3070  ->
                               match uu___323_3070 with
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
                               | uu____3073 -> []))
                        in
                     FStar_List.append flags1 uu____3062
                  in
               let strengthen uu____3079 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____3083 = FStar_TypeChecker_Env.guard_form g01  in
                    match uu____3083 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____3086 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____3086
                          then
                            let uu____3087 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____3088 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____3087 uu____3088
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____3090 =
                 let uu____3091 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____3091
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____3090,
                 (let uu___343_3093 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___343_3093.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___343_3093.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___343_3093.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___324_3100  ->
            match uu___324_3100 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____3101 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____3128 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____3128
          then e
          else
            (let uu____3132 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____3134 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____3134)
                in
             if uu____3132
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
          fun uu____3184  ->
            match uu____3184 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____3204 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____3204 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____3212 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____3212
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____3219 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____3219
                       then
                         let uu____3222 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____3222
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____3226 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____3226
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____3231 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____3231
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____3235 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____3235
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____3244 =
                  let uu____3245 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____3245
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
                       (fun uu____3259  ->
                          let uu____3260 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____3261 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____3263 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____3260 uu____3261 uu____3263);
                     (let aux uu____3277 =
                        let uu____3278 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____3278
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____3299 ->
                              let uu____3300 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____3300
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____3319 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____3319
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____3390 =
                              let uu____3395 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____3395, reason)  in
                            FStar_Util.Inl uu____3390
                        | uu____3402 -> aux ()  in
                      let try_simplify uu____3426 =
                        let rec maybe_close t x c =
                          let uu____3443 =
                            let uu____3444 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____3444.FStar_Syntax_Syntax.n  in
                          match uu____3443 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____3448) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____3454 -> c  in
                        let uu____3455 =
                          let uu____3456 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____3456  in
                        if uu____3455
                        then
                          let uu____3467 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____3467
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____3481 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____3481))
                        else
                          (let uu____3491 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____3491
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____3501 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____3501
                              then
                                let uu____3510 =
                                  let uu____3515 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____3515, "both gtot")  in
                                FStar_Util.Inl uu____3510
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____3539 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____3541 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____3541)
                                        in
                                     if uu____3539
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___344_3554 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___344_3554.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___344_3554.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____3555 =
                                         let uu____3560 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____3560, "c1 Tot")  in
                                       FStar_Util.Inl uu____3555
                                     else aux ()
                                 | uu____3566 -> aux ())))
                         in
                      let uu____3575 = try_simplify ()  in
                      match uu____3575 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____3595  ->
                                let uu____3596 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____3596);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____3605  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____3626 = lift_and_destruct env c11 c21
                                 in
                              match uu____3626 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3679 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____3679]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____3693 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____3693]
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
                                    let uu____3732 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____3739 =
                                      let uu____3748 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____3755 =
                                        let uu____3764 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____3771 =
                                          let uu____3780 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____3787 =
                                            let uu____3796 =
                                              let uu____3803 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____3803
                                               in
                                            [uu____3796]  in
                                          uu____3780 :: uu____3787  in
                                        uu____3764 :: uu____3771  in
                                      uu____3748 :: uu____3755  in
                                    uu____3732 :: uu____3739  in
                                  let wp =
                                    let uu____3843 =
                                      let uu____3848 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____3848 wp_args
                                       in
                                    uu____3843 FStar_Pervasives_Native.None
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
                              let uu____3873 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____3873 with
                              | (m,uu____3881,lift2) ->
                                  let c23 =
                                    let uu____3884 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____3884
                                     in
                                  let uu____3885 = destruct_comp c12  in
                                  (match uu____3885 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____3899 =
                                           let uu____3904 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3905 =
                                             let uu____3906 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____3913 =
                                               let uu____3922 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____3922]  in
                                             uu____3906 :: uu____3913  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____3904 uu____3905
                                            in
                                         uu____3899
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
                            let uu____3953 = destruct_comp c1_typ  in
                            match uu____3953 with
                            | (u_res_t1,res_t1,uu____3962) ->
                                let uu____3963 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____3963
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____3966 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____3966
                                   then
                                     (debug1
                                        (fun uu____3974  ->
                                           let uu____3975 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____3976 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____3975 uu____3976);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____3981 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____3983 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____3983)
                                         in
                                      if uu____3981
                                      then
                                        let e1' =
                                          let uu____4003 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____4003
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____4012  ->
                                              let uu____4013 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____4014 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____4013 uu____4014);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____4026  ->
                                              let uu____4027 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____4028 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____4027 uu____4028);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____4033 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____4033
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
      | uu____4049 -> g2
  
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
            (let uu____4071 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____4071)
           in
        let flags1 =
          if should_return1
          then
            let uu____4077 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____4077
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____4089 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____4093 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____4093
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____4097 =
              let uu____4098 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____4098  in
            (if uu____4097
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___345_4103 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___345_4103.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___345_4103.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___345_4103.FStar_Syntax_Syntax.effect_args);
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
               let uu____4114 =
                 let uu____4115 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____4115
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____4114
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____4118 =
               let uu____4119 =
                 let uu____4120 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____4120
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____4119  in
             FStar_Syntax_Util.comp_set_flags uu____4118 flags1)
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
            fun uu____4155  ->
              match uu____4155 with
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
                    let uu____4167 =
                      ((let uu____4170 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____4170) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____4167
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____4184 =
        let uu____4185 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____4185  in
      FStar_Syntax_Syntax.fvar uu____4184 FStar_Syntax_Syntax.delta_constant
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
               fun uu____4251  ->
                 match uu____4251 with
                 | (uu____4264,eff_label,uu____4266,uu____4267) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____4278 =
          let uu____4285 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____4319  ->
                    match uu____4319 with
                    | (uu____4332,uu____4333,flags1,uu____4335) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___325_4349  ->
                                match uu___325_4349 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____4350 -> false))))
             in
          if uu____4285
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____4278 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____4373 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____4375 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____4375
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____4413 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____4414 =
                     let uu____4419 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____4420 =
                       let uu____4421 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____4428 =
                         let uu____4437 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____4444 =
                           let uu____4453 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____4460 =
                             let uu____4469 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____4469]  in
                           uu____4453 :: uu____4460  in
                         uu____4437 :: uu____4444  in
                       uu____4421 :: uu____4428  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____4419 uu____4420  in
                   uu____4414 FStar_Pervasives_Native.None uu____4413  in
                 let default_case =
                   let post_k =
                     let uu____4512 =
                       let uu____4519 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____4519]  in
                     let uu____4532 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4512 uu____4532  in
                   let kwp =
                     let uu____4538 =
                       let uu____4545 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____4545]  in
                     let uu____4558 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____4538 uu____4558  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____4565 =
                       let uu____4566 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____4566]  in
                     let uu____4579 =
                       let uu____4582 =
                         let uu____4589 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____4589
                          in
                       let uu____4590 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____4582 uu____4590  in
                     FStar_Syntax_Util.abs uu____4565 uu____4579
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
                   let uu____4612 =
                     should_not_inline_whole_match ||
                       (let uu____4614 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____4614)
                      in
                   if uu____4612 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____4647  ->
                        fun celse  ->
                          match uu____4647 with
                          | (g,eff_label,uu____4663,cthen) ->
                              let uu____4675 =
                                let uu____4700 =
                                  let uu____4701 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____4701
                                   in
                                lift_and_destruct env uu____4700 celse  in
                              (match uu____4675 with
                               | ((md,uu____4703,uu____4704),(uu____4705,uu____4706,wp_then),
                                  (uu____4708,uu____4709,wp_else)) ->
                                   let uu____4729 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____4729 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____4743::[] -> comp
                 | uu____4783 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____4801 = destruct_comp comp1  in
                     (match uu____4801 with
                      | (uu____4808,uu____4809,wp) ->
                          let wp1 =
                            let uu____4814 =
                              let uu____4819 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____4820 =
                                let uu____4821 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____4828 =
                                  let uu____4837 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____4837]  in
                                uu____4821 :: uu____4828  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____4819
                                uu____4820
                               in
                            uu____4814 FStar_Pervasives_Native.None
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
          let uu____4896 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____4896 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____4911 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____4916 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____4911 uu____4916
              else
                (let uu____4924 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____4929 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____4924 uu____4929)
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
               let uu____4973 =
                 let uu____4974 = FStar_Syntax_Subst.compress t2  in
                 uu____4974.FStar_Syntax_Syntax.n  in
               match uu____4973 with
               | FStar_Syntax_Syntax.Tm_type uu____4977 -> true
               | uu____4978 -> false  in
             let uu____4979 =
               let uu____4980 =
                 FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ
                  in
               uu____4980.FStar_Syntax_Syntax.n  in
             match uu____4979 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bool_lid)
                   && (is_type1 t)
                 ->
                 let uu____4988 =
                   FStar_TypeChecker_Env.lookup_lid env
                     FStar_Parser_Const.b2t_lid
                    in
                 let b2t1 =
                   let uu____4998 =
                     FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                       e.FStar_Syntax_Syntax.pos
                      in
                   FStar_Syntax_Syntax.fvar uu____4998
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 let lc1 =
                   let uu____5000 =
                     let uu____5001 =
                       let uu____5002 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                         uu____5002
                        in
                     (FStar_Pervasives_Native.None, uu____5001)  in
                   bind e.FStar_Syntax_Syntax.pos env
                     (FStar_Pervasives_Native.Some e) lc uu____5000
                    in
                 let e1 =
                   let uu____5008 =
                     let uu____5013 =
                       let uu____5014 = FStar_Syntax_Syntax.as_arg e  in
                       [uu____5014]  in
                     FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____5013  in
                   uu____5008 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
                    in
                 (e1, lc1)
             | uu____5035 -> (e, lc))
  
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
          (let uu____5069 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____5069
           then
             let uu____5070 = FStar_Syntax_Print.term_to_string e  in
             let uu____5071 = FStar_Syntax_Print.lcomp_to_string lc  in
             let uu____5072 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____5070 uu____5071 uu____5072
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____5078 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_Syntax_Syntax.eff_name
                   in
                match uu____5078 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____5101 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____5123 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____5123, false)
             else
               (let uu____5129 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_Syntax_Syntax.res_typ t
                   in
                (uu____5129, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____5140) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____5149 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_Syntax_Syntax.res_typ
                    in
                 FStar_Errors.raise_error uu____5149
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_Syntax_Syntax.res_typ t;
                  (e,
                    ((let uu___346_5163 = lc  in
                      {
                        FStar_Syntax_Syntax.eff_name =
                          (uu___346_5163.FStar_Syntax_Syntax.eff_name);
                        FStar_Syntax_Syntax.res_typ = t;
                        FStar_Syntax_Syntax.cflags =
                          (uu___346_5163.FStar_Syntax_Syntax.cflags);
                        FStar_Syntax_Syntax.comp_thunk =
                          (uu___346_5163.FStar_Syntax_Syntax.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____5168 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____5168 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let uu____5175 = FStar_Syntax_Util.set_result_typ_lc lc t
                       in
                    (e, uu____5175, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___347_5178 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___347_5178.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___347_5178.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___347_5178.FStar_TypeChecker_Env.implicits)
                      }  in
                    let strengthen uu____5184 =
                      let uu____5185 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____5185
                      then FStar_Syntax_Syntax.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.Eager_unfolding;
                             FStar_TypeChecker_Normalize.Simplify;
                             FStar_TypeChecker_Normalize.Primops] env f
                            in
                         let uu____5188 =
                           let uu____5189 = FStar_Syntax_Subst.compress f1
                              in
                           uu____5189.FStar_Syntax_Syntax.n  in
                         match uu____5188 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____5192,{
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____5194;
                                           FStar_Syntax_Syntax.vars =
                                             uu____5195;_},uu____5196)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___348_5218 = lc  in
                               {
                                 FStar_Syntax_Syntax.eff_name =
                                   (uu___348_5218.FStar_Syntax_Syntax.eff_name);
                                 FStar_Syntax_Syntax.res_typ = t;
                                 FStar_Syntax_Syntax.cflags =
                                   (uu___348_5218.FStar_Syntax_Syntax.cflags);
                                 FStar_Syntax_Syntax.comp_thunk =
                                   (uu___348_5218.FStar_Syntax_Syntax.comp_thunk)
                               }  in
                             FStar_Syntax_Syntax.lcomp_comp lc1
                         | uu____5219 ->
                             let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                             ((let uu____5222 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   FStar_Options.Extreme
                                  in
                               if uu____5222
                               then
                                 let uu____5223 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env lc.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____5224 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env t
                                    in
                                 let uu____5225 =
                                   FStar_TypeChecker_Normalize.comp_to_string
                                     env c
                                    in
                                 let uu____5226 =
                                   FStar_TypeChecker_Normalize.term_to_string
                                     env f1
                                    in
                                 FStar_Util.print4
                                   "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                   uu____5223 uu____5224 uu____5225
                                   uu____5226
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
                                   let uu____5235 =
                                     let uu____5240 =
                                       let uu____5241 =
                                         FStar_Syntax_Syntax.as_arg xexp  in
                                       [uu____5241]  in
                                     FStar_Syntax_Syntax.mk_Tm_app f1
                                       uu____5240
                                      in
                                   uu____5235 FStar_Pervasives_Native.None
                                     f1.FStar_Syntax_Syntax.pos
                                 else f1  in
                               let uu____5263 =
                                 let uu____5268 =
                                   FStar_All.pipe_left
                                     (fun _0_16  ->
                                        FStar_Pervasives_Native.Some _0_16)
                                     (FStar_TypeChecker_Err.subtyping_failed
                                        env lc.FStar_Syntax_Syntax.res_typ t)
                                    in
                                 let uu____5285 =
                                   FStar_TypeChecker_Env.set_range env
                                     e.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____5286 =
                                   FStar_Syntax_Util.lcomp_of_comp cret  in
                                 let uu____5287 =
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                     (FStar_TypeChecker_Common.NonTrivial
                                        guard)
                                    in
                                 strengthen_precondition uu____5268
                                   uu____5285 e uu____5286 uu____5287
                                  in
                               match uu____5263 with
                               | (eq_ret,_trivial_so_ok_to_discard) ->
                                   let x1 =
                                     let uu___349_5291 = x  in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___349_5291.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___349_5291.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (lc.FStar_Syntax_Syntax.res_typ)
                                     }  in
                                   let c1 =
                                     let uu____5293 =
                                       FStar_Syntax_Util.lcomp_of_comp c  in
                                     bind e.FStar_Syntax_Syntax.pos env
                                       (FStar_Pervasives_Native.Some e)
                                       uu____5293
                                       ((FStar_Pervasives_Native.Some x1),
                                         eq_ret)
                                      in
                                   let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                      in
                                   ((let uu____5298 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         FStar_Options.Extreme
                                        in
                                     if uu____5298
                                     then
                                       let uu____5299 =
                                         FStar_TypeChecker_Normalize.comp_to_string
                                           env c2
                                          in
                                       FStar_Util.print1
                                         "Strengthened to %s\n" uu____5299
                                     else ());
                                    c2))))
                       in
                    let flags1 =
                      FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                        (FStar_List.collect
                           (fun uu___326_5309  ->
                              match uu___326_5309 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____5312 -> []))
                       in
                    let lc1 =
                      let uu____5314 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_Syntax_Syntax.eff_name
                         in
                      FStar_Syntax_Syntax.mk_lcomp uu____5314 t flags1
                        strengthen
                       in
                    let g2 =
                      let uu___350_5316 = g1  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Env.deferred =
                          (uu___350_5316.FStar_TypeChecker_Env.deferred);
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___350_5316.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___350_5316.FStar_TypeChecker_Env.implicits)
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
        let uu____5351 =
          let uu____5354 =
            let uu____5359 =
              let uu____5360 =
                let uu____5367 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____5367  in
              [uu____5360]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____5359  in
          uu____5354 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____5351  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____5388 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____5388
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____5404 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____5419 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____5435 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____5435
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____5449)::(ens,uu____5451)::uu____5452 ->
                    let uu____5481 =
                      let uu____5484 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____5484  in
                    let uu____5485 =
                      let uu____5486 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____5486  in
                    (uu____5481, uu____5485)
                | uu____5489 ->
                    let uu____5498 =
                      let uu____5503 =
                        let uu____5504 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____5504
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____5503)
                       in
                    FStar_Errors.raise_error uu____5498
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____5520)::uu____5521 ->
                    let uu____5540 =
                      let uu____5545 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____5545
                       in
                    (match uu____5540 with
                     | (us_r,uu____5577) ->
                         let uu____5578 =
                           let uu____5583 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____5583
                            in
                         (match uu____5578 with
                          | (us_e,uu____5615) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____5618 =
                                  let uu____5619 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5619
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5618
                                  us_r
                                 in
                              let as_ens =
                                let uu____5621 =
                                  let uu____5622 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____5622
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____5621
                                  us_e
                                 in
                              let req =
                                let uu____5626 =
                                  let uu____5631 =
                                    let uu____5632 =
                                      let uu____5641 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5641]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5632
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____5631
                                   in
                                uu____5626 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____5673 =
                                  let uu____5678 =
                                    let uu____5679 =
                                      let uu____5688 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____5688]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____5679
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____5678
                                   in
                                uu____5673 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____5717 =
                                let uu____5720 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____5720  in
                              let uu____5721 =
                                let uu____5722 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____5722  in
                              (uu____5717, uu____5721)))
                | uu____5725 -> failwith "Impossible"))
  
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
      (let uu____5755 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____5755
       then
         let uu____5756 = FStar_Syntax_Print.term_to_string tm  in
         let uu____5757 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____5756 uu____5757
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
        (let uu____5801 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____5801
         then
           let uu____5802 = FStar_Syntax_Print.term_to_string tm  in
           let uu____5803 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____5802
             uu____5803
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____5810 =
      let uu____5811 =
        let uu____5812 = FStar_Syntax_Subst.compress t  in
        uu____5812.FStar_Syntax_Syntax.n  in
      match uu____5811 with
      | FStar_Syntax_Syntax.Tm_app uu____5815 -> false
      | uu____5830 -> true  in
    if uu____5810
    then t
    else
      (let uu____5832 = FStar_Syntax_Util.head_and_args t  in
       match uu____5832 with
       | (head1,args) ->
           let uu____5869 =
             let uu____5870 =
               let uu____5871 = FStar_Syntax_Subst.compress head1  in
               uu____5871.FStar_Syntax_Syntax.n  in
             match uu____5870 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____5874 -> false  in
           if uu____5869
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____5896 ->
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
             let uu____5941 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____5941 with
             | (formals,uu____5955) ->
                 let n_implicits =
                   let uu____5973 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____6051  ->
                             match uu____6051 with
                             | (uu____6058,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____5973 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____6191 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____6191 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____6215 =
                     let uu____6220 =
                       let uu____6221 = FStar_Util.string_of_int n_expected
                          in
                       let uu____6228 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6229 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____6221 uu____6228 uu____6229
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____6220)
                      in
                   let uu____6236 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____6215 uu____6236
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___327_6259 =
             match uu___327_6259 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____6289 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____6289 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_17,uu____6404) when
                          _0_17 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Env.trivial_guard)
                      | (uu____6447,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____6480 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____6480 with
                           | (v1,uu____6520,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____6539 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____6539 with
                                | (args,bs3,subst3,g') ->
                                    let uu____6632 =
                                      FStar_TypeChecker_Env.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____6632)))
                      | (uu____6659,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Env.trivial_guard)
                       in
                    let uu____6705 =
                      let uu____6732 = inst_n_binders t  in
                      aux [] uu____6732 bs1  in
                    (match uu____6705 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____6803) -> (e, torig, guard)
                          | (uu____6834,[]) when
                              let uu____6865 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____6865 ->
                              (e, torig, FStar_TypeChecker_Env.trivial_guard)
                          | uu____6866 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____6894 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____6907 -> (e, t, FStar_TypeChecker_Env.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____6917 =
      let uu____6920 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____6920
        (FStar_List.map
           (fun u  ->
              let uu____6930 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____6930 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____6917 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____6951 = FStar_Util.set_is_empty x  in
      if uu____6951
      then []
      else
        (let s =
           let uu____6966 =
             let uu____6969 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____6969  in
           FStar_All.pipe_right uu____6966 FStar_Util.set_elements  in
         (let uu____6985 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____6985
          then
            let uu____6986 =
              let uu____6987 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____6987  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____6986
          else ());
         (let r =
            let uu____6994 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____6994  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____7033 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____7033
                     then
                       let uu____7034 =
                         let uu____7035 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____7035
                          in
                       let uu____7036 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____7037 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____7034 uu____7036 uu____7037
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
        let uu____7063 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____7063 FStar_Util.set_elements  in
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
        | ([],uu____7101) -> generalized_univ_names
        | (uu____7108,[]) -> explicit_univ_names
        | uu____7115 ->
            let uu____7124 =
              let uu____7129 =
                let uu____7130 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____7130
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____7129)
               in
            FStar_Errors.raise_error uu____7124 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____7148 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____7148
       then
         let uu____7149 = FStar_Syntax_Print.term_to_string t  in
         let uu____7150 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____7149 uu____7150
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____7156 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____7156
        then
          let uu____7157 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____7157
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____7163 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____7163
         then
           let uu____7164 = FStar_Syntax_Print.term_to_string t  in
           let uu____7165 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____7164 uu____7165
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
        let uu____7243 =
          let uu____7244 =
            FStar_Util.for_all
              (fun uu____7257  ->
                 match uu____7257 with
                 | (uu____7266,uu____7267,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____7244  in
        if uu____7243
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____7315 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____7315
              then
                let uu____7316 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____7316
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____7320 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____7320
               then
                 let uu____7321 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____7321
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____7336 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____7336 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____7370 =
             match uu____7370 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____7407 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____7407
                   then
                     let uu____7408 =
                       let uu____7409 =
                         let uu____7412 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____7412
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____7409
                         (FStar_String.concat ", ")
                        in
                     let uu____7455 =
                       let uu____7456 =
                         let uu____7459 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____7459
                           (FStar_List.map
                              (fun u  ->
                                 let uu____7470 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____7471 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____7470
                                   uu____7471))
                          in
                       FStar_All.pipe_right uu____7456
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____7408
                       uu____7455
                   else ());
                  (let univs2 =
                     let uu____7478 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____7490 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____7490) univs1
                       uu____7478
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____7497 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____7497
                    then
                      let uu____7498 =
                        let uu____7499 =
                          let uu____7502 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____7502
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____7499
                          (FStar_String.concat ", ")
                         in
                      let uu____7545 =
                        let uu____7546 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____7557 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____7558 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____7557
                                    uu____7558))
                           in
                        FStar_All.pipe_right uu____7546
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____7498
                        uu____7545
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____7572 =
             let uu____7589 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____7589  in
           match uu____7572 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____7679 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____7679
                 then ()
                 else
                   (let uu____7681 = lec_hd  in
                    match uu____7681 with
                    | (lb1,uu____7689,uu____7690) ->
                        let uu____7691 = lec2  in
                        (match uu____7691 with
                         | (lb2,uu____7699,uu____7700) ->
                             let msg =
                               let uu____7702 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7703 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____7702 uu____7703
                                in
                             let uu____7704 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____7704))
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
                 let uu____7768 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____7768
                 then ()
                 else
                   (let uu____7770 = lec_hd  in
                    match uu____7770 with
                    | (lb1,uu____7778,uu____7779) ->
                        let uu____7780 = lec2  in
                        (match uu____7780 with
                         | (lb2,uu____7788,uu____7789) ->
                             let msg =
                               let uu____7791 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____7792 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____7791 uu____7792
                                in
                             let uu____7793 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____7793))
                  in
               let lecs1 =
                 let uu____7803 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____7856 = univs_and_uvars_of_lec this_lec  in
                        match uu____7856 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____7803 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____7957 = lec_hd  in
                   match uu____7957 with
                   | (lbname,e,c) ->
                       let uu____7967 =
                         let uu____7972 =
                           let uu____7973 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____7974 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____7975 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____7973 uu____7974 uu____7975
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____7972)
                          in
                       let uu____7976 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____7967 uu____7976
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____7997 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____7997 with
                         | FStar_Pervasives_Native.Some uu____8006 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____8013 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____8017 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____8017 with
                              | (bs,kres) ->
                                  ((let uu____8055 =
                                      let uu____8056 =
                                        let uu____8059 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine uu____8059
                                         in
                                      uu____8056.FStar_Syntax_Syntax.n  in
                                    match uu____8055 with
                                    | FStar_Syntax_Syntax.Tm_type uu____8060
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____8064 =
                                          let uu____8065 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____8065  in
                                        if uu____8064 then fail1 kres else ()
                                    | uu____8067 -> fail1 kres);
                                   (let a =
                                      let uu____8069 =
                                        let uu____8072 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_18  ->
                                             FStar_Pervasives_Native.Some
                                               _0_18) uu____8072
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____8069
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____8080 ->
                                          let uu____8087 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs uu____8087
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
                      (fun uu____8194  ->
                         match uu____8194 with
                         | (lbname,e,c) ->
                             let uu____8242 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____8317 ->
                                   let uu____8332 = (e, c)  in
                                   (match uu____8332 with
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
                                                (fun uu____8375  ->
                                                   match uu____8375 with
                                                   | (x,uu____8383) ->
                                                       let uu____8388 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____8388)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____8406 =
                                                let uu____8407 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____8407
                                                 in
                                              if uu____8406
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
                                          let uu____8413 =
                                            let uu____8414 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____8414.FStar_Syntax_Syntax.n
                                             in
                                          match uu____8413 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____8435 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____8435 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____8448 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____8452 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____8452, gen_tvars))
                                in
                             (match uu____8242 with
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
        (let uu____8606 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____8606
         then
           let uu____8607 =
             let uu____8608 =
               FStar_List.map
                 (fun uu____8621  ->
                    match uu____8621 with
                    | (lb,uu____8629,uu____8630) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____8608 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____8607
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____8651  ->
                match uu____8651 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____8680 = gen env is_rec lecs  in
           match uu____8680 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____8779  ->
                       match uu____8779 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____8841 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____8841
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____8887  ->
                           match uu____8887 with
                           | (l,us,e,c,gvs) ->
                               let uu____8921 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____8922 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____8923 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____8924 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____8925 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____8921 uu____8922 uu____8923 uu____8924
                                 uu____8925))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____8966  ->
                match uu____8966 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____9010 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____9010, t, c, gvs)) univnames_lecs
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
              (let uu____9067 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____9067 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____9073 = FStar_TypeChecker_Env.apply_guard f e  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____9073)
             in
          let is_var e1 =
            let uu____9082 =
              let uu____9083 = FStar_Syntax_Subst.compress e1  in
              uu____9083.FStar_Syntax_Syntax.n  in
            match uu____9082 with
            | FStar_Syntax_Syntax.Tm_name uu____9086 -> true
            | uu____9087 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___351_9107 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___351_9107.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___351_9107.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____9108 -> e2  in
          let env2 =
            let uu___352_9110 = env1  in
            let uu____9111 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___352_9110.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___352_9110.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___352_9110.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___352_9110.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___352_9110.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___352_9110.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___352_9110.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___352_9110.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___352_9110.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___352_9110.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___352_9110.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___352_9110.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___352_9110.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___352_9110.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___352_9110.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___352_9110.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____9111;
              FStar_TypeChecker_Env.is_iface =
                (uu___352_9110.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___352_9110.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___352_9110.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___352_9110.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___352_9110.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___352_9110.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___352_9110.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___352_9110.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___352_9110.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___352_9110.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___352_9110.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___352_9110.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___352_9110.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___352_9110.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___352_9110.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___352_9110.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___352_9110.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___352_9110.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___352_9110.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___352_9110.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___352_9110.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___352_9110.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___352_9110.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____9112 = check1 env2 t1 t2  in
          match uu____9112 with
          | FStar_Pervasives_Native.None  ->
              let uu____9119 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____9124 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____9119 uu____9124
          | FStar_Pervasives_Native.Some g ->
              ((let uu____9131 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____9131
                then
                  let uu____9132 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____9132
                else ());
               (let uu____9134 = decorate e t2  in (uu____9134, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____9159 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____9159
         then
           let uu____9160 = FStar_Syntax_Print.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____9160
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_Syntax_Util.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____9170 = FStar_Syntax_Util.is_total_lcomp lc  in
         if uu____9170
         then
           let uu____9175 = discharge g1  in
           let uu____9176 = FStar_Syntax_Syntax.lcomp_comp lc  in
           (uu____9175, uu____9176)
         else
           (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
            let steps =
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.NoFullNorm;
              FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
            let c1 =
              let uu____9183 =
                let uu____9184 =
                  let uu____9185 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                  FStar_All.pipe_right uu____9185 FStar_Syntax_Syntax.mk_Comp
                   in
                FStar_All.pipe_right uu____9184
                  (FStar_TypeChecker_Normalize.normalize_comp steps env)
                 in
              FStar_All.pipe_right uu____9183
                (FStar_TypeChecker_Env.comp_to_comp_typ env)
               in
            let md =
              FStar_TypeChecker_Env.get_effect_decl env
                c1.FStar_Syntax_Syntax.effect_name
               in
            let uu____9187 = destruct_comp c1  in
            match uu____9187 with
            | (u_t,t,wp) ->
                let vc =
                  let uu____9204 = FStar_TypeChecker_Env.get_range env  in
                  let uu____9205 =
                    let uu____9210 =
                      FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                        md.FStar_Syntax_Syntax.trivial
                       in
                    let uu____9211 =
                      let uu____9212 = FStar_Syntax_Syntax.as_arg t  in
                      let uu____9219 =
                        let uu____9228 = FStar_Syntax_Syntax.as_arg wp  in
                        [uu____9228]  in
                      uu____9212 :: uu____9219  in
                    FStar_Syntax_Syntax.mk_Tm_app uu____9210 uu____9211  in
                  uu____9205 FStar_Pervasives_Native.None uu____9204  in
                ((let uu____9256 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Simplification")
                     in
                  if uu____9256
                  then
                    let uu____9257 = FStar_Syntax_Print.term_to_string vc  in
                    FStar_Util.print1 "top-level VC: %s\n" uu____9257
                  else ());
                 (let g2 =
                    let uu____9260 =
                      FStar_All.pipe_left
                        FStar_TypeChecker_Env.guard_of_guard_formula
                        (FStar_TypeChecker_Common.NonTrivial vc)
                       in
                    FStar_TypeChecker_Env.conj_guard g1 uu____9260  in
                  let uu____9261 = discharge g2  in
                  let uu____9262 = FStar_Syntax_Syntax.mk_Comp c1  in
                  (uu____9261, uu____9262)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___328_9294 =
        match uu___328_9294 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____9302)::[] -> f fst1
        | uu____9319 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____9330 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____9330
          (fun _0_20  -> FStar_TypeChecker_Common.NonTrivial _0_20)
         in
      let op_or_e e =
        let uu____9341 =
          let uu____9342 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____9342  in
        FStar_All.pipe_right uu____9341
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_or_t t =
        let uu____9361 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____9361
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let short_op_ite uu___329_9375 =
        match uu___329_9375 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____9383)::[] -> FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____9402)::[] ->
            let uu____9431 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____9431
              (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
        | uu____9432 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____9443 =
          let uu____9451 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____9451)  in
        let uu____9459 =
          let uu____9469 =
            let uu____9477 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____9477)  in
          let uu____9485 =
            let uu____9495 =
              let uu____9503 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____9503)  in
            let uu____9511 =
              let uu____9521 =
                let uu____9529 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____9529)  in
              let uu____9537 =
                let uu____9547 =
                  let uu____9555 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____9555)  in
                [uu____9547; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____9521 :: uu____9537  in
            uu____9495 :: uu____9511  in
          uu____9469 :: uu____9485  in
        uu____9443 :: uu____9459  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____9617 =
            FStar_Util.find_map table
              (fun uu____9632  ->
                 match uu____9632 with
                 | (x,mk1) ->
                     let uu____9649 = FStar_Ident.lid_equals x lid  in
                     if uu____9649
                     then
                       let uu____9652 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____9652
                     else FStar_Pervasives_Native.None)
             in
          (match uu____9617 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____9655 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____9661 =
      let uu____9662 = FStar_Syntax_Util.un_uinst l  in
      uu____9662.FStar_Syntax_Syntax.n  in
    match uu____9661 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____9666 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____9696)::uu____9697 -> FStar_Syntax_Syntax.range_of_bv hd1
        | uu____9708 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____9715,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____9716))::uu____9717 -> bs
      | uu____9728 ->
          let uu____9729 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____9729 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____9733 =
                 let uu____9734 = FStar_Syntax_Subst.compress t  in
                 uu____9734.FStar_Syntax_Syntax.n  in
               (match uu____9733 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____9738) ->
                    let uu____9755 =
                      FStar_Util.prefix_until
                        (fun uu___330_9795  ->
                           match uu___330_9795 with
                           | (uu____9802,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____9803)) ->
                               false
                           | uu____9806 -> true) bs'
                       in
                    (match uu____9755 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____9841,uu____9842) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____9914,uu____9915) ->
                         let uu____9988 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____10006  ->
                                   match uu____10006 with
                                   | (x,uu____10014) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____9988
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____10057  ->
                                     match uu____10057 with
                                     | (x,i) ->
                                         let uu____10076 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____10076, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____10084 -> bs))
  
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
            let uu____10112 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____10112
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
          let uu____10139 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____10139
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
        (let uu____10174 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____10174
         then
           ((let uu____10176 = FStar_Ident.text_of_lid lident  in
             d uu____10176);
            (let uu____10177 = FStar_Ident.text_of_lid lident  in
             let uu____10178 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____10177 uu____10178))
         else ());
        (let fv =
           let uu____10181 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____10181
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
         let uu____10191 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___353_10193 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___353_10193.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___353_10193.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___353_10193.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___353_10193.FStar_Syntax_Syntax.sigattrs)
           }), uu____10191))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___331_10209 =
        match uu___331_10209 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10210 -> false  in
      let reducibility uu___332_10216 =
        match uu___332_10216 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____10217 -> false  in
      let assumption uu___333_10223 =
        match uu___333_10223 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____10224 -> false  in
      let reification uu___334_10230 =
        match uu___334_10230 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____10231 -> true
        | uu____10232 -> false  in
      let inferred uu___335_10238 =
        match uu___335_10238 with
        | FStar_Syntax_Syntax.Discriminator uu____10239 -> true
        | FStar_Syntax_Syntax.Projector uu____10240 -> true
        | FStar_Syntax_Syntax.RecordType uu____10245 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____10254 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____10263 -> false  in
      let has_eq uu___336_10269 =
        match uu___336_10269 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____10270 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____10334 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____10339 -> true  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____10349 =
        let uu____10350 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___337_10354  ->
                  match uu___337_10354 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____10355 -> false))
           in
        FStar_All.pipe_right uu____10350 Prims.op_Negation  in
      if uu____10349
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____10370 =
            let uu____10375 =
              let uu____10376 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____10376 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____10375)  in
          FStar_Errors.raise_error uu____10370 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____10388 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____10392 =
            let uu____10393 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____10393  in
          if uu____10392 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____10398),uu____10399) ->
              ((let uu____10409 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____10409
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____10413 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____10413
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____10419 ->
              let uu____10428 =
                let uu____10429 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____10429  in
              if uu____10428 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____10435 ->
              let uu____10442 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____10442 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____10446 ->
              let uu____10453 =
                let uu____10454 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____10454  in
              if uu____10453 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____10460 ->
              let uu____10461 =
                let uu____10462 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10462  in
              if uu____10461 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10468 ->
              let uu____10469 =
                let uu____10470 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____10470  in
              if uu____10469 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____10476 ->
              let uu____10489 =
                let uu____10490 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____10490  in
              if uu____10489 then err'1 () else ()
          | uu____10496 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____10530 =
          let uu____10531 = FStar_Syntax_Subst.compress t1  in
          uu____10531.FStar_Syntax_Syntax.n  in
        match uu____10530 with
        | FStar_Syntax_Syntax.Tm_type uu____10534 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____10537 =
                 let uu____10542 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____10542
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____10537
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____10560 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____10560
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____10577 =
                                 let uu____10578 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____10578.FStar_Syntax_Syntax.n  in
                               match uu____10577 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____10582 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____10583 ->
            let uu____10596 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____10596 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____10622 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____10622
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____10624;
               FStar_Syntax_Syntax.index = uu____10625;
               FStar_Syntax_Syntax.sort = t2;_},uu____10627)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____10635,uu____10636) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____10678::[]) ->
            let uu____10709 =
              let uu____10710 = FStar_Syntax_Util.un_uinst head1  in
              uu____10710.FStar_Syntax_Syntax.n  in
            (match uu____10709 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____10714 -> false)
        | uu____10715 -> false
      
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
        (let uu____10723 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____10723
         then
           let uu____10724 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____10724
         else ());
        res
       in aux g t
  