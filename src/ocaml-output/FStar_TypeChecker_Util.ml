open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____22 = FStar_TypeChecker_Env.get_range env  in
      let uu____23 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____22 uu____23
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
            FStar_Range.range) Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          FStar_TypeChecker_Env.new_implicit_var_aux reason r env k
            FStar_Syntax_Syntax.Strict FStar_Pervasives_Native.None
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun solve_deferred  ->
      fun xs  ->
        fun g  ->
          let uu____87 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____87
          then
            let uu____90 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____142  ->
                      match uu____142 with
                      | (uu____149,p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p))
               in
            match uu____90 with
            | (solve_now,defer) ->
                ((let uu____184 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____184
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____201  ->
                          match uu____201 with
                          | (s,p) ->
                              let uu____211 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____211)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____226  ->
                          match uu____226 with
                          | (s,p) ->
                              let uu____236 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____236) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_244 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_244.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred_to_tac =
                           (uu___49_244.FStar_TypeChecker_Common.deferred_to_tac);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_244.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_244.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___52_246 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_246.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac =
                        (uu___52_246.FStar_TypeChecker_Common.deferred_to_tac);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_246.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_246.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____263 =
        let uu____265 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____265  in
      if uu____263
      then
        let us =
          let uu____270 =
            let uu____274 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____274
             in
          FStar_All.pipe_right uu____270 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____293 =
            let uu____299 =
              let uu____301 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____301
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____299)  in
          FStar_Errors.log_issue r uu____293);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____324  ->
      match uu____324 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____335;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____337;
          FStar_Syntax_Syntax.lbpos = uu____338;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____373 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____373 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____411) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____418) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____473) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____509 = FStar_Options.ml_ish ()  in
                                if uu____509
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____531 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____531
                            then
                              let uu____534 = FStar_Range.string_of_range r
                                 in
                              let uu____536 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____534 uu____536
                            else ());
                           FStar_Util.Inl t2)
                      | uu____541 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____543 = aux e1  in
                      match uu____543 with
                      | FStar_Util.Inr c ->
                          let uu____549 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____549
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____554 =
                               let uu____560 =
                                 let uu____562 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____562
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____560)
                                in
                             FStar_Errors.raise_error uu____554 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____571 ->
               let uu____572 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____572 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____636 =
      match uu____636 with
      | (p,i) ->
          let uu____656 = decorated_pattern_as_term p  in
          (match uu____656 with
           | (vars,te) ->
               let uu____679 =
                 let uu____684 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____684)  in
               (vars, uu____679))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____698 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____698)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____702 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____702)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____706 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____729 =
          let uu____748 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____748 FStar_List.unzip  in
        (match uu____729 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____886 =
               let uu____887 =
                 let uu____888 =
                   let uu____905 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____905, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____888  in
               mk1 uu____887  in
             (vars1, uu____886))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____944,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____954,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____968 -> FStar_Pervasives_Native.Some hd1)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____983 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____983
      (fun uu____1011  ->
         match uu____1011 with | (c,g) -> ((comp_univ_opt c), g))
  
let (destruct_wp_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  = fun c  -> FStar_Syntax_Util.destruct_comp c 
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags  ->
            let uu____1084 =
              let uu____1085 =
                let uu____1096 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1096]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1085;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1084
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (effect_args_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool -> FStar_Range.range -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr  ->
    fun is_layered1  ->
      fun r  ->
        let err uu____1180 =
          let uu____1181 =
            let uu____1187 =
              let uu____1189 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1191 = FStar_Util.string_of_bool is_layered1  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1189 uu____1191
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1187)  in
          FStar_Errors.raise_error uu____1181 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered1
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1203,uu____1204::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1272 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1277,c) ->
               let uu____1299 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____1299
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1334 -> err ())
  
let (mk_wp_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let ret_wp =
                FStar_All.pipe_right ed
                  FStar_Syntax_Util.get_return_vc_combinator
                 in
              let wp =
                let uu____1370 =
                  let uu____1375 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                      ret_wp
                     in
                  let uu____1376 =
                    let uu____1377 = FStar_Syntax_Syntax.as_arg a  in
                    let uu____1386 =
                      let uu____1397 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____1397]  in
                    uu____1377 :: uu____1386  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____1375 uu____1376  in
                uu____1370 FStar_Pervasives_Native.None r  in
              mk_comp ed u_a a wp [FStar_Syntax_Syntax.RETURN]
  
let (mk_indexed_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              (let uu____1470 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1470
               then
                 let uu____1475 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1477 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1479 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1481 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1475 uu____1477 uu____1479 uu____1481
               else ());
              (let uu____1486 =
                 let uu____1491 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1491 [u_a]  in
               match uu____1486 with
               | (uu____1496,return_t) ->
                   let return_t_shape_error s =
                     let uu____1511 =
                       let uu____1513 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1515 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1513 uu____1515 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1511)  in
                   let uu____1519 =
                     let uu____1548 =
                       let uu____1549 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1549.FStar_Syntax_Syntax.n  in
                     match uu____1548 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1609 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1609 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1678 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1678))
                     | uu____1699 ->
                         let uu____1700 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1700 r
                      in
                   (match uu____1519 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1783 =
                          let uu____1790 =
                            let uu____1791 =
                              let uu____1792 =
                                let uu____1799 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1799, a)  in
                              FStar_Syntax_Syntax.NT uu____1792  in
                            let uu____1810 =
                              let uu____1813 =
                                let uu____1814 =
                                  let uu____1821 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1821, e)  in
                                FStar_Syntax_Syntax.NT uu____1814  in
                              [uu____1813]  in
                            uu____1791 :: uu____1810  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1790
                            (fun b  ->
                               let uu____1837 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1839 =
                                 let uu____1841 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1841
                                  in
                               let uu____1844 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1837 uu____1839 uu____1844) r
                           in
                        (match uu____1783 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst1 =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1881 =
                                        let uu____1888 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1888, t)  in
                                      FStar_Syntax_Syntax.NT uu____1881) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1914 =
                                 let uu____1917 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1918 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1917 uu____1918
                                   r
                                  in
                               FStar_All.pipe_right uu____1914
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst1))
                                in
                             let c =
                               let uu____1925 =
                                 let uu____1926 =
                                   FStar_All.pipe_right is
                                     (FStar_List.map
                                        FStar_Syntax_Syntax.as_arg)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs = [u_a];
                                   FStar_Syntax_Syntax.effect_name =
                                     (ed.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.result_typ = a;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____1926;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1925  in
                             ((let uu____1950 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1950
                               then
                                 let uu____1955 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1955
                               else ());
                              (c, g_uvars)))))
  
let (mk_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun e  ->
            fun r  ->
              let uu____1999 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1999
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2009 = mk_wp_return env ed u_a a e r  in
                 (uu____2009, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2034 =
          FStar_All.pipe_right
            (let uu___251_2036 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2036.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2036.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2036.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2036.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2034
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2057 =
          let uu____2062 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2063 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2062, uu____2063)  in
        match uu____2057 with
        | (l1,l2) ->
            let uu____2066 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2066 with
             | FStar_Pervasives_Native.Some (m,uu____2076,uu____2077) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2090 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2090 with
                  | FStar_Pervasives_Native.Some (m,uu____2104) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2137 =
                        let uu____2143 =
                          let uu____2145 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2147 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2145
                            uu____2147
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2143)
                         in
                      FStar_Errors.raise_error uu____2137
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2167 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____2167
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_TypeChecker_Common.eff_name
            c2.FStar_TypeChecker_Common.eff_name
  
let (lift_comps_sep_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2226 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2226 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2254 = lift_comp env c11 lift1  in
                (match uu____2254 with
                 | (c12,g1) ->
                     let uu____2271 =
                       if Prims.op_Negation for_bind
                       then lift_comp env c21 lift2
                       else
                         (let x_a =
                            match b with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Syntax.null_binder
                                  (FStar_Syntax_Util.comp_result c12)
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Syntax.mk_binder x
                             in
                          let env_x =
                            FStar_TypeChecker_Env.push_binders env [x_a]  in
                          let uu____2310 = lift_comp env_x c21 lift2  in
                          match uu____2310 with
                          | (c22,g2) ->
                              let uu____2321 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2321))
                        in
                     (match uu____2271 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2368 =
                  let uu____2369 =
                    let uu____2375 =
                      let uu____2377 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2379 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2377
                        uu____2379
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2375)
                     in
                  FStar_Errors.raise_error uu____2369 rng  in
                ((let uu____2394 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2394
                  then
                    let uu____2399 =
                      let uu____2401 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2401
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2403 =
                      let uu____2405 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2405
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2407 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2399 uu____2403 uu____2407
                  else ());
                 if for_bind
                 then err ()
                 else
                   (let bind_with_return ct ret_eff f_bind =
                      let x_bv =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          ct.FStar_Syntax_Syntax.result_typ
                         in
                      let uu____2463 =
                        let uu____2468 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2469 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2470 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2471 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2468 uu____2469 uu____2470
                          ct.FStar_Syntax_Syntax.result_typ uu____2471 rng
                         in
                      match uu____2463 with
                      | (c_ret,g_ret) ->
                          let uu____2478 =
                            let uu____2483 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2483 [] rng
                             in
                          (match uu____2478 with
                           | (c,g_bind) ->
                               let uu____2490 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2490))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2535 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2535
                      then
                        let uu____2571 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2571 with
                        | (p,f_bind) ->
                            let uu____2638 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2638
                             then
                               let uu____2651 = bind_with_return c12 p f_bind
                                  in
                               match uu____2651 with
                               | (c13,g) ->
                                   let uu____2668 =
                                     let uu____2677 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2677, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2668
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2706 =
                      let uu____2717 = try_lift c11 c21  in
                      match uu____2717 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2758 = try_lift c21 c11  in
                          (match uu____2758 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2706 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2815 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2815
                          then
                            let uu____2820 = FStar_Ident.string_of_lid p  in
                            let uu____2822 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2824 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2820 uu____2822 uu____2824
                          else ());
                         (p, c12, c22, g1, g2))))
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          Prims.bool ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun for_bind  ->
            let uu____2877 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2877 with
            | (l,c11,c21,g1,g2) ->
                let uu____2901 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2901)
  
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
  
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags  ->
          let uu____2957 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2957
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2969 =
      let uu____2970 = FStar_Syntax_Subst.compress t  in
      uu____2970.FStar_Syntax_Syntax.n  in
    match uu____2969 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2974 -> true
    | uu____2990 -> false
  
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
              let uu____3060 =
                let uu____3062 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3062  in
              if uu____3060
              then f
              else (let uu____3069 = reason1 ()  in label uu____3069 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___396_3090 = g  in
            let uu____3091 =
              let uu____3092 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3092  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3091;
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___396_3090.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___396_3090.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3090.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3090.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3113 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3113
        then c
        else
          (let uu____3118 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3118
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____3160 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3160 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3188 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3188]  in
                       let us =
                         let uu____3210 =
                           let uu____3213 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3213]  in
                         u_res :: uu____3210  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3219 =
                         let uu____3224 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____3225 =
                           let uu____3226 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3235 =
                             let uu____3246 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3255 =
                               let uu____3266 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3266]  in
                             uu____3246 :: uu____3255  in
                           uu____3226 :: uu____3235  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3224 uu____3225
                          in
                       uu____3219 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3308 = destruct_wp_comp c1  in
              match uu____3308 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_wp_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        let bs =
          FStar_All.pipe_right bvs
            (FStar_List.map FStar_Syntax_Syntax.mk_binder)
           in
        FStar_All.pipe_right lc
          (FStar_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
             (fun g  ->
                let uu____3348 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3348
                  (close_guard_implicits env false bs)))
  
let (close_layered_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun tms  ->
        fun lc  ->
          let bs =
            FStar_All.pipe_right bvs
              (FStar_List.map FStar_Syntax_Syntax.mk_binder)
             in
          let substs =
            FStar_List.map2
              (fun bv  -> fun tm  -> FStar_Syntax_Syntax.NT (bv, tm)) bvs tms
             in
          FStar_All.pipe_right lc
            (FStar_TypeChecker_Common.apply_lcomp
               (FStar_Syntax_Subst.subst_comp substs)
               (fun g  ->
                  let uu____3398 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3398
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3411  ->
            match uu___0_3411 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3414 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3439 =
            let uu____3442 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3442 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3439
            (fun c  ->
               (let uu____3466 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3466) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3470 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3470)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3481 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3481 with
                | (head1,uu____3498) ->
                    let uu____3519 =
                      let uu____3520 = FStar_Syntax_Util.un_uinst head1  in
                      uu____3520.FStar_Syntax_Syntax.n  in
                    (match uu____3519 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3525 =
                           let uu____3527 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3527
                            in
                         Prims.op_Negation uu____3525
                     | uu____3528 -> true)))
              &&
              (let uu____3531 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3531)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____3559 =
              let uu____3561 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3561  in
            if uu____3559
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3568 = FStar_Syntax_Util.is_unit t  in
               if uu____3568
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
                    let uu____3577 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3577
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3583 =
                         let uu____3584 =
                           let uu____3589 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3590 =
                             let uu____3591 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3600 =
                               let uu____3611 = FStar_Syntax_Syntax.as_arg v1
                                  in
                               [uu____3611]  in
                             uu____3591 :: uu____3600  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3589
                             uu____3590
                            in
                         uu____3584 FStar_Pervasives_Native.None
                           v1.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3583)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3645 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3645
           then
             let uu____3650 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3652 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3654 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3650 uu____3652 uu____3654
           else ());
          c
  
let (mk_indexed_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Syntax_Syntax.comp_typ ->
                  FStar_Syntax_Syntax.cflag Prims.list ->
                    FStar_Range.range ->
                      (FStar_Syntax_Syntax.comp *
                        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun bind_t  ->
            fun ct1  ->
              fun b  ->
                fun ct2  ->
                  fun flags  ->
                    fun r1  ->
                      (let uu____3727 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3727
                       then
                         let uu____3732 =
                           let uu____3734 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3734  in
                         let uu____3735 =
                           let uu____3737 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3737  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3732 uu____3735
                       else ());
                      (let uu____3742 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "ResolveImplicitsHook")
                          in
                       if uu____3742
                       then
                         let uu____3747 =
                           let uu____3749 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Range.string_of_range uu____3749  in
                         let uu____3750 =
                           FStar_Syntax_Print.tscheme_to_string bind_t  in
                         FStar_Util.print2
                           "///////////////////////////////Bind at %s/////////////////////\nwith bind_t = %s\n"
                           uu____3747 uu____3750
                       else ());
                      (let uu____3755 =
                         let uu____3762 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3763 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3764 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3762, uu____3763, uu____3764)  in
                       match uu____3755 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3772 =
                             let uu____3785 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3786 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3785,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3786)
                              in
                           (match uu____3772 with
                            | (u1,t1,is1) ->
                                let uu____3830 =
                                  let uu____3843 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3844 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3843,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3844)
                                   in
                                (match uu____3830 with
                                 | (u2,t2,is2) ->
                                     let uu____3888 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3888 with
                                      | (uu____3897,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3912 =
                                              let uu____3914 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3914 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3912)
                                             in
                                          let uu____3918 =
                                            let uu____3963 =
                                              let uu____3964 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3964.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3963 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4040 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4040 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4125 =
                                                       let uu____4152 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4152
                                                         (fun uu____4237  ->
                                                            match uu____4237
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4318
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4331
                                                                  =
                                                                  let uu____4338
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4338
                                                                   in
                                                                (l1,
                                                                  uu____4318,
                                                                  uu____4331))
                                                        in
                                                     (match uu____4125 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4498 ->
                                                let uu____4499 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4499 r1
                                             in
                                          (match uu____3918 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4624 =
                                                 let uu____4631 =
                                                   let uu____4632 =
                                                     let uu____4633 =
                                                       let uu____4640 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4640, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4633
                                                      in
                                                   let uu____4651 =
                                                     let uu____4654 =
                                                       let uu____4655 =
                                                         let uu____4662 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4662, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4655
                                                        in
                                                     [uu____4654]  in
                                                   uu____4632 :: uu____4651
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4631
                                                   (fun b1  ->
                                                      let uu____4678 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4680 =
                                                        let uu____4682 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4684 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4686 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4682
                                                          uu____4684
                                                          uu____4686
                                                         in
                                                      let uu____4689 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4678 uu____4680
                                                        uu____4689) r1
                                                  in
                                               (match uu____4624 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    ((let uu____4703 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "ResolveImplicitsHook")
                                                         in
                                                      if uu____4703
                                                      then
                                                        FStar_All.pipe_right
                                                          rest_bs_uvars
                                                          (FStar_List.iter
                                                             (fun t  ->
                                                                let uu____4717
                                                                  =
                                                                  let uu____4718
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    t  in
                                                                  uu____4718.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____4717
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_uvar
                                                                    (u,uu____4722)
                                                                    ->
                                                                    let uu____4739
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    let uu____4741
                                                                    =
                                                                    match 
                                                                    u.FStar_Syntax_Syntax.ctx_uvar_meta
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                                                    a) ->
                                                                    FStar_Syntax_Print.term_to_string
                                                                    a
                                                                    | 
                                                                    uu____4747
                                                                    ->
                                                                    "<no attr>"
                                                                     in
                                                                    FStar_Util.print2
                                                                    "Generated uvar %s with attribute %s\n"
                                                                    uu____4739
                                                                    uu____4741))
                                                      else ());
                                                     (let subst1 =
                                                        FStar_List.map2
                                                          (fun b1  ->
                                                             fun t  ->
                                                               let uu____4778
                                                                 =
                                                                 let uu____4785
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    b1
                                                                    FStar_Pervasives_Native.fst
                                                                    in
                                                                 (uu____4785,
                                                                   t)
                                                                  in
                                                               FStar_Syntax_Syntax.NT
                                                                 uu____4778)
                                                          (a_b :: b_b ::
                                                          rest_bs) (t1 :: t2
                                                          :: rest_bs_uvars)
                                                         in
                                                      let f_guard =
                                                        let f_sort_is =
                                                          let uu____4814 =
                                                            let uu____4817 =
                                                              let uu____4818
                                                                =
                                                                let uu____4819
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    f_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4819.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4818
                                                               in
                                                            let uu____4828 =
                                                              FStar_Syntax_Util.is_layered
                                                                m_ed
                                                               in
                                                            effect_args_from_repr
                                                              uu____4817
                                                              uu____4828 r1
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____4814
                                                            (FStar_List.map
                                                               (FStar_Syntax_Subst.subst
                                                                  subst1))
                                                           in
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun f_i1  ->
                                                                 (let uu____4853
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                  if
                                                                    uu____4853
                                                                  then
                                                                    let uu____4858
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____4860
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    f_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____4858
                                                                    uu____4860
                                                                  else ());
                                                                 (let uu____4865
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env i1
                                                                    f_i1  in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____4865))
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is1 f_sort_is
                                                         in
                                                      let g_guard =
                                                        let x_a =
                                                          match b with
                                                          | FStar_Pervasives_Native.None
                                                               ->
                                                              FStar_Syntax_Syntax.null_binder
                                                                ct1.FStar_Syntax_Syntax.result_typ
                                                          | FStar_Pervasives_Native.Some
                                                              x ->
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                           in
                                                        let g_sort_is =
                                                          let uu____4884 =
                                                            let uu____4885 =
                                                              let uu____4888
                                                                =
                                                                let uu____4889
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    g_b
                                                                    FStar_Pervasives_Native.fst
                                                                   in
                                                                uu____4889.FStar_Syntax_Syntax.sort
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4888
                                                               in
                                                            uu____4885.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4884
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (bs,c) ->
                                                              let uu____4922
                                                                =
                                                                FStar_Syntax_Subst.open_comp
                                                                  bs c
                                                                 in
                                                              (match uu____4922
                                                               with
                                                               | (bs1,c1) ->
                                                                   let bs_subst
                                                                    =
                                                                    let uu____4932
                                                                    =
                                                                    let uu____4939
                                                                    =
                                                                    let uu____4940
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4940
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4961
                                                                    =
                                                                    let uu____4964
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4964
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4939,
                                                                    uu____4961)
                                                                     in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____4932
                                                                     in
                                                                   let c2 =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1  in
                                                                   let uu____4978
                                                                    =
                                                                    let uu____4981
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                    let uu____4982
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                    effect_args_from_repr
                                                                    uu____4981
                                                                    uu____4982
                                                                    r1  in
                                                                   FStar_All.pipe_right
                                                                    uu____4978
                                                                    (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                           in
                                                        let env_g =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env [x_a]
                                                           in
                                                        let uu____5001 =
                                                          FStar_List.fold_left2
                                                            (fun g  ->
                                                               fun i1  ->
                                                                 fun g_i1  ->
                                                                   (let uu____5019
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                    (FStar_Options.Other
                                                                    "ResolveImplicitsHook")
                                                                     in
                                                                    if
                                                                    uu____5019
                                                                    then
                                                                    let uu____5024
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    i1  in
                                                                    let uu____5026
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    g_i1  in
                                                                    FStar_Util.print2
                                                                    "Generating constraint %s = %s\n"
                                                                    uu____5024
                                                                    uu____5026
                                                                    else ());
                                                                   (let uu____5031
                                                                    =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____5031))
                                                            FStar_TypeChecker_Env.trivial_guard
                                                            is2 g_sort_is
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5001
                                                          (FStar_TypeChecker_Env.close_guard
                                                             env [x_a])
                                                         in
                                                      let bind_ct =
                                                        let uu____5045 =
                                                          FStar_All.pipe_right
                                                            bind_c
                                                            (FStar_Syntax_Subst.subst_comp
                                                               subst1)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5045
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                         in
                                                      let fml =
                                                        let uu____5047 =
                                                          let uu____5052 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____5053 =
                                                            let uu____5054 =
                                                              FStar_List.hd
                                                                bind_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5054
                                                             in
                                                          (uu____5052,
                                                            uu____5053)
                                                           in
                                                        match uu____5047 with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              bind_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let is =
                                                        let uu____5080 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____5081 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____5080
                                                          uu____5081 r1
                                                         in
                                                      let c =
                                                        let uu____5084 =
                                                          let uu____5085 =
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              is
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              =
                                                              (ct2.FStar_Syntax_Syntax.comp_univs);
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              (p_ed.FStar_Syntax_Syntax.mname);
                                                            FStar_Syntax_Syntax.result_typ
                                                              = t2;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____5085;
                                                            FStar_Syntax_Syntax.flags
                                                              = flags
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____5084
                                                         in
                                                      (let uu____5105 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "LayeredEffects")
                                                          in
                                                       if uu____5105
                                                       then
                                                         let uu____5110 =
                                                           FStar_Syntax_Print.comp_to_string
                                                             c
                                                            in
                                                         FStar_Util.print1
                                                           "} c after bind: %s\n"
                                                           uu____5110
                                                       else ());
                                                      (let guard =
                                                         let uu____5116 =
                                                           let uu____5119 =
                                                             let uu____5122 =
                                                               let uu____5125
                                                                 =
                                                                 let uu____5128
                                                                   =
                                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                    in
                                                                 [uu____5128]
                                                                  in
                                                               g_guard ::
                                                                 uu____5125
                                                                in
                                                             f_guard ::
                                                               uu____5122
                                                              in
                                                           g_uvars ::
                                                             uu____5119
                                                            in
                                                         FStar_TypeChecker_Env.conj_guards
                                                           uu____5116
                                                          in
                                                       (let uu____5130 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "ResolveImplicitsHook")
                                                           in
                                                        if uu____5130
                                                        then
                                                          let uu____5135 =
                                                            let uu____5137 =
                                                              FStar_TypeChecker_Env.get_range
                                                                env
                                                               in
                                                            FStar_Range.string_of_range
                                                              uu____5137
                                                             in
                                                          let uu____5138 =
                                                            FStar_TypeChecker_Rel.guard_to_string
                                                              env guard
                                                             in
                                                          FStar_Util.print2
                                                            "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                            uu____5135
                                                            uu____5138
                                                        else ());
                                                       (c, guard))))))))))
  
let (mk_wp_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.comp_typ ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.comp_typ ->
            FStar_Syntax_Syntax.cflag Prims.list ->
              FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun m  ->
      fun ct1  ->
        fun b  ->
          fun ct2  ->
            fun flags  ->
              fun r1  ->
                let uu____5187 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5213 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5213 with
                  | (a,kwp) ->
                      let uu____5244 = destruct_wp_comp ct1  in
                      let uu____5251 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5244, uu____5251)
                   in
                match uu____5187 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5304 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5304]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5324 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5324]
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
                      let uu____5371 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5380 =
                        let uu____5391 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5400 =
                          let uu____5411 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5420 =
                            let uu____5431 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5440 =
                              let uu____5451 =
                                let uu____5460 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5460  in
                              [uu____5451]  in
                            uu____5431 :: uu____5440  in
                          uu____5411 :: uu____5420  in
                        uu____5391 :: uu____5400  in
                      uu____5371 :: uu____5380  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5513 =
                        let uu____5518 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5518 wp_args  in
                      uu____5513 FStar_Pervasives_Native.None
                        t2.FStar_Syntax_Syntax.pos
                       in
                    mk_comp md u_t2 t2 wp flags
  
let (mk_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.comp ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            FStar_Range.range ->
              (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun b  ->
        fun c2  ->
          fun flags  ->
            fun r1  ->
              let uu____5566 =
                let uu____5571 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5572 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5571, uu____5572)  in
              match uu____5566 with
              | (ct1,ct2) ->
                  let uu____5579 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5579 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5630 = lift_comps env c1 c2 b true  in
                       (match uu____5630 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5648 =
                              let uu____5653 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5654 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5653, uu____5654)  in
                            (match uu____5648 with
                             | (ct11,ct21) ->
                                 let uu____5661 =
                                   let uu____5666 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5666
                                   then
                                     let bind_t =
                                       let uu____5674 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5674
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5677 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5677,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5661 with
                                  | (c,g_bind) ->
                                      let uu____5684 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5684)))))
  
let (bind_pure_wp_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.cflag Prims.list ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun wp1  ->
      fun c  ->
        fun flags  ->
          let r = FStar_TypeChecker_Env.get_range env  in
          let pure_c =
            let uu____5720 =
              let uu____5721 =
                let uu____5732 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5732]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5721;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5720  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5777 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5783  ->
              match uu___1_5783 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5786 -> false))
       in
    if uu____5777
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5798  ->
              match uu___2_5798 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____5826 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5826
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5837 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5837  in
           let pure_assume_wp1 =
             let uu____5842 = FStar_TypeChecker_Env.get_range env  in
             let uu____5843 =
               let uu____5848 =
                 let uu____5849 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5849]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5848  in
             uu____5843 FStar_Pervasives_Native.None uu____5842  in
           let uu____5882 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5882)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5910 =
          let uu____5911 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5911 with
          | (c,g_c) ->
              let uu____5922 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5922
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5936 = weaken_comp env c f1  in
                     (match uu____5936 with
                      | (c1,g_w) ->
                          let uu____5947 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5947)))
           in
        let uu____5948 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5948 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflag Prims.list ->
            (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags  ->
            if env.FStar_TypeChecker_Env.lax
            then (c, FStar_TypeChecker_Env.trivial_guard)
            else
              (let r = FStar_TypeChecker_Env.get_range env  in
               let pure_assert_wp =
                 let uu____6005 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____6005  in
               let pure_assert_wp1 =
                 let uu____6010 =
                   let uu____6015 =
                     let uu____6016 =
                       let uu____6025 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____6025
                        in
                     [uu____6016]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____6015
                    in
                 uu____6010 FStar_Pervasives_Native.None r  in
               bind_pure_wp_with env pure_assert_wp1 c flags)
  
let (record_simplify :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  let x = FStar_Util.mk_ref Prims.int_zero  in
  fun env  ->
    fun guard  ->
      let n1 = FStar_ST.op_Bang x  in
      FStar_ST.op_Colon_Equals x (n1 + Prims.int_one);
      (let start = FStar_Util.now ()  in
       let g = FStar_TypeChecker_Rel.simplify_guard env guard  in
       let fin = FStar_Util.now ()  in
       (let uu____6117 = FStar_Options.debug_any ()  in
        if uu____6117
        then
          let uu____6120 = FStar_Util.string_of_int n1  in
          let uu____6122 =
            let uu____6124 =
              let uu____6126 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____6126  in
            FStar_Util.string_of_int uu____6124  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____6120
            uu____6122
        else ());
       g)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_TypeChecker_Common.guard_t ->
            (FStar_TypeChecker_Common.lcomp *
              FStar_TypeChecker_Common.guard_t))
  =
  fun reason  ->
    fun env  ->
      fun e_for_debugging_only  ->
        fun lc  ->
          fun g0  ->
            let uu____6181 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6181
            then (lc, g0)
            else
              (let flags =
                 let uu____6193 =
                   let uu____6201 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6201
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6193 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6231 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6239  ->
                               match uu___3_6239 with
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
                               | uu____6242 -> []))
                        in
                     FStar_List.append flags uu____6231
                  in
               let strengthen uu____6252 =
                 let uu____6253 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6253 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6272 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6272 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6279 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6279
                              then
                                let uu____6283 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6285 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6283 uu____6285
                              else ());
                             (let uu____6290 =
                                strengthen_comp env reason c f flags  in
                              match uu____6290 with
                              | (c1,g_s) ->
                                  let uu____6301 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6301))))
                  in
               let uu____6302 =
                 let uu____6303 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6303
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6302,
                 (let uu___736_6305 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred_to_tac =
                      (uu___736_6305.FStar_TypeChecker_Common.deferred_to_tac);
                    FStar_TypeChecker_Common.deferred =
                      (uu___736_6305.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___736_6305.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___736_6305.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6314  ->
            match uu___4_6314 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6318 -> false) lc.FStar_TypeChecker_Common.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____6347 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6347
          then e
          else
            (let uu____6354 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6357 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6357)
                in
             if uu____6354
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_TypeChecker_Common.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_TypeChecker_Common.res_typ e
             else e)
  
let (maybe_capture_unit_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun x  ->
        fun c  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize_refinement
              FStar_TypeChecker_Normalize.whnf_steps env t
             in
          match t1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (b,phi) ->
              let is_unit1 =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____6427 -> false  in
              if is_unit1
              then
                let uu____6434 =
                  let uu____6436 =
                    let uu____6437 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6437
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6436
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6434
                 then
                   let uu____6446 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6446 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6490 =
                           let uu____6493 =
                             let uu____6494 =
                               let uu____6501 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6501, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6494  in
                           [uu____6493]  in
                         FStar_Syntax_Subst.subst uu____6490 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6514 = close_wp_comp env [x] c  in
                    (uu____6514, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6517 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____6545  ->
            match uu____6545 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6565 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6565 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6578 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6578
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6588 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6588
                       then
                         let uu____6593 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6593
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6600 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6600
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6609 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6609
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6616 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6616
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6632 =
                  let uu____6633 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6633
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6641 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6641, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6644 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6644 with
                     | (c1,g_c1) ->
                         let uu____6655 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6655 with
                          | (c2,g_c2) ->
                              let trivial_guard1 =
                                let uu____6667 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6670 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6670
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6667
                                 in
                              (debug1
                                 (fun uu____6696  ->
                                    let uu____6697 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6699 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6704 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6697 uu____6699 uu____6704);
                               (let aux uu____6722 =
                                  let uu____6723 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6723
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6754
                                        ->
                                        let uu____6755 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6755
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6787 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6787
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6834 =
                                  let aux_with_trivial_guard uu____6864 =
                                    let uu____6865 = aux ()  in
                                    match uu____6865 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard1, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6923 =
                                    let uu____6925 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6925  in
                                  if uu____6923
                                  then
                                    let uu____6941 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6941
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard1,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6968 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6968))
                                  else
                                    (let uu____6985 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6985
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___840_7016 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___840_7016.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___840_7016.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         maybe_capture_unit_refinement env
                                           x1.FStar_Syntax_Syntax.sort x1 c
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____7047 =
                                             let uu____7052 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____7052
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____7047 with
                                            | (c21,g_close) ->
                                                let uu____7073 =
                                                  let uu____7081 =
                                                    let uu____7082 =
                                                      let uu____7085 =
                                                        let uu____7088 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____7088; g_close]
                                                         in
                                                      g_c1 :: uu____7085  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7082
                                                     in
                                                  (c21, uu____7081, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____7073)
                                       | (uu____7101,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____7113 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____7113 with
                                            | (c21,g_close) ->
                                                let uu____7136 =
                                                  let uu____7144 =
                                                    let uu____7145 =
                                                      let uu____7148 =
                                                        let uu____7151 =
                                                          let uu____7152 =
                                                            let uu____7153 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____7153]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____7152
                                                            g_c2
                                                           in
                                                        [uu____7151; g_close]
                                                         in
                                                      g_c1 :: uu____7148  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7145
                                                     in
                                                  (c21, uu____7144,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____7136)
                                       | (uu____7182,uu____7183) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7198 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7198
                                        then
                                          let uu____7213 =
                                            let uu____7221 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7221, trivial_guard1,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7213
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7234 = try_simplify ()  in
                                match uu____7234 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug1
                                       (fun uu____7269  ->
                                          let uu____7270 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7270);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7286  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7317 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7317 with
                                        | (c,g_bind) ->
                                            let uu____7328 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7328)
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
                                        let uu____7355 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7355 with
                                        | (m,uu____7367,lift2) ->
                                            let uu____7369 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7369 with
                                             | (c23,g2) ->
                                                 let uu____7380 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7380 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7396 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7396
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7406 =
                                                          let uu____7411 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7412 =
                                                            let uu____7413 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7422 =
                                                              let uu____7433
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7433]
                                                               in
                                                            uu____7413 ::
                                                              uu____7422
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7411
                                                            uu____7412
                                                           in
                                                        uu____7406
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7466 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7466 with
                                                       | (c,g_s) ->
                                                           let uu____7481 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7481))))
                                         in
                                      let uu____7482 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7498 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7498, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7482 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7514 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7514
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7523 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7523
                                             then
                                               (debug1
                                                  (fun uu____7537  ->
                                                     let uu____7538 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7540 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7538 uu____7540);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7547 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7547
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7552 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7555 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7555)
                                                   in
                                                if uu____7552
                                                then
                                                  let e1' =
                                                    let uu____7580 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7580
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7592  ->
                                                        let uu____7593 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7595 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7593
                                                          uu____7595);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7610  ->
                                                        let uu____7611 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7613 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7611
                                                          uu____7613);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7620 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7620
                                                       in
                                                    let uu____7621 =
                                                      let uu____7626 =
                                                        let uu____7627 =
                                                          let uu____7628 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7628]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7627
                                                         in
                                                      weaken_comp uu____7626
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7621 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7654 =
                                                            let uu____7655 =
                                                              let uu____7656
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7656]
                                                               in
                                                            let uu____7675 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7655
                                                              uu____7675
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7654
                                                           in
                                                        let uu____7676 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7676
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7687 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7687))))))
                                          else
                                            mk_bind1 c1 b c2 trivial_guard1))))))
                   in
                FStar_TypeChecker_Common.mk_lcomp joined_eff
                  lc21.FStar_TypeChecker_Common.res_typ bind_flags bind_it
  
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
      | uu____7704 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
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
            (let uu____7728 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7728)
           in
        let flags =
          if should_return1
          then
            let uu____7736 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7736
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7754 =
          let uu____7755 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7755 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7768 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7768
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7776 =
                  let uu____7778 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7778  in
                (if uu____7776
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___965_7787 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___965_7787.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___965_7787.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___965_7787.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7788 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7788, g_c)
                 else
                   (let uu____7791 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7791, g_c)))
              else
                (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                    in
                 let t = c1.FStar_Syntax_Syntax.result_typ  in
                 let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (t.FStar_Syntax_Syntax.pos)) t
                    in
                 let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                 let ret1 =
                   let uu____7802 =
                     let uu____7803 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7803
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7802
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7806 =
                   let uu____7811 =
                     let uu____7812 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7812
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7811  in
                 match uu____7806 with
                 | (bind_c,g_bind) ->
                     let uu____7821 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7822 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7821, uu____7822))
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_TypeChecker_Common.mk_lcomp
            lc.FStar_TypeChecker_Common.eff_name
            lc.FStar_TypeChecker_Common.res_typ flags refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_TypeChecker_Common.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____7858  ->
              match uu____7858 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_TypeChecker_Common.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_TypeChecker_Common.eff_name
                       in
                    let uu____7870 =
                      ((let uu____7874 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7874) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7870
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7892 =
        let uu____7893 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7893  in
      FStar_Syntax_Syntax.fvar uu____7892 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (mk_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun r  ->
                  let uu____7943 =
                    let uu____7948 =
                      let uu____7949 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7949 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7948 [u_a]
                     in
                  match uu____7943 with
                  | (uu____7960,conjunction) ->
                      let uu____7962 =
                        let uu____7971 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7986 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7971, uu____7986)  in
                      (match uu____7962 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____8032 =
                               let uu____8034 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____8034 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____8032)
                              in
                           let uu____8038 =
                             let uu____8083 =
                               let uu____8084 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____8084.FStar_Syntax_Syntax.n  in
                             match uu____8083 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____8133) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____8165 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____8165 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8237 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8237 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8385 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8385)))
                             | uu____8418 ->
                                 let uu____8419 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8419 r
                              in
                           (match uu____8038 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8544 =
                                  let uu____8551 =
                                    let uu____8552 =
                                      let uu____8553 =
                                        let uu____8560 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8560, a)  in
                                      FStar_Syntax_Syntax.NT uu____8553  in
                                    [uu____8552]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8551
                                    (fun b  ->
                                       let uu____8576 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8578 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8580 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8576 uu____8578 uu____8580) r
                                   in
                                (match uu____8544 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8618 =
                                                let uu____8625 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8625, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8618) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8664 =
                                           let uu____8665 =
                                             let uu____8668 =
                                               let uu____8669 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8669.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8668
                                              in
                                           uu____8665.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8664 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8680,uu____8681::is) ->
                                             let uu____8723 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8723
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8756 ->
                                             let uu____8757 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8757 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8773 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8773)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8778 =
                                           let uu____8779 =
                                             let uu____8782 =
                                               let uu____8783 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8783.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8782
                                              in
                                           uu____8779.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8778 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8794,uu____8795::is) ->
                                             let uu____8837 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8837
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8870 ->
                                             let uu____8871 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8871 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8887 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8887)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8892 =
                                         let uu____8893 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8893.FStar_Syntax_Syntax.n  in
                                       match uu____8892 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8898,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8953 ->
                                           let uu____8954 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8954 r
                                        in
                                     let uu____8963 =
                                       let uu____8964 =
                                         let uu____8965 =
                                           FStar_All.pipe_right is
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.as_arg)
                                            in
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_a];
                                           FStar_Syntax_Syntax.effect_name =
                                             (ed.FStar_Syntax_Syntax.mname);
                                           FStar_Syntax_Syntax.result_typ = a;
                                           FStar_Syntax_Syntax.effect_args =
                                             uu____8965;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8964
                                        in
                                     let uu____8988 =
                                       let uu____8989 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8989 g_guard
                                        in
                                     (uu____8963, uu____8988))))
  
let (mk_non_layered_conjunction :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.comp_typ ->
              FStar_Syntax_Syntax.comp_typ ->
                FStar_Range.range ->
                  (FStar_Syntax_Syntax.comp *
                    FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun ed  ->
      fun u_a  ->
        fun a  ->
          fun p  ->
            fun ct1  ->
              fun ct2  ->
                fun uu____9034  ->
                  let if_then_else1 =
                    let uu____9040 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____9040 FStar_Util.must  in
                  let uu____9047 = destruct_wp_comp ct1  in
                  match uu____9047 with
                  | (uu____9058,uu____9059,wp_t) ->
                      let uu____9061 = destruct_wp_comp ct2  in
                      (match uu____9061 with
                       | (uu____9072,uu____9073,wp_e) ->
                           let wp =
                             let uu____9078 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____9079 =
                               let uu____9084 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____9085 =
                                 let uu____9086 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____9095 =
                                   let uu____9106 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____9115 =
                                     let uu____9126 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____9135 =
                                       let uu____9146 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____9146]  in
                                     uu____9126 :: uu____9135  in
                                   uu____9106 :: uu____9115  in
                                 uu____9086 :: uu____9095  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____9084
                                 uu____9085
                                in
                             uu____9079 FStar_Pervasives_Native.None
                               uu____9078
                              in
                           let uu____9195 = mk_comp ed u_a a wp []  in
                           (uu____9195, FStar_TypeChecker_Env.trivial_guard))
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_Syntax_Syntax.bv -> FStar_TypeChecker_Common.lcomp)
  =
  fun env0  ->
    fun res_t  ->
      fun lcases  ->
        fun scrutinee  ->
          let env =
            let uu____9249 =
              let uu____9250 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9250]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9249  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9297  ->
                   match uu____9297 with
                   | (uu____9311,eff_label,uu____9313,uu____9314) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9327 =
            let uu____9335 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9373  ->
                      match uu____9373 with
                      | (uu____9388,uu____9389,flags,uu____9391) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9408  ->
                                  match uu___5_9408 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9411 -> false))))
               in
            if uu____9335
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9327 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9448 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9450 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9450
                then
                  let uu____9457 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9457, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9464 =
                         let uu____9473 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9473]  in
                       let uu____9492 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9464 uu____9492  in
                     let kwp =
                       let uu____9498 =
                         let uu____9507 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9507]  in
                       let uu____9526 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9498 uu____9526  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9533 =
                         let uu____9534 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9534]  in
                       let uu____9553 =
                         let uu____9556 =
                           let uu____9563 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9563
                            in
                         let uu____9564 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9556 uu____9564  in
                       FStar_Syntax_Util.abs uu____9533 uu____9553
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
                     let uu____9588 =
                       should_not_inline_whole_match ||
                         (let uu____9591 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9591)
                        in
                     if uu____9588 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9603 =
                       let uu____9616 =
                         let uu____9621 =
                           let uu____9632 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9676  ->
                                     match uu____9676 with
                                     | (g,uu____9691,uu____9692,uu____9693)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9632
                             (FStar_List.fold_left
                                (fun uu____9737  ->
                                   fun g  ->
                                     match uu____9737 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9778 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9778
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9621
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9616
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9603
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9879 =
                     FStar_List.fold_right2
                       (fun uu____9942  ->
                          fun bcond  ->
                            fun uu____9944  ->
                              match (uu____9942, uu____9944) with
                              | ((g,eff_label,uu____10004,cthen),(uu____10006,celse,g_comp))
                                  ->
                                  let uu____10053 =
                                    let uu____10058 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____10058
                                     in
                                  (match uu____10053 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____10070 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____10070
                                          in
                                       let uu____10071 =
                                         let uu____10082 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             false
                                            in
                                         match uu____10082 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____10110 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____10111 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____10110, uu____10111,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____10071 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____10162 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____10162
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____10197 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____10197
                                               in
                                            let g_lift_else1 =
                                              let uu____10199 =
                                                let uu____10200 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____10200
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____10199
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____10204 =
                                              let uu____10209 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____10209
                                               in
                                            (match uu____10204 with
                                             | (c,g_conjunction) ->
                                                 let uu____10220 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____10220)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9879 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____10237 =
                           let uu____10238 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____10238]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____10237
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____10281::[] -> (comp, g_comp1)
                        | uu____10324 ->
                            let uu____10341 =
                              let uu____10343 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10343
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10341
                            then (comp, g_comp1)
                            else
                              (let comp1 =
                                 FStar_TypeChecker_Env.comp_to_comp_typ env
                                   comp
                                  in
                               let md1 =
                                 FStar_TypeChecker_Env.get_effect_decl env
                                   comp1.FStar_Syntax_Syntax.effect_name
                                  in
                               let uu____10356 = destruct_wp_comp comp1  in
                               match uu____10356 with
                               | (uu____10367,uu____10368,wp) ->
                                   let ite_wp =
                                     let uu____10371 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10371
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10381 =
                                       let uu____10386 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10387 =
                                         let uu____10388 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10397 =
                                           let uu____10408 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10408]  in
                                         uu____10388 :: uu____10397  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10386 uu____10387
                                        in
                                     uu____10381 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10441 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10441, g_comp1))))
                 in
              FStar_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags
                bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____10476 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10476 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10492 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10498 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10492 uu____10498
              else
                (let uu____10507 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10513 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10507 uu____10513)
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (universe_of_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u_res  ->
      fun c  ->
        let c_lid =
          let uu____10538 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10538
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10541 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10541
        then u_res
        else
          (let is_total =
             let uu____10548 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10548
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10559 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10559 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10562 =
                    let uu____10568 =
                      let uu____10570 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10570
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10568)
                     in
                  FStar_Errors.raise_error uu____10562
                    c.FStar_Syntax_Syntax.pos
              | FStar_Pervasives_Native.Some tm ->
                  env.FStar_TypeChecker_Env.universe_of env tm))
  
let (check_trivial_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp_typ * FStar_Syntax_Syntax.formula *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let ct =
        FStar_All.pipe_right c
          (FStar_TypeChecker_Env.unfold_effect_abbrev env)
         in
      let md =
        FStar_TypeChecker_Env.get_effect_decl env
          ct.FStar_Syntax_Syntax.effect_name
         in
      let uu____10594 = destruct_wp_comp ct  in
      match uu____10594 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10613 = FStar_TypeChecker_Env.get_range env  in
            let uu____10614 =
              let uu____10619 =
                let uu____10620 =
                  let uu____10621 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10621 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10620
                 in
              let uu____10628 =
                let uu____10629 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10638 =
                  let uu____10649 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10649]  in
                uu____10629 :: uu____10638  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10619 uu____10628  in
            uu____10614 FStar_Pervasives_Native.None uu____10613  in
          let uu____10682 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10682)
  
let (coerce_with :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp) ->
                  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun ty  ->
          fun f  ->
            fun us  ->
              fun eargs  ->
                fun mkcomp  ->
                  let uu____10737 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10737 with
                  | FStar_Pervasives_Native.Some uu____10752 ->
                      ((let uu____10770 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10770
                        then
                          let uu____10774 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10774
                        else ());
                       (let coercion =
                          let uu____10780 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10780
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10787 =
                            let uu____10788 =
                              let uu____10789 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10789
                               in
                            (FStar_Pervasives_Native.None, uu____10788)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10787
                           in
                        let e1 =
                          let uu____10795 =
                            let uu____10800 =
                              let uu____10801 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10801]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10800
                             in
                          uu____10795 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10835 =
                          let uu____10841 =
                            let uu____10843 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10843
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10841)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10835);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10862 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10880 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10891 -> false 
let rec (check_erased :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> isErased) =
  fun env  ->
    fun t  ->
      let norm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
          FStar_TypeChecker_Env.Primops;
          FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.Iota]
         in
      let t1 = norm' env t  in
      let t2 = FStar_Syntax_Util.unrefine t1  in
      let uu____10915 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10915 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10960 =
              let uu____10975 =
                let uu____10976 = FStar_Syntax_Subst.compress h1  in
                uu____10976.FStar_Syntax_Syntax.n  in
              (uu____10975, args)  in
            match uu____10960 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11023,uu____11024) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11057) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11078,branches),uu____11080) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11144 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11145 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11145 with
                               | (uu____11146,uu____11147,br_body) ->
                                   let uu____11165 =
                                     let uu____11166 =
                                       let uu____11171 =
                                         let uu____11172 =
                                           let uu____11175 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11175
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11172
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11171  in
                                     FStar_All.pipe_right br_body uu____11166
                                      in
                                   (match uu____11165 with
                                    | No  -> No
                                    | uu____11186 -> Maybe))) No)
            | uu____11187 -> No  in
          r
  
let (maybe_coerce_lc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun exp_t  ->
          let should_coerce =
            (((let uu____11239 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11239) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11258 =
                 let uu____11259 = FStar_Syntax_Subst.compress t1  in
                 uu____11259.FStar_Syntax_Syntax.n  in
               match uu____11258 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11264 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11274 =
                 let uu____11275 = FStar_Syntax_Subst.compress t1  in
                 uu____11275.FStar_Syntax_Syntax.n  in
               match uu____11274 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11280 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11291 =
                 let uu____11292 = FStar_Syntax_Subst.compress t2  in
                 uu____11292.FStar_Syntax_Syntax.n  in
               match uu____11291 with
               | FStar_Syntax_Syntax.Tm_type uu____11296 -> true
               | uu____11298 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11301 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11301 with
             | (head1,args) ->
                 ((let uu____11351 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11351
                   then
                     let uu____11355 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11357 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11359 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11361 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11355 uu____11357 uu____11359 uu____11361
                   else ());
                  (let mk_erased u t =
                     let uu____11379 =
                       let uu____11382 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11382 [u]  in
                     let uu____11383 =
                       let uu____11394 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11394]  in
                     FStar_Syntax_Util.mk_app uu____11379 uu____11383  in
                   let uu____11419 =
                     let uu____11434 =
                       let uu____11435 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11435.FStar_Syntax_Syntax.n  in
                     (uu____11434, args)  in
                   match uu____11419 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11473 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11473 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11513 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11513 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11553 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11553 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11593 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11593 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11614 ->
                       let uu____11629 =
                         let uu____11634 = check_erased env res_typ  in
                         let uu____11635 = check_erased env exp_t  in
                         (uu____11634, uu____11635)  in
                       (match uu____11629 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11644 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11644 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11655 =
                                   let uu____11660 =
                                     let uu____11661 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11661]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11660
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11655 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11696 =
                              let uu____11701 =
                                let uu____11702 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11702]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11701
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11696 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11735 ->
                            (e, lc, FStar_TypeChecker_Env.trivial_guard)))))
  
let (coerce_views :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let rt = lc.FStar_TypeChecker_Common.res_typ  in
        let rt1 = FStar_Syntax_Util.unrefine rt  in
        let uu____11770 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11770 with
        | (hd1,args) ->
            let uu____11819 =
              let uu____11834 =
                let uu____11835 = FStar_Syntax_Subst.compress hd1  in
                uu____11835.FStar_Syntax_Syntax.n  in
              (uu____11834, args)  in
            (match uu____11819 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11873 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11900  -> FStar_Pervasives_Native.Some _11900)
                   uu____11873
             | uu____11901 -> FStar_Pervasives_Native.None)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          (let uu____11954 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11954
           then
             let uu____11957 = FStar_Syntax_Print.term_to_string e  in
             let uu____11959 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11961 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11957 uu____11959 uu____11961
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11971 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11971 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11996 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12022 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12022, false)
             else
               (let uu____12032 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12032, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12045) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12057 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12057
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1407_12073 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1407_12073.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1407_12073.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1407_12073.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____12080 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12080 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12096 =
                      let uu____12097 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12097 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____12117 =
                            let uu____12119 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____12119 = FStar_Syntax_Util.Equal  in
                          if uu____12117
                          then
                            ((let uu____12126 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12126
                              then
                                let uu____12130 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12132 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12130 uu____12132
                              else ());
                             (let uu____12137 = set_result_typ1 c  in
                              (uu____12137, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12144 ->
                                   true
                               | uu____12152 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12161 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12161
                                  in
                               let lc1 =
                                 let uu____12163 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12164 =
                                   let uu____12165 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12165)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12163 uu____12164
                                  in
                               ((let uu____12169 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12169
                                 then
                                   let uu____12173 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12175 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12177 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12179 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12173 uu____12175 uu____12177
                                     uu____12179
                                 else ());
                                (let uu____12184 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12184 with
                                 | (c1,g_lc) ->
                                     let uu____12195 = set_result_typ1 c1  in
                                     let uu____12196 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12195, uu____12196)))
                             else
                               ((let uu____12200 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12200
                                 then
                                   let uu____12204 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12206 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12204 uu____12206
                                 else ());
                                (let uu____12211 = set_result_typ1 c  in
                                 (uu____12211, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1444_12215 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1444_12215.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1444_12215.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1444_12215.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1444_12215.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12225 =
                      let uu____12226 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12226
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12236 =
                           let uu____12237 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12237.FStar_Syntax_Syntax.n  in
                         match uu____12236 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12244,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12246;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12247;_},uu____12248)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1460_12274 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1460_12274.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1460_12274.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1460_12274.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12275 ->
                             let uu____12276 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12276 with
                              | (c,g_c) ->
                                  ((let uu____12288 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12288
                                    then
                                      let uu____12292 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12294 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12296 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12298 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12292 uu____12294 uu____12296
                                        uu____12298
                                    else ());
                                   (let u_t_opt = comp_univ_opt c  in
                                    let x =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (t.FStar_Syntax_Syntax.pos)) t
                                       in
                                    let xexp =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let cret =
                                      return_value env u_t_opt t xexp  in
                                    let guard =
                                      if apply_guard1
                                      then
                                        let uu____12311 =
                                          let uu____12316 =
                                            let uu____12317 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12317]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12316
                                           in
                                        uu____12311
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12344 =
                                      let uu____12349 =
                                        FStar_All.pipe_left
                                          (fun _12370  ->
                                             FStar_Pervasives_Native.Some
                                               _12370)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12371 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12372 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12373 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12349
                                        uu____12371 e uu____12372 uu____12373
                                       in
                                    match uu____12344 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1478_12381 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1478_12381.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1478_12381.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12383 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12383
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12386 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12386 with
                                         | (c2,g_lc) ->
                                             ((let uu____12398 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12398
                                               then
                                                 let uu____12402 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12402
                                               else ());
                                              (let uu____12407 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12407))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12416  ->
                              match uu___6_12416 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12419 -> []))
                       in
                    let lc1 =
                      let uu____12421 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12421 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1494_12423 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred_to_tac =
                          (uu___1494_12423.FStar_TypeChecker_Common.deferred_to_tac);
                        FStar_TypeChecker_Common.deferred =
                          (uu___1494_12423.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1494_12423.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1494_12423.FStar_TypeChecker_Common.implicits)
                      }  in
                    (e, lc1, g2)))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____12459 =
          let uu____12462 =
            let uu____12467 =
              let uu____12468 =
                let uu____12477 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12477  in
              [uu____12468]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12467  in
          uu____12462 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12459  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12500 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12500
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12519 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12535 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12552 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12552
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12568)::(ens,uu____12570)::uu____12571 ->
                    let uu____12614 =
                      let uu____12617 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12617  in
                    let uu____12618 =
                      let uu____12619 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12619  in
                    (uu____12614, uu____12618)
                | uu____12622 ->
                    let uu____12633 =
                      let uu____12639 =
                        let uu____12641 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12641
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12639)
                       in
                    FStar_Errors.raise_error uu____12633
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12661)::uu____12662 ->
                    let uu____12689 =
                      let uu____12694 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12694
                       in
                    (match uu____12689 with
                     | (us_r,uu____12726) ->
                         let uu____12727 =
                           let uu____12732 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12732
                            in
                         (match uu____12727 with
                          | (us_e,uu____12764) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12767 =
                                  let uu____12768 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12768
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12767
                                  us_r
                                 in
                              let as_ens =
                                let uu____12770 =
                                  let uu____12771 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12771
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12770
                                  us_e
                                 in
                              let req =
                                let uu____12775 =
                                  let uu____12780 =
                                    let uu____12781 =
                                      let uu____12792 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12792]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12781
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12780
                                   in
                                uu____12775 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12832 =
                                  let uu____12837 =
                                    let uu____12838 =
                                      let uu____12849 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12849]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12838
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12837
                                   in
                                uu____12832 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12886 =
                                let uu____12889 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12889  in
                              let uu____12890 =
                                let uu____12891 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12891  in
                              (uu____12886, uu____12890)))
                | uu____12894 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun t  ->
        let tm = FStar_Syntax_Util.mk_reify t  in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            (FStar_List.append
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.Eager_unfolding;
               FStar_TypeChecker_Env.EraseUniverses;
               FStar_TypeChecker_Env.AllowUnboundUniverses;
               FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
               steps) env tm
           in
        (let uu____12933 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12933
         then
           let uu____12938 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12940 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12938
             uu____12940
         else ());
        tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun steps  ->
      fun head1  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
              FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
             in
          let tm' =
            FStar_TypeChecker_Normalize.normalize
              (FStar_List.append
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Reify;
                 FStar_TypeChecker_Env.Eager_unfolding;
                 FStar_TypeChecker_Env.EraseUniverses;
                 FStar_TypeChecker_Env.AllowUnboundUniverses;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta]
                 steps) env tm
             in
          (let uu____12999 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12999
           then
             let uu____13004 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13006 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13004
               uu____13006
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13017 =
      let uu____13019 =
        let uu____13020 = FStar_Syntax_Subst.compress t  in
        uu____13020.FStar_Syntax_Syntax.n  in
      match uu____13019 with
      | FStar_Syntax_Syntax.Tm_app uu____13024 -> false
      | uu____13042 -> true  in
    if uu____13017
    then t
    else
      (let uu____13047 = FStar_Syntax_Util.head_and_args t  in
       match uu____13047 with
       | (head1,args) ->
           let uu____13090 =
             let uu____13092 =
               let uu____13093 = FStar_Syntax_Subst.compress head1  in
               uu____13093.FStar_Syntax_Syntax.n  in
             match uu____13092 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13098 -> false  in
           if uu____13090
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13130 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Env.trivial_guard)
        else
          ((let uu____13177 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13177
            then
              let uu____13180 = FStar_Syntax_Print.term_to_string e  in
              let uu____13182 = FStar_Syntax_Print.term_to_string t  in
              let uu____13184 =
                let uu____13186 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13186
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13180 uu____13182 uu____13184
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13222 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13222 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13256 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13334  ->
                          match uu____13334 with
                          | (uu____13342,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13349 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13349 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13256 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13468 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13468 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13482 =
                      let uu____13488 =
                        let uu____13490 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13492 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13494 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13490 uu____13492 uu____13494
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13488)
                       in
                    let uu____13498 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13482 uu____13498
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13516 =
              match uu___7_13516 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13559 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13559 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13690,uu____13677)
                           when _13690 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13723,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13725))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13759 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13759 with
                            | (v1,uu____13800,g) ->
                                ((let uu____13815 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13815
                                  then
                                    let uu____13818 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13818
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13828 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13828 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13921 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13921))))
                       | (uu____13948,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta
                                       tac_or_attr))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let meta_t =
                             match tac_or_attr with
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_tac tau
                                 ->
                                 let uu____13987 =
                                   let uu____13994 = FStar_Dyn.mkdyn env  in
                                   (uu____13994, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____13987
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____14000 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____14000 with
                            | (v1,uu____14041,g) ->
                                ((let uu____14056 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14056
                                  then
                                    let uu____14059 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14059
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____14069 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____14069 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____14162 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____14162))))
                       | (uu____14189,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14237 =
                       let uu____14264 = inst_n_binders t1  in
                       aux [] uu____14264 bs1  in
                     (match uu____14237 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14336) -> (e, torig, guard)
                           | (uu____14367,[]) when
                               let uu____14398 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14398 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14400 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14428 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst1 t2
                                  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14441 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14453 =
      let uu____14457 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14457
        (FStar_List.map
           (fun u  ->
              let uu____14469 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14469 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14453 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14497 = FStar_Util.set_is_empty x  in
      if uu____14497
      then []
      else
        (let s =
           let uu____14515 =
             let uu____14518 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14518  in
           FStar_All.pipe_right uu____14515 FStar_Util.set_elements  in
         (let uu____14534 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14534
          then
            let uu____14539 =
              let uu____14541 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14541  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14539
          else ());
         (let r =
            let uu____14550 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14550  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14589 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14589
                     then
                       let uu____14594 =
                         let uu____14596 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14596
                          in
                       let uu____14600 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14602 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14594 uu____14600 uu____14602
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
        let uu____14632 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14632 FStar_Util.set_elements  in
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
        | ([],uu____14671) -> generalized_univ_names
        | (uu____14678,[]) -> explicit_univ_names
        | uu____14685 ->
            let uu____14694 =
              let uu____14700 =
                let uu____14702 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14702
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14700)
               in
            FStar_Errors.raise_error uu____14694 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.NoFullNorm;
          FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____14724 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14724
       then
         let uu____14729 = FStar_Syntax_Print.term_to_string t  in
         let uu____14731 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14729 uu____14731
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14740 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14740
        then
          let uu____14745 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14745
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14754 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14754
         then
           let uu____14759 = FStar_Syntax_Print.term_to_string t  in
           let uu____14761 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14759 uu____14761
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_name
          Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____14845 =
          let uu____14847 =
            FStar_Util.for_all
              (fun uu____14861  ->
                 match uu____14861 with
                 | (uu____14871,uu____14872,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14847  in
        if uu____14845
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14924 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14924
              then
                let uu____14927 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14927
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14934 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14934
               then
                 let uu____14937 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14937
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14955 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14955 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14989 =
             match uu____14989 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15026 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15026
                   then
                     let uu____15031 =
                       let uu____15033 =
                         let uu____15037 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____15037
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15033
                         (FStar_String.concat ", ")
                        in
                     let uu____15085 =
                       let uu____15087 =
                         let uu____15091 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15091
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15104 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15106 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15104
                                   uu____15106))
                          in
                       FStar_All.pipe_right uu____15087
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15031
                       uu____15085
                   else ());
                  (let univs2 =
                     let uu____15120 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____15132 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____15132) univs1
                       uu____15120
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15139 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15139
                    then
                      let uu____15144 =
                        let uu____15146 =
                          let uu____15150 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____15150
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15146
                          (FStar_String.concat ", ")
                         in
                      let uu____15198 =
                        let uu____15200 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15214 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15216 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15214
                                    uu____15216))
                           in
                        FStar_All.pipe_right uu____15200
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15144 uu____15198
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____15237 =
             let uu____15254 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15254  in
           match uu____15237 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15344 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15344
                 then ()
                 else
                   (let uu____15349 = lec_hd  in
                    match uu____15349 with
                    | (lb1,uu____15357,uu____15358) ->
                        let uu____15359 = lec2  in
                        (match uu____15359 with
                         | (lb2,uu____15367,uu____15368) ->
                             let msg =
                               let uu____15371 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15373 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15371 uu____15373
                                in
                             let uu____15376 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15376))
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
                 let uu____15444 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15444
                 then ()
                 else
                   (let uu____15449 = lec_hd  in
                    match uu____15449 with
                    | (lb1,uu____15457,uu____15458) ->
                        let uu____15459 = lec2  in
                        (match uu____15459 with
                         | (lb2,uu____15467,uu____15468) ->
                             let msg =
                               let uu____15471 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15473 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15471 uu____15473
                                in
                             let uu____15476 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15476))
                  in
               let lecs1 =
                 let uu____15487 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15540 = univs_and_uvars_of_lec this_lec  in
                        match uu____15540 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15487 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15645 = lec_hd  in
                   match uu____15645 with
                   | (lbname,e,c) ->
                       let uu____15655 =
                         let uu____15661 =
                           let uu____15663 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15665 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15667 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15663 uu____15665 uu____15667
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15661)
                          in
                       let uu____15671 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15655 uu____15671
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15690 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15690 with
                         | FStar_Pervasives_Native.Some uu____15699 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15707 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15711 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15711 with
                              | (bs,kres) ->
                                  ((let uu____15731 =
                                      let uu____15732 =
                                        let uu____15735 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15735
                                         in
                                      uu____15732.FStar_Syntax_Syntax.n  in
                                    match uu____15731 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15736
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15740 =
                                          let uu____15742 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15742  in
                                        if uu____15740
                                        then fail1 kres
                                        else ()
                                    | uu____15747 -> fail1 kres);
                                   (let a =
                                      let uu____15749 =
                                        let uu____15752 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15755  ->
                                             FStar_Pervasives_Native.Some
                                               _15755) uu____15752
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15749
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15763 ->
                                          let uu____15764 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15764
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
                      (fun uu____15867  ->
                         match uu____15867 with
                         | (lbname,e,c) ->
                             let uu____15913 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15974 ->
                                   let uu____15987 = (e, c)  in
                                   (match uu____15987 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Env.Beta;
                                            FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Env.CompressUvars;
                                            FStar_TypeChecker_Env.NoFullNorm;
                                            FStar_TypeChecker_Env.Exclude
                                              FStar_TypeChecker_Env.Zeta] env
                                            c
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
                                                (fun uu____16027  ->
                                                   match uu____16027 with
                                                   | (x,uu____16033) ->
                                                       let uu____16034 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16034)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16052 =
                                                let uu____16054 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16054
                                                 in
                                              if uu____16052
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
                                          let uu____16063 =
                                            let uu____16064 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16064.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16063 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16089 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16089 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16100 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16104 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16104, gen_tvars))
                                in
                             (match uu____15913 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____16251 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16251
         then
           let uu____16254 =
             let uu____16256 =
               FStar_List.map
                 (fun uu____16271  ->
                    match uu____16271 with
                    | (lb,uu____16280,uu____16281) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16256 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16254
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16307  ->
                match uu____16307 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16336 = gen env is_rec lecs  in
           match uu____16336 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16435  ->
                       match uu____16435 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16497 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16497
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16545  ->
                           match uu____16545 with
                           | (l,us,e,c,gvs) ->
                               let uu____16579 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16581 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16583 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16585 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16587 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16579 uu____16581 uu____16583
                                 uu____16585 uu____16587))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16632  ->
                match uu____16632 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16676 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16676, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.comp) Prims.list ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_Syntax_Syntax.binder Prims.list) Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____16731 =
          let uu____16735 =
            let uu____16737 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16737  in
          FStar_Pervasives_Native.Some uu____16735  in
        FStar_Profiling.profile
          (fun uu____16754  -> generalize' env is_rec lecs) uu____16731
          "FStar.TypeChecker.Util.generalize"
  
let (check_has_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu____16811 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16811 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16817 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16817
                    (fun _16820  -> FStar_Pervasives_Native.Some _16820)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16829 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16829 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16835 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun _16838  -> FStar_Pervasives_Native.Some _16838)
                       uu____16835)
             in
          let uu____16839 = maybe_coerce_lc env1 e lc t2  in
          match uu____16839 with
          | (e1,lc1,g_c) ->
              let uu____16855 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16855 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16864 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16870 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16864 uu____16870
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16879 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16879
                     then
                       let uu____16884 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16884
                     else ());
                    (let uu____16890 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16890))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16918 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16918
         then
           let uu____16921 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16921
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16935 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16935 with
         | (c,g_c) ->
             let uu____16947 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16947
             then
               let uu____16955 =
                 let uu____16957 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16957  in
               (uu____16955, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16965 =
                    let uu____16966 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16966
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16965
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16967 = check_trivial_precondition env c1  in
                match uu____16967 with
                | (ct,vc,g_pre) ->
                    ((let uu____16983 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16983
                      then
                        let uu____16988 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16988
                      else ());
                     (let uu____16993 =
                        let uu____16995 =
                          let uu____16996 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16996  in
                        discharge uu____16995  in
                      let uu____16997 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16993, uu____16997)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17031 =
        match uu___8_17031 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____17041)::[] -> f fst1
        | uu____17066 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17078 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17078
          (fun _17079  -> FStar_TypeChecker_Common.NonTrivial _17079)
         in
      let op_or_e e =
        let uu____17090 =
          let uu____17091 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17091  in
        FStar_All.pipe_right uu____17090
          (fun _17094  -> FStar_TypeChecker_Common.NonTrivial _17094)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _17101  -> FStar_TypeChecker_Common.NonTrivial _17101)
         in
      let op_or_t t =
        let uu____17112 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____17112
          (fun _17115  -> FStar_TypeChecker_Common.NonTrivial _17115)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _17122  -> FStar_TypeChecker_Common.NonTrivial _17122)
         in
      let short_op_ite uu___9_17128 =
        match uu___9_17128 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17138)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17165)::[] ->
            let uu____17206 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17206
              (fun _17207  -> FStar_TypeChecker_Common.NonTrivial _17207)
        | uu____17208 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17220 =
          let uu____17228 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17228)  in
        let uu____17236 =
          let uu____17246 =
            let uu____17254 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17254)  in
          let uu____17262 =
            let uu____17272 =
              let uu____17280 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17280)  in
            let uu____17288 =
              let uu____17298 =
                let uu____17306 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17306)  in
              let uu____17314 =
                let uu____17324 =
                  let uu____17332 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17332)  in
                [uu____17324; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17298 :: uu____17314  in
            uu____17272 :: uu____17288  in
          uu____17246 :: uu____17262  in
        uu____17220 :: uu____17236  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17394 =
            FStar_Util.find_map table
              (fun uu____17409  ->
                 match uu____17409 with
                 | (x,mk1) ->
                     let uu____17426 = FStar_Ident.lid_equals x lid  in
                     if uu____17426
                     then
                       let uu____17431 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17431
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17394 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17435 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17443 =
      let uu____17444 = FStar_Syntax_Util.un_uinst l  in
      uu____17444.FStar_Syntax_Syntax.n  in
    match uu____17443 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17449 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17485)::uu____17486 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17505 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17514,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17515))::uu____17516 -> bs
      | uu____17534 ->
          let uu____17535 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17535 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17539 =
                 let uu____17540 = FStar_Syntax_Subst.compress t  in
                 uu____17540.FStar_Syntax_Syntax.n  in
               (match uu____17539 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17544) ->
                    let uu____17565 =
                      FStar_Util.prefix_until
                        (fun uu___10_17605  ->
                           match uu___10_17605 with
                           | (uu____17613,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17614)) ->
                               false
                           | uu____17619 -> true) bs'
                       in
                    (match uu____17565 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17655,uu____17656) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17728,uu____17729) ->
                         let uu____17802 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17822  ->
                                   match uu____17822 with
                                   | (x,uu____17831) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17802
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17880  ->
                                     match uu____17880 with
                                     | (x,i) ->
                                         let uu____17899 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17899, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17910 -> bs))
  
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
            let uu____17939 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17939
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
          let uu____17970 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17970
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
        (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____18013 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18013
         then
           ((let uu____18018 = FStar_Ident.text_of_lid lident  in
             d uu____18018);
            (let uu____18020 = FStar_Ident.text_of_lid lident  in
             let uu____18022 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18020 uu____18022))
         else ());
        (let fv =
           let uu____18028 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18028
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
         let uu____18040 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2120_18042 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2120_18042.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2120_18042.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2120_18042.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2120_18042.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2120_18042.FStar_Syntax_Syntax.sigopts)
           }), uu____18040))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18060 =
        match uu___11_18060 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18063 -> false  in
      let reducibility uu___12_18071 =
        match uu___12_18071 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18078 -> false  in
      let assumption uu___13_18086 =
        match uu___13_18086 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18090 -> false  in
      let reification uu___14_18098 =
        match uu___14_18098 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18101 -> true
        | uu____18103 -> false  in
      let inferred uu___15_18111 =
        match uu___15_18111 with
        | FStar_Syntax_Syntax.Discriminator uu____18113 -> true
        | FStar_Syntax_Syntax.Projector uu____18115 -> true
        | FStar_Syntax_Syntax.RecordType uu____18121 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18131 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18144 -> false  in
      let has_eq uu___16_18152 =
        match uu___16_18152 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18156 -> false  in
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
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (visibility x))
                           || (reducibility x))
                          || (reification x))
                         || (inferred x))
                        || (has_eq x))
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
        | FStar_Syntax_Syntax.Reflectable uu____18235 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18242 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18275 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18275))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18306 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18306
                       FStar_Parser_Const.erasable_attr)))
           in
        let se_has_erasable_attr =
          FStar_Syntax_Util.has_attribute se1.FStar_Syntax_Syntax.sigattrs
            FStar_Parser_Const.erasable_attr
           in
        if
          (val_exists && val_has_erasable_attr) &&
            (Prims.op_Negation se_has_erasable_attr)
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributes between declaration and definition: Declaration is marked `erasable` but the definition is not")
            r
        else ();
        if
          (val_exists && (Prims.op_Negation val_has_erasable_attr)) &&
            se_has_erasable_attr
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_QulifierListNotPermitted,
              "Mismatch of attributed between declaration and definition: Definition is marked `erasable` but the declaration is not")
            r
        else ();
        if se_has_erasable_attr
        then
          (match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_bundle uu____18326 ->
               let uu____18335 =
                 let uu____18337 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18343  ->
                           match uu___17_18343 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18346 -> false))
                    in
                 Prims.op_Negation uu____18337  in
               if uu____18335
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18353 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18360 -> ()
           | uu____18373 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_QulifierListNotPermitted,
                   "Illegal attribute: the `erasable` attribute is only permitted on inductive type definitions")
                 r)
        else ()  in
      let quals =
        FStar_All.pipe_right (FStar_Syntax_Util.quals_of_sigelt se)
          (FStar_List.filter
             (fun x  -> Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)))
         in
      let uu____18387 =
        let uu____18389 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18395  ->
                  match uu___18_18395 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18398 -> false))
           in
        FStar_All.pipe_right uu____18389 Prims.op_Negation  in
      if uu____18387
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18419 =
            let uu____18425 =
              let uu____18427 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18427 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18425)  in
          FStar_Errors.raise_error uu____18419 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18445 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18453 =
            let uu____18455 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18455  in
          if uu____18453 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18466),uu____18467) ->
              ((let uu____18479 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18479
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18488 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18488
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18499 ->
              ((let uu____18509 =
                  let uu____18511 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_all
                         (fun x  ->
                            (((((x = FStar_Syntax_Syntax.Abstract) ||
                                  (x =
                                     FStar_Syntax_Syntax.Inline_for_extraction))
                                 || (x = FStar_Syntax_Syntax.NoExtract))
                                || (inferred x))
                               || (visibility x))
                              || (has_eq x)))
                     in
                  Prims.op_Negation uu____18511  in
                if uu____18509 then err'1 () else ());
               (let uu____18521 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18527  ->
                           match uu___19_18527 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18530 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18521
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18536 ->
              let uu____18543 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18543 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18551 ->
              let uu____18558 =
                let uu____18560 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18560  in
              if uu____18558 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18570 ->
              let uu____18571 =
                let uu____18573 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18573  in
              if uu____18571 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18583 ->
              let uu____18596 =
                let uu____18598 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18598  in
              if uu____18596 then err'1 () else ()
          | uu____18608 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18647 =
          let uu____18648 = FStar_Syntax_Subst.compress t1  in
          uu____18648.FStar_Syntax_Syntax.n  in
        match uu____18647 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18652 ->
            let uu____18667 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18667 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18676;
               FStar_Syntax_Syntax.index = uu____18677;
               FStar_Syntax_Syntax.sort = t2;_},uu____18679)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18688) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18714) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18720 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Primops;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF;
            FStar_TypeChecker_Env.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.AllowUnboundUniverses;
            FStar_TypeChecker_Env.Zeta;
            FStar_TypeChecker_Env.Iota;
            FStar_TypeChecker_Env.Unascribe] env t1
           in
        let res =
          (FStar_TypeChecker_Env.non_informative env t2) || (descend env t2)
           in
        (let uu____18730 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18730
         then
           let uu____18735 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18735
         else ());
        res
       in aux g t
  
let (fresh_effect_repr :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.universe ->
              FStar_Syntax_Syntax.term ->
                (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun signature_ts  ->
          fun repr_ts_opt  ->
            fun u  ->
              fun a_tm  ->
                let fail1 t =
                  let uu____18800 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18800 r  in
                let uu____18810 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18810 with
                | (uu____18819,signature) ->
                    let uu____18821 =
                      let uu____18822 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18822.FStar_Syntax_Syntax.n  in
                    (match uu____18821 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18830) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18878 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18893 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18895 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18893 eff_name.FStar_Ident.str
                                       uu____18895) r
                                 in
                              (match uu____18878 with
                               | (is,g) ->
                                   let uu____18908 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18910 =
                                             let uu____18911 =
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 is
                                                in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = [u];
                                               FStar_Syntax_Syntax.effect_name
                                                 = eff_name;
                                               FStar_Syntax_Syntax.result_typ
                                                 = a_tm;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____18911;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18910
                                            in
                                         let uu____18930 =
                                           let uu____18937 =
                                             let uu____18938 =
                                               let uu____18953 =
                                                 let uu____18962 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18962]  in
                                               (uu____18953, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18938
                                              in
                                           FStar_Syntax_Syntax.mk uu____18937
                                            in
                                         uu____18930
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18993 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18993
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19002 =
                                           let uu____19007 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____19007
                                            in
                                         uu____19002
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18908, g))
                          | uu____19016 -> fail1 signature)
                     | uu____19017 -> fail1 signature)
  
let (fresh_effect_repr_en :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun u  ->
          fun a_tm  ->
            let uu____19048 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19048
              (fun ed  ->
                 let uu____19056 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19056 u a_tm)
  
let (layered_effect_indices_as_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun r  ->
      fun eff_name  ->
        fun sig_ts  ->
          fun u  ->
            fun a_tm  ->
              let uu____19092 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19092 with
              | (uu____19097,sig_tm) ->
                  let fail1 t =
                    let uu____19105 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19105 r  in
                  let uu____19111 =
                    let uu____19112 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19112.FStar_Syntax_Syntax.n  in
                  (match uu____19111 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19116) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19139)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19161 -> fail1 sig_tm)
                   | uu____19162 -> fail1 sig_tm)
  
let (lift_tf_layered_effect :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun tgt  ->
    fun lift_ts  ->
      fun env  ->
        fun c  ->
          (let uu____19193 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19193
           then
             let uu____19198 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19200 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19198 uu____19200
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19207 =
             let uu____19218 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19219 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19218, (ct.FStar_Syntax_Syntax.result_typ), uu____19219)
              in
           match uu____19207 with
           | (u,a,c_is) ->
               let uu____19267 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19267 with
                | (uu____19276,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19287 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19289 = FStar_Ident.string_of_lid tgt  in
                      let uu____19291 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19287 uu____19289 s uu____19291
                       in
                    let uu____19294 =
                      let uu____19327 =
                        let uu____19328 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19328.FStar_Syntax_Syntax.n  in
                      match uu____19327 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19392 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19392 with
                           | (a_b::bs1,c2) ->
                               let uu____19452 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19452, c2))
                      | uu____19540 ->
                          let uu____19541 =
                            let uu____19547 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19547)
                             in
                          FStar_Errors.raise_error uu____19541 r
                       in
                    (match uu____19294 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19665 =
                           let uu____19672 =
                             let uu____19673 =
                               let uu____19674 =
                                 let uu____19681 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19681, a)  in
                               FStar_Syntax_Syntax.NT uu____19674  in
                             [uu____19673]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19672
                             (fun b  ->
                                let uu____19698 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19700 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19702 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19704 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19698 uu____19700 uu____19702
                                  uu____19704) r
                            in
                         (match uu____19665 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19718 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19718
                                then
                                  let uu____19723 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19732 =
                                             let uu____19734 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19734
                                              in
                                           Prims.op_Hat s uu____19732) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19723
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19765 =
                                           let uu____19772 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19772, t)  in
                                         FStar_Syntax_Syntax.NT uu____19765)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19791 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19791
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19797 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19797
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19806 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19806)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19808 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19808
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19812 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19812 r
                                   in
                                let fml =
                                  let uu____19817 =
                                    let uu____19822 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19823 =
                                      let uu____19824 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19824
                                       in
                                    (uu____19822, uu____19823)  in
                                  match uu____19817 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19850 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19850
                                 then
                                   let uu____19856 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19856
                                 else ());
                                (let c1 =
                                   let uu____19862 =
                                     let uu____19863 =
                                       FStar_All.pipe_right is
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg)
                                        in
                                     {
                                       FStar_Syntax_Syntax.comp_univs =
                                         (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                       FStar_Syntax_Syntax.effect_name = tgt;
                                       FStar_Syntax_Syntax.result_typ = a;
                                       FStar_Syntax_Syntax.effect_args =
                                         uu____19863;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19862
                                    in
                                 (let uu____19887 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19887
                                  then
                                    let uu____19892 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19892
                                  else ());
                                 (let uu____19897 =
                                    let uu____19898 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19899 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19898 uu____19899
                                     in
                                  (c1, uu____19897)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19913 .
    'Auu____19913 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub1  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____19942 =
                let uu____19947 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19947
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19942 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19990 =
                let uu____19991 =
                  let uu____19994 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19994
                    FStar_Syntax_Subst.compress
                   in
                uu____19991.FStar_Syntax_Syntax.n  in
              match uu____19990 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20017::bs,uu____20019)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20059 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20059
                    FStar_Pervasives_Native.fst
              | uu____20165 ->
                  let uu____20166 =
                    let uu____20172 =
                      let uu____20174 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20174
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20172)  in
                  FStar_Errors.raise_error uu____20166
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20201 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20210 =
                let uu____20221 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20257  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20264 =
                  let uu____20275 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20275]  in
                FStar_List.append uu____20221 uu____20264  in
              uu____20201 :: uu____20210  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20346 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20346 with
        | (uu____20351,t) ->
            let err n1 =
              let uu____20361 =
                let uu____20367 =
                  let uu____20369 = FStar_Ident.string_of_lid datacon  in
                  let uu____20371 = FStar_Util.string_of_int n1  in
                  let uu____20373 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20369 uu____20371 uu____20373
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20367)
                 in
              let uu____20377 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20361 uu____20377  in
            let uu____20378 =
              let uu____20379 = FStar_Syntax_Subst.compress t  in
              uu____20379.FStar_Syntax_Syntax.n  in
            (match uu____20378 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20383) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20438  ->
                           match uu____20438 with
                           | (uu____20446,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20455 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____20487 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____20487
                      FStar_Pervasives_Native.fst)
             | uu____20498 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20511 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20511
      then
        let uu____20514 =
          let uu____20527 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20527
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20514;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20562 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20562 with
           | (uu____20571,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20590 =
                 let uu____20591 =
                   let uu___2496_20592 = ct  in
                   let uu____20593 =
                     let uu____20604 =
                       let uu____20613 =
                         let uu____20614 =
                           let uu____20621 =
                             let uu____20622 =
                               let uu____20639 =
                                 let uu____20650 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20650; wp]  in
                               (lift_t, uu____20639)  in
                             FStar_Syntax_Syntax.Tm_app uu____20622  in
                           FStar_Syntax_Syntax.mk uu____20621  in
                         uu____20614 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20613
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20604]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2496_20592.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2496_20592.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20593;
                     FStar_Syntax_Syntax.flags =
                       (uu___2496_20592.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20591  in
               (uu____20590, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20750 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20750 with
           | (uu____20757,lift_t) ->
               let uu____20759 =
                 let uu____20766 =
                   let uu____20767 =
                     let uu____20784 =
                       let uu____20795 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20804 =
                         let uu____20815 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20824 =
                           let uu____20835 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20835]  in
                         uu____20815 :: uu____20824  in
                       uu____20795 :: uu____20804  in
                     (lift_t, uu____20784)  in
                   FStar_Syntax_Syntax.Tm_app uu____20767  in
                 FStar_Syntax_Syntax.mk uu____20766  in
               uu____20759 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20888 =
           let uu____20901 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20901 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20888;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20937  ->
                        fun uu____20938  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20961 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20961
  
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n1 p
              (fun env1  ->
                 fun c1  ->
                   fun bv_opt  ->
                     fun c2  ->
                       fun flags  ->
                         fun r  ->
                           mk_indexed_bind env1 m n1 p ty c1 bv_opt c2 flags
                             r)
  