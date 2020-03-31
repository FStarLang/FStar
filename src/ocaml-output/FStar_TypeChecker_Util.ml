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
                         FStar_Util.print1
                           "///////////////////////////////Bind at %s/////////////////////\n"
                           uu____3747
                       else ());
                      (let uu____3753 =
                         let uu____3760 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3761 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3762 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3760, uu____3761, uu____3762)  in
                       match uu____3753 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3770 =
                             let uu____3781 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3782 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3781,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3782)
                              in
                           (match uu____3770 with
                            | (u1,t1,is1) ->
                                let uu____3816 =
                                  let uu____3827 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3828 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3827,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3828)
                                   in
                                (match uu____3816 with
                                 | (u2,t2,is2) ->
                                     let uu____3862 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3862 with
                                      | (uu____3871,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3886 =
                                              let uu____3888 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3888 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3886)
                                             in
                                          let uu____3892 =
                                            let uu____3937 =
                                              let uu____3938 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3938.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3937 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4014 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4014 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4099 =
                                                       let uu____4126 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4126
                                                         (fun uu____4211  ->
                                                            match uu____4211
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4292
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4305
                                                                  =
                                                                  let uu____4312
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4312
                                                                   in
                                                                (l1,
                                                                  uu____4292,
                                                                  uu____4305))
                                                        in
                                                     (match uu____4099 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4472 ->
                                                let uu____4473 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4473 r1
                                             in
                                          (match uu____3892 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4598 =
                                                 let uu____4605 =
                                                   let uu____4606 =
                                                     let uu____4607 =
                                                       let uu____4614 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4614, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4607
                                                      in
                                                   let uu____4625 =
                                                     let uu____4628 =
                                                       let uu____4629 =
                                                         let uu____4636 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4636, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4629
                                                        in
                                                     [uu____4628]  in
                                                   uu____4606 :: uu____4625
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4605
                                                   (fun b1  ->
                                                      let uu____4652 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4654 =
                                                        let uu____4656 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4658 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4660 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4656
                                                          uu____4658
                                                          uu____4660
                                                         in
                                                      let uu____4663 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4652 uu____4654
                                                        uu____4663) r1
                                                  in
                                               (match uu____4598 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4700 =
                                                               let uu____4707
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4707,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4700)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4734 =
                                                          let uu____4737 =
                                                            let uu____4738 =
                                                              let uu____4739
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4739.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4738
                                                             in
                                                          let uu____4748 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4737
                                                            uu____4748 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4734
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4761
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq_maybe_defer
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4761)
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
                                                        let uu____4780 =
                                                          let uu____4781 =
                                                            let uu____4784 =
                                                              let uu____4785
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4785.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4784
                                                             in
                                                          uu____4781.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4780 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4818 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4818
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4828
                                                                    =
                                                                    let uu____4835
                                                                    =
                                                                    let uu____4836
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4836
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4857
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4860
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4835,
                                                                    uu____4857)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4828
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4874
                                                                   =
                                                                   let uu____4877
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4878
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4877
                                                                    uu____4878
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4874
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4897 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4905
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_maybe_defer
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4905)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4897
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4919 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst1)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4919
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4921 =
                                                        let uu____4926 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4927 =
                                                          let uu____4928 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4928
                                                           in
                                                        (uu____4926,
                                                          uu____4927)
                                                         in
                                                      match uu____4921 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4954 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4955 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4954 uu____4955
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4958 =
                                                        let uu____4959 =
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
                                                            = uu____4959;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4958
                                                       in
                                                    ((let uu____4979 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4979
                                                      then
                                                        let uu____4984 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4984
                                                      else ());
                                                     (let uu____4989 =
                                                        let uu____4990 =
                                                          let uu____4993 =
                                                            let uu____4996 =
                                                              let uu____4999
                                                                =
                                                                let uu____5002
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____5002]
                                                                 in
                                                              g_guard ::
                                                                uu____4999
                                                               in
                                                            f_guard ::
                                                              uu____4996
                                                             in
                                                          g_uvars ::
                                                            uu____4993
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4990
                                                         in
                                                      (c, uu____4989)))))))))
  
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
                let uu____5047 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5073 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5073 with
                  | (a,kwp) ->
                      let uu____5104 = destruct_wp_comp ct1  in
                      let uu____5111 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5104, uu____5111)
                   in
                match uu____5047 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5164 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5164]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5184 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5184]
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
                      let uu____5231 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5240 =
                        let uu____5251 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5260 =
                          let uu____5271 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5280 =
                            let uu____5291 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5300 =
                              let uu____5311 =
                                let uu____5320 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5320  in
                              [uu____5311]  in
                            uu____5291 :: uu____5300  in
                          uu____5271 :: uu____5280  in
                        uu____5251 :: uu____5260  in
                      uu____5231 :: uu____5240  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5373 =
                        let uu____5378 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5378 wp_args  in
                      uu____5373 FStar_Pervasives_Native.None
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
              let uu____5426 =
                let uu____5431 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5432 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5431, uu____5432)  in
              match uu____5426 with
              | (ct1,ct2) ->
                  let uu____5439 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5439 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5490 = lift_comps env c1 c2 b true  in
                       (match uu____5490 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5508 =
                              let uu____5513 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5514 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5513, uu____5514)  in
                            (match uu____5508 with
                             | (ct11,ct21) ->
                                 let uu____5521 =
                                   let uu____5526 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5526
                                   then
                                     let bind_t =
                                       let uu____5534 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5534
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5537 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5537,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5521 with
                                  | (c,g_bind) ->
                                      let uu____5544 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5544)))))
  
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
            let uu____5580 =
              let uu____5581 =
                let uu____5592 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5592]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5581;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5580  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5637 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5643  ->
              match uu___1_5643 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5646 -> false))
       in
    if uu____5637
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5658  ->
              match uu___2_5658 with
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
        let uu____5686 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5686
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5697 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5697  in
           let pure_assume_wp1 =
             let uu____5702 = FStar_TypeChecker_Env.get_range env  in
             let uu____5703 =
               let uu____5708 =
                 let uu____5709 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5709]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5708  in
             uu____5703 FStar_Pervasives_Native.None uu____5702  in
           let uu____5742 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5742)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5770 =
          let uu____5771 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5771 with
          | (c,g_c) ->
              let uu____5782 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5782
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5796 = weaken_comp env c f1  in
                     (match uu____5796 with
                      | (c1,g_w) ->
                          let uu____5807 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5807)))
           in
        let uu____5808 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5808 weaken
  
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
                 let uu____5865 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5865  in
               let pure_assert_wp1 =
                 let uu____5870 =
                   let uu____5875 =
                     let uu____5876 =
                       let uu____5885 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5885
                        in
                     [uu____5876]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5875
                    in
                 uu____5870 FStar_Pervasives_Native.None r  in
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
       (let uu____5977 = FStar_Options.debug_any ()  in
        if uu____5977
        then
          let uu____5980 = FStar_Util.string_of_int n1  in
          let uu____5982 =
            let uu____5984 =
              let uu____5986 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____5986  in
            FStar_Util.string_of_int uu____5984  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____5980
            uu____5982
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
            let uu____6041 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6041
            then (lc, g0)
            else
              (let flags =
                 let uu____6053 =
                   let uu____6061 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6061
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6053 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6091 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6099  ->
                               match uu___3_6099 with
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
                               | uu____6102 -> []))
                        in
                     FStar_List.append flags uu____6091
                  in
               let strengthen uu____6112 =
                 let uu____6113 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6113 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6132 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6132 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6139 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6139
                              then
                                let uu____6143 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6145 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6143 uu____6145
                              else ());
                             (let uu____6150 =
                                strengthen_comp env reason c f flags  in
                              match uu____6150 with
                              | (c1,g_s) ->
                                  let uu____6161 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6161))))
                  in
               let uu____6162 =
                 let uu____6163 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6163
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6162,
                 (let uu___718_6165 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___718_6165.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___718_6165.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___718_6165.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6174  ->
            match uu___4_6174 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6178 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6207 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6207
          then e
          else
            (let uu____6214 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6217 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6217)
                in
             if uu____6214
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
                | uu____6287 -> false  in
              if is_unit1
              then
                let uu____6294 =
                  let uu____6296 =
                    let uu____6297 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6297
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6296
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6294
                 then
                   let uu____6306 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6306 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6350 =
                           let uu____6353 =
                             let uu____6354 =
                               let uu____6361 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6361, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6354  in
                           [uu____6353]  in
                         FStar_Syntax_Subst.subst uu____6350 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6374 = close_wp_comp env [x] c  in
                    (uu____6374, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6377 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6405  ->
            match uu____6405 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6425 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6425 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6438 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6438
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6448 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6448
                       then
                         let uu____6453 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6453
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6460 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6460
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6469 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6469
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6476 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6476
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6492 =
                  let uu____6493 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6493
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6501 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6501, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6504 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6504 with
                     | (c1,g_c1) ->
                         let uu____6515 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6515 with
                          | (c2,g_c2) ->
                              let trivial_guard1 =
                                let uu____6527 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6530 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6530
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6527
                                 in
                              (debug1
                                 (fun uu____6556  ->
                                    let uu____6557 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6559 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6564 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6557 uu____6559 uu____6564);
                               (let aux uu____6582 =
                                  let uu____6583 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6583
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6614
                                        ->
                                        let uu____6615 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6615
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6647 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6647
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6694 =
                                  let aux_with_trivial_guard uu____6724 =
                                    let uu____6725 = aux ()  in
                                    match uu____6725 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard1, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6783 =
                                    let uu____6785 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6785  in
                                  if uu____6783
                                  then
                                    let uu____6801 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6801
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard1,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6828 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6828))
                                  else
                                    (let uu____6845 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6845
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___822_6876 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___822_6876.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___822_6876.FStar_Syntax_Syntax.index);
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
                                           let uu____6907 =
                                             let uu____6912 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6912
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6907 with
                                            | (c21,g_close) ->
                                                let uu____6933 =
                                                  let uu____6941 =
                                                    let uu____6942 =
                                                      let uu____6945 =
                                                        let uu____6948 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6948; g_close]
                                                         in
                                                      g_c1 :: uu____6945  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6942
                                                     in
                                                  (c21, uu____6941, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6933)
                                       | (uu____6961,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6973 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6973 with
                                            | (c21,g_close) ->
                                                let uu____6996 =
                                                  let uu____7004 =
                                                    let uu____7005 =
                                                      let uu____7008 =
                                                        let uu____7011 =
                                                          let uu____7012 =
                                                            let uu____7013 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____7013]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____7012
                                                            g_c2
                                                           in
                                                        [uu____7011; g_close]
                                                         in
                                                      g_c1 :: uu____7008  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7005
                                                     in
                                                  (c21, uu____7004,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6996)
                                       | (uu____7042,uu____7043) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7058 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7058
                                        then
                                          let uu____7073 =
                                            let uu____7081 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7081, trivial_guard1,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7073
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7094 = try_simplify ()  in
                                match uu____7094 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug1
                                       (fun uu____7129  ->
                                          let uu____7130 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7130);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7146  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7177 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7177 with
                                        | (c,g_bind) ->
                                            let uu____7188 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7188)
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
                                        let uu____7215 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7215 with
                                        | (m,uu____7227,lift2) ->
                                            let uu____7229 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7229 with
                                             | (c23,g2) ->
                                                 let uu____7240 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7240 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7256 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7256
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7266 =
                                                          let uu____7271 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7272 =
                                                            let uu____7273 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7282 =
                                                              let uu____7293
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7293]
                                                               in
                                                            uu____7273 ::
                                                              uu____7282
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7271
                                                            uu____7272
                                                           in
                                                        uu____7266
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7326 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7326 with
                                                       | (c,g_s) ->
                                                           let uu____7341 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7341))))
                                         in
                                      let uu____7342 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7358 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7358, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7342 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7374 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7374
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7383 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7383
                                             then
                                               (debug1
                                                  (fun uu____7397  ->
                                                     let uu____7398 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7400 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7398 uu____7400);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7407 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7407
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7412 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7415 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7415)
                                                   in
                                                if uu____7412
                                                then
                                                  let e1' =
                                                    let uu____7440 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7440
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7452  ->
                                                        let uu____7453 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7455 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7453
                                                          uu____7455);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7470  ->
                                                        let uu____7471 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7473 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7471
                                                          uu____7473);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7480 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7480
                                                       in
                                                    let uu____7481 =
                                                      let uu____7486 =
                                                        let uu____7487 =
                                                          let uu____7488 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7488]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7487
                                                         in
                                                      weaken_comp uu____7486
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7481 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7514 =
                                                            let uu____7515 =
                                                              let uu____7516
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7516]
                                                               in
                                                            let uu____7535 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7515
                                                              uu____7535
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7514
                                                           in
                                                        let uu____7536 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7536
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7547 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7547))))))
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
      | uu____7564 -> g2
  
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
            (let uu____7588 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7588)
           in
        let flags =
          if should_return1
          then
            let uu____7596 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7596
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7614 =
          let uu____7615 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7615 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7628 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7628
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7636 =
                  let uu____7638 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7638  in
                (if uu____7636
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___947_7647 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___947_7647.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___947_7647.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___947_7647.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7648 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7648, g_c)
                 else
                   (let uu____7651 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7651, g_c)))
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
                   let uu____7662 =
                     let uu____7663 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7663
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7662
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7666 =
                   let uu____7671 =
                     let uu____7672 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7672
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7671  in
                 match uu____7666 with
                 | (bind_c,g_bind) ->
                     let uu____7681 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7682 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7681, uu____7682))
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
            fun uu____7718  ->
              match uu____7718 with
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
                    let uu____7730 =
                      ((let uu____7734 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7734) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7730
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7752 =
        let uu____7753 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7753  in
      FStar_Syntax_Syntax.fvar uu____7752 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7803 =
                    let uu____7808 =
                      let uu____7809 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7809 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7808 [u_a]
                     in
                  match uu____7803 with
                  | (uu____7820,conjunction) ->
                      let uu____7822 =
                        let uu____7831 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7846 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7831, uu____7846)  in
                      (match uu____7822 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7892 =
                               let uu____7894 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7894 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7892)
                              in
                           let uu____7898 =
                             let uu____7943 =
                               let uu____7944 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7944.FStar_Syntax_Syntax.n  in
                             match uu____7943 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7993) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____8025 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____8025 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8097 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8097 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8245 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8245)))
                             | uu____8278 ->
                                 let uu____8279 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8279 r
                              in
                           (match uu____7898 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8404 =
                                  let uu____8411 =
                                    let uu____8412 =
                                      let uu____8413 =
                                        let uu____8420 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8420, a)  in
                                      FStar_Syntax_Syntax.NT uu____8413  in
                                    [uu____8412]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8411
                                    (fun b  ->
                                       let uu____8436 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8438 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8440 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8436 uu____8438 uu____8440) r
                                   in
                                (match uu____8404 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8478 =
                                                let uu____8485 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8485, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8478) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8524 =
                                           let uu____8525 =
                                             let uu____8528 =
                                               let uu____8529 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8529.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8528
                                              in
                                           uu____8525.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8524 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8540,uu____8541::is) ->
                                             let uu____8583 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8583
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8616 ->
                                             let uu____8617 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8617 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8633 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8633)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8638 =
                                           let uu____8639 =
                                             let uu____8642 =
                                               let uu____8643 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8643.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8642
                                              in
                                           uu____8639.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8638 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8654,uu____8655::is) ->
                                             let uu____8697 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8697
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8730 ->
                                             let uu____8731 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8731 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8747 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8747)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8752 =
                                         let uu____8753 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8753.FStar_Syntax_Syntax.n  in
                                       match uu____8752 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8758,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8813 ->
                                           let uu____8814 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8814 r
                                        in
                                     let uu____8823 =
                                       let uu____8824 =
                                         let uu____8825 =
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
                                             uu____8825;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8824
                                        in
                                     let uu____8848 =
                                       let uu____8849 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8849 g_guard
                                        in
                                     (uu____8823, uu____8848))))
  
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
                fun uu____8894  ->
                  let if_then_else1 =
                    let uu____8900 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8900 FStar_Util.must  in
                  let uu____8907 = destruct_wp_comp ct1  in
                  match uu____8907 with
                  | (uu____8918,uu____8919,wp_t) ->
                      let uu____8921 = destruct_wp_comp ct2  in
                      (match uu____8921 with
                       | (uu____8932,uu____8933,wp_e) ->
                           let wp =
                             let uu____8938 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8939 =
                               let uu____8944 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8945 =
                                 let uu____8946 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8955 =
                                   let uu____8966 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8975 =
                                     let uu____8986 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8995 =
                                       let uu____9006 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____9006]  in
                                     uu____8986 :: uu____8995  in
                                   uu____8966 :: uu____8975  in
                                 uu____8946 :: uu____8955  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8944
                                 uu____8945
                                in
                             uu____8939 FStar_Pervasives_Native.None
                               uu____8938
                              in
                           let uu____9055 = mk_comp ed u_a a wp []  in
                           (uu____9055, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____9109 =
              let uu____9110 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9110]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9109  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9157  ->
                   match uu____9157 with
                   | (uu____9171,eff_label,uu____9173,uu____9174) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9187 =
            let uu____9195 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9233  ->
                      match uu____9233 with
                      | (uu____9248,uu____9249,flags,uu____9251) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9268  ->
                                  match uu___5_9268 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9271 -> false))))
               in
            if uu____9195
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9187 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9308 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9310 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9310
                then
                  let uu____9317 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9317, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9324 =
                         let uu____9333 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9333]  in
                       let uu____9352 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9324 uu____9352  in
                     let kwp =
                       let uu____9358 =
                         let uu____9367 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9367]  in
                       let uu____9386 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9358 uu____9386  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9393 =
                         let uu____9394 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9394]  in
                       let uu____9413 =
                         let uu____9416 =
                           let uu____9423 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9423
                            in
                         let uu____9424 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9416 uu____9424  in
                       FStar_Syntax_Util.abs uu____9393 uu____9413
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
                     let uu____9448 =
                       should_not_inline_whole_match ||
                         (let uu____9451 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9451)
                        in
                     if uu____9448 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9463 =
                       let uu____9476 =
                         let uu____9481 =
                           let uu____9492 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9536  ->
                                     match uu____9536 with
                                     | (g,uu____9551,uu____9552,uu____9553)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9492
                             (FStar_List.fold_left
                                (fun uu____9597  ->
                                   fun g  ->
                                     match uu____9597 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9638 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9638
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9481
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9476
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9463
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9739 =
                     FStar_List.fold_right2
                       (fun uu____9802  ->
                          fun bcond  ->
                            fun uu____9804  ->
                              match (uu____9802, uu____9804) with
                              | ((g,eff_label,uu____9864,cthen),(uu____9866,celse,g_comp))
                                  ->
                                  let uu____9913 =
                                    let uu____9918 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9918
                                     in
                                  (match uu____9913 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9930 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9930
                                          in
                                       let uu____9931 =
                                         let uu____9942 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             false
                                            in
                                         match uu____9942 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9970 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9971 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9970, uu____9971,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9931 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____10022 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____10022
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____10057 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____10057
                                               in
                                            let g_lift_else1 =
                                              let uu____10059 =
                                                let uu____10060 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____10060
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____10059
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____10064 =
                                              let uu____10069 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____10069
                                               in
                                            (match uu____10064 with
                                             | (c,g_conjunction) ->
                                                 let uu____10080 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____10080)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9739 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____10097 =
                           let uu____10098 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____10098]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____10097
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____10141::[] -> (comp, g_comp1)
                        | uu____10184 ->
                            let uu____10201 =
                              let uu____10203 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10203
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10201
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
                               let uu____10216 = destruct_wp_comp comp1  in
                               match uu____10216 with
                               | (uu____10227,uu____10228,wp) ->
                                   let ite_wp =
                                     let uu____10231 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10231
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10241 =
                                       let uu____10246 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10247 =
                                         let uu____10248 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10257 =
                                           let uu____10268 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10268]  in
                                         uu____10248 :: uu____10257  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10246 uu____10247
                                        in
                                     uu____10241 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10301 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10301, g_comp1))))
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
          let uu____10336 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10336 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10352 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10358 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10352 uu____10358
              else
                (let uu____10367 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10373 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10367 uu____10373)
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
          let uu____10398 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10398
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10401 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10401
        then u_res
        else
          (let is_total =
             let uu____10408 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10408
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10419 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10419 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10422 =
                    let uu____10428 =
                      let uu____10430 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10430
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10428)
                     in
                  FStar_Errors.raise_error uu____10422
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
      let uu____10454 = destruct_wp_comp ct  in
      match uu____10454 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10473 = FStar_TypeChecker_Env.get_range env  in
            let uu____10474 =
              let uu____10479 =
                let uu____10480 =
                  let uu____10481 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10481 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10480
                 in
              let uu____10488 =
                let uu____10489 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10498 =
                  let uu____10509 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10509]  in
                uu____10489 :: uu____10498  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10479 uu____10488  in
            uu____10474 FStar_Pervasives_Native.None uu____10473  in
          let uu____10542 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10542)
  
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
                  let uu____10597 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10597 with
                  | FStar_Pervasives_Native.Some uu____10612 ->
                      ((let uu____10630 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10630
                        then
                          let uu____10634 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10634
                        else ());
                       (let coercion =
                          let uu____10640 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10640
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10647 =
                            let uu____10648 =
                              let uu____10649 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10649
                               in
                            (FStar_Pervasives_Native.None, uu____10648)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10647
                           in
                        let e1 =
                          let uu____10655 =
                            let uu____10660 =
                              let uu____10661 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10661]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10660
                             in
                          uu____10655 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10695 =
                          let uu____10701 =
                            let uu____10703 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10703
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10701)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10695);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10722 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10740 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10751 -> false 
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
      let uu____10775 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10775 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10820 =
              let uu____10835 =
                let uu____10836 = FStar_Syntax_Subst.compress h1  in
                uu____10836.FStar_Syntax_Syntax.n  in
              (uu____10835, args)  in
            match uu____10820 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10883,uu____10884) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10917) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10938,branches),uu____10940) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11004 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11005 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11005 with
                               | (uu____11006,uu____11007,br_body) ->
                                   let uu____11025 =
                                     let uu____11026 =
                                       let uu____11031 =
                                         let uu____11032 =
                                           let uu____11035 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11035
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11032
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11031  in
                                     FStar_All.pipe_right br_body uu____11026
                                      in
                                   (match uu____11025 with
                                    | No  -> No
                                    | uu____11046 -> Maybe))) No)
            | uu____11047 -> No  in
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
            (((let uu____11099 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11099) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11118 =
                 let uu____11119 = FStar_Syntax_Subst.compress t1  in
                 uu____11119.FStar_Syntax_Syntax.n  in
               match uu____11118 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11124 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11134 =
                 let uu____11135 = FStar_Syntax_Subst.compress t1  in
                 uu____11135.FStar_Syntax_Syntax.n  in
               match uu____11134 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11140 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11151 =
                 let uu____11152 = FStar_Syntax_Subst.compress t2  in
                 uu____11152.FStar_Syntax_Syntax.n  in
               match uu____11151 with
               | FStar_Syntax_Syntax.Tm_type uu____11156 -> true
               | uu____11158 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11161 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11161 with
             | (head1,args) ->
                 ((let uu____11211 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11211
                   then
                     let uu____11215 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11217 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11219 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11221 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11215 uu____11217 uu____11219 uu____11221
                   else ());
                  (let mk_erased u t =
                     let uu____11239 =
                       let uu____11242 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11242 [u]  in
                     let uu____11243 =
                       let uu____11254 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11254]  in
                     FStar_Syntax_Util.mk_app uu____11239 uu____11243  in
                   let uu____11279 =
                     let uu____11294 =
                       let uu____11295 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11295.FStar_Syntax_Syntax.n  in
                     (uu____11294, args)  in
                   match uu____11279 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11333 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11333 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11373 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11373 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11413 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11413 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11453 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11453 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11474 ->
                       let uu____11489 =
                         let uu____11494 = check_erased env res_typ  in
                         let uu____11495 = check_erased env exp_t  in
                         (uu____11494, uu____11495)  in
                       (match uu____11489 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11504 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11504 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11515 =
                                   let uu____11520 =
                                     let uu____11521 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11521]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11520
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11515 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11556 =
                              let uu____11561 =
                                let uu____11562 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11562]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11561
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11556 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11595 ->
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
        let uu____11630 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11630 with
        | (hd1,args) ->
            let uu____11679 =
              let uu____11694 =
                let uu____11695 = FStar_Syntax_Subst.compress hd1  in
                uu____11695.FStar_Syntax_Syntax.n  in
              (uu____11694, args)  in
            (match uu____11679 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11733 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11760  -> FStar_Pervasives_Native.Some _11760)
                   uu____11733
             | uu____11761 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11814 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11814
           then
             let uu____11817 = FStar_Syntax_Print.term_to_string e  in
             let uu____11819 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11821 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11817 uu____11819 uu____11821
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11831 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11831 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11856 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11882 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11882, false)
             else
               (let uu____11892 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11892, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11905) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11917 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11917
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1389_11933 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1389_11933.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1389_11933.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1389_11933.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11940 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11940 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11956 =
                      let uu____11957 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11957 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11977 =
                            let uu____11979 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11979 = FStar_Syntax_Util.Equal  in
                          if uu____11977
                          then
                            ((let uu____11986 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11986
                              then
                                let uu____11990 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11992 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11990 uu____11992
                              else ());
                             (let uu____11997 = set_result_typ1 c  in
                              (uu____11997, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12004 ->
                                   true
                               | uu____12012 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12021 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12021
                                  in
                               let lc1 =
                                 let uu____12023 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12024 =
                                   let uu____12025 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12025)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12023 uu____12024
                                  in
                               ((let uu____12029 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12029
                                 then
                                   let uu____12033 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12035 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12037 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12039 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12033 uu____12035 uu____12037
                                     uu____12039
                                 else ());
                                (let uu____12044 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12044 with
                                 | (c1,g_lc) ->
                                     let uu____12055 = set_result_typ1 c1  in
                                     let uu____12056 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12055, uu____12056)))
                             else
                               ((let uu____12060 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12060
                                 then
                                   let uu____12064 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12066 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12064 uu____12066
                                 else ());
                                (let uu____12071 = set_result_typ1 c  in
                                 (uu____12071, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1426_12075 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1426_12075.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1426_12075.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1426_12075.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12085 =
                      let uu____12086 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12086
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12096 =
                           let uu____12097 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12097.FStar_Syntax_Syntax.n  in
                         match uu____12096 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12104,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12106;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12107;_},uu____12108)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1442_12134 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1442_12134.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1442_12134.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1442_12134.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12135 ->
                             let uu____12136 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12136 with
                              | (c,g_c) ->
                                  ((let uu____12148 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12148
                                    then
                                      let uu____12152 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12154 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12156 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12158 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12152 uu____12154 uu____12156
                                        uu____12158
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
                                        let uu____12171 =
                                          let uu____12176 =
                                            let uu____12177 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12177]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12176
                                           in
                                        uu____12171
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12204 =
                                      let uu____12209 =
                                        FStar_All.pipe_left
                                          (fun _12230  ->
                                             FStar_Pervasives_Native.Some
                                               _12230)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12231 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12232 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12233 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12209
                                        uu____12231 e uu____12232 uu____12233
                                       in
                                    match uu____12204 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1460_12241 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1460_12241.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1460_12241.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12243 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12243
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12246 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12246 with
                                         | (c2,g_lc) ->
                                             ((let uu____12258 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12258
                                               then
                                                 let uu____12262 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12262
                                               else ());
                                              (let uu____12267 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12267))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12276  ->
                              match uu___6_12276 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12279 -> []))
                       in
                    let lc1 =
                      let uu____12281 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12281 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1476_12283 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1476_12283.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1476_12283.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1476_12283.FStar_TypeChecker_Common.implicits)
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
        let uu____12319 =
          let uu____12322 =
            let uu____12327 =
              let uu____12328 =
                let uu____12337 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12337  in
              [uu____12328]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12327  in
          uu____12322 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12319  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12360 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12360
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12379 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12395 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12412 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12412
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12428)::(ens,uu____12430)::uu____12431 ->
                    let uu____12474 =
                      let uu____12477 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12477  in
                    let uu____12478 =
                      let uu____12479 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12479  in
                    (uu____12474, uu____12478)
                | uu____12482 ->
                    let uu____12493 =
                      let uu____12499 =
                        let uu____12501 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12501
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12499)
                       in
                    FStar_Errors.raise_error uu____12493
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12521)::uu____12522 ->
                    let uu____12549 =
                      let uu____12554 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12554
                       in
                    (match uu____12549 with
                     | (us_r,uu____12586) ->
                         let uu____12587 =
                           let uu____12592 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12592
                            in
                         (match uu____12587 with
                          | (us_e,uu____12624) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12627 =
                                  let uu____12628 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12628
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12627
                                  us_r
                                 in
                              let as_ens =
                                let uu____12630 =
                                  let uu____12631 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12631
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12630
                                  us_e
                                 in
                              let req =
                                let uu____12635 =
                                  let uu____12640 =
                                    let uu____12641 =
                                      let uu____12652 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12652]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12641
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12640
                                   in
                                uu____12635 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12692 =
                                  let uu____12697 =
                                    let uu____12698 =
                                      let uu____12709 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12709]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12698
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12697
                                   in
                                uu____12692 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12746 =
                                let uu____12749 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12749  in
                              let uu____12750 =
                                let uu____12751 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12751  in
                              (uu____12746, uu____12750)))
                | uu____12754 -> failwith "Impossible"))
  
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
        (let uu____12793 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12793
         then
           let uu____12798 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12800 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12798
             uu____12800
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
          (let uu____12859 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12859
           then
             let uu____12864 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12866 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12864
               uu____12866
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12877 =
      let uu____12879 =
        let uu____12880 = FStar_Syntax_Subst.compress t  in
        uu____12880.FStar_Syntax_Syntax.n  in
      match uu____12879 with
      | FStar_Syntax_Syntax.Tm_app uu____12884 -> false
      | uu____12902 -> true  in
    if uu____12877
    then t
    else
      (let uu____12907 = FStar_Syntax_Util.head_and_args t  in
       match uu____12907 with
       | (head1,args) ->
           let uu____12950 =
             let uu____12952 =
               let uu____12953 = FStar_Syntax_Subst.compress head1  in
               uu____12953.FStar_Syntax_Syntax.n  in
             match uu____12952 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12958 -> false  in
           if uu____12950
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12990 ->
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
          ((let uu____13037 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13037
            then
              let uu____13040 = FStar_Syntax_Print.term_to_string e  in
              let uu____13042 = FStar_Syntax_Print.term_to_string t  in
              let uu____13044 =
                let uu____13046 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13046
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13040 uu____13042 uu____13044
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13082 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13082 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13116 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13194  ->
                          match uu____13194 with
                          | (uu____13202,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13209 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13209 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13116 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13328 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13328 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13342 =
                      let uu____13348 =
                        let uu____13350 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13352 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13354 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13350 uu____13352 uu____13354
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13348)
                       in
                    let uu____13358 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13342 uu____13358
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13376 =
              match uu___7_13376 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13419 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13419 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13550,uu____13537)
                           when _13550 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13583,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13585))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13619 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13619 with
                            | (v1,uu____13660,g) ->
                                ((let uu____13675 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13675
                                  then
                                    let uu____13678 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13678
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13688 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13688 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13781 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13781))))
                       | (uu____13808,(x,FStar_Pervasives_Native.Some
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
                                 let uu____13847 =
                                   let uu____13854 = FStar_Dyn.mkdyn env  in
                                   (uu____13854, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____13847
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____13860 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____13860 with
                            | (v1,uu____13901,g) ->
                                ((let uu____13916 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13916
                                  then
                                    let uu____13919 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13919
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13929 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13929 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____14022 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____14022))))
                       | (uu____14049,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14097 =
                       let uu____14124 = inst_n_binders t1  in
                       aux [] uu____14124 bs1  in
                     (match uu____14097 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14196) -> (e, torig, guard)
                           | (uu____14227,[]) when
                               let uu____14258 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14258 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14260 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14288 ->
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
            | uu____14301 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14313 =
      let uu____14317 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14317
        (FStar_List.map
           (fun u  ->
              let uu____14329 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14329 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14313 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14357 = FStar_Util.set_is_empty x  in
      if uu____14357
      then []
      else
        (let s =
           let uu____14375 =
             let uu____14378 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14378  in
           FStar_All.pipe_right uu____14375 FStar_Util.set_elements  in
         (let uu____14394 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14394
          then
            let uu____14399 =
              let uu____14401 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14401  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14399
          else ());
         (let r =
            let uu____14410 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14410  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14449 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14449
                     then
                       let uu____14454 =
                         let uu____14456 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14456
                          in
                       let uu____14460 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14462 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14454 uu____14460 uu____14462
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
        let uu____14492 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14492 FStar_Util.set_elements  in
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
        | ([],uu____14531) -> generalized_univ_names
        | (uu____14538,[]) -> explicit_univ_names
        | uu____14545 ->
            let uu____14554 =
              let uu____14560 =
                let uu____14562 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14562
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14560)
               in
            FStar_Errors.raise_error uu____14554 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14584 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14584
       then
         let uu____14589 = FStar_Syntax_Print.term_to_string t  in
         let uu____14591 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14589 uu____14591
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14600 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14600
        then
          let uu____14605 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14605
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14614 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14614
         then
           let uu____14619 = FStar_Syntax_Print.term_to_string t  in
           let uu____14621 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14619 uu____14621
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
        let uu____14705 =
          let uu____14707 =
            FStar_Util.for_all
              (fun uu____14721  ->
                 match uu____14721 with
                 | (uu____14731,uu____14732,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14707  in
        if uu____14705
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14784 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14784
              then
                let uu____14787 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14787
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14794 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14794
               then
                 let uu____14797 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14797
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14815 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14815 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14849 =
             match uu____14849 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14886 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14886
                   then
                     let uu____14891 =
                       let uu____14893 =
                         let uu____14897 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14897
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14893
                         (FStar_String.concat ", ")
                        in
                     let uu____14945 =
                       let uu____14947 =
                         let uu____14951 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14951
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14964 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14966 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14964
                                   uu____14966))
                          in
                       FStar_All.pipe_right uu____14947
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14891
                       uu____14945
                   else ());
                  (let univs2 =
                     let uu____14980 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14992 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14992) univs1
                       uu____14980
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14999 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14999
                    then
                      let uu____15004 =
                        let uu____15006 =
                          let uu____15010 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____15010
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15006
                          (FStar_String.concat ", ")
                         in
                      let uu____15058 =
                        let uu____15060 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15074 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15076 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15074
                                    uu____15076))
                           in
                        FStar_All.pipe_right uu____15060
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15004 uu____15058
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____15097 =
             let uu____15114 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15114  in
           match uu____15097 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15204 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15204
                 then ()
                 else
                   (let uu____15209 = lec_hd  in
                    match uu____15209 with
                    | (lb1,uu____15217,uu____15218) ->
                        let uu____15219 = lec2  in
                        (match uu____15219 with
                         | (lb2,uu____15227,uu____15228) ->
                             let msg =
                               let uu____15231 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15233 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15231 uu____15233
                                in
                             let uu____15236 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15236))
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
                 let uu____15304 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15304
                 then ()
                 else
                   (let uu____15309 = lec_hd  in
                    match uu____15309 with
                    | (lb1,uu____15317,uu____15318) ->
                        let uu____15319 = lec2  in
                        (match uu____15319 with
                         | (lb2,uu____15327,uu____15328) ->
                             let msg =
                               let uu____15331 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15333 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15331 uu____15333
                                in
                             let uu____15336 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15336))
                  in
               let lecs1 =
                 let uu____15347 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15400 = univs_and_uvars_of_lec this_lec  in
                        match uu____15400 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15347 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15505 = lec_hd  in
                   match uu____15505 with
                   | (lbname,e,c) ->
                       let uu____15515 =
                         let uu____15521 =
                           let uu____15523 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15525 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15527 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15523 uu____15525 uu____15527
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15521)
                          in
                       let uu____15531 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15515 uu____15531
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15550 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15550 with
                         | FStar_Pervasives_Native.Some uu____15559 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15567 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15571 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15571 with
                              | (bs,kres) ->
                                  ((let uu____15591 =
                                      let uu____15592 =
                                        let uu____15595 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15595
                                         in
                                      uu____15592.FStar_Syntax_Syntax.n  in
                                    match uu____15591 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15596
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15600 =
                                          let uu____15602 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15602  in
                                        if uu____15600
                                        then fail1 kres
                                        else ()
                                    | uu____15607 -> fail1 kres);
                                   (let a =
                                      let uu____15609 =
                                        let uu____15612 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15615  ->
                                             FStar_Pervasives_Native.Some
                                               _15615) uu____15612
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15609
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15623 ->
                                          let uu____15624 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15624
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
                      (fun uu____15727  ->
                         match uu____15727 with
                         | (lbname,e,c) ->
                             let uu____15773 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15834 ->
                                   let uu____15847 = (e, c)  in
                                   (match uu____15847 with
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
                                                (fun uu____15887  ->
                                                   match uu____15887 with
                                                   | (x,uu____15893) ->
                                                       let uu____15894 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15894)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15912 =
                                                let uu____15914 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15914
                                                 in
                                              if uu____15912
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
                                          let uu____15923 =
                                            let uu____15924 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15924.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15923 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15949 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15949 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15960 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15964 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15964, gen_tvars))
                                in
                             (match uu____15773 with
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
        (let uu____16111 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16111
         then
           let uu____16114 =
             let uu____16116 =
               FStar_List.map
                 (fun uu____16131  ->
                    match uu____16131 with
                    | (lb,uu____16140,uu____16141) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16116 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16114
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16167  ->
                match uu____16167 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16196 = gen env is_rec lecs  in
           match uu____16196 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16295  ->
                       match uu____16295 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16357 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16357
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16405  ->
                           match uu____16405 with
                           | (l,us,e,c,gvs) ->
                               let uu____16439 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16441 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16443 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16445 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16447 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16439 uu____16441 uu____16443
                                 uu____16445 uu____16447))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16492  ->
                match uu____16492 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16536 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16536, t, c, gvs)) univnames_lecs
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
        let uu____16591 =
          let uu____16595 =
            let uu____16597 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16597  in
          FStar_Pervasives_Native.Some uu____16595  in
        FStar_Profiling.profile
          (fun uu____16614  -> generalize' env is_rec lecs) uu____16591
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
              let uu____16671 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16671 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16677 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16677
                    (fun _16680  -> FStar_Pervasives_Native.Some _16680)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16689 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16689 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16695 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun _16698  -> FStar_Pervasives_Native.Some _16698)
                       uu____16695)
             in
          let uu____16699 = maybe_coerce_lc env1 e lc t2  in
          match uu____16699 with
          | (e1,lc1,g_c) ->
              let uu____16715 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16715 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16724 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16730 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16724 uu____16730
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16739 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16739
                     then
                       let uu____16744 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16744
                     else ());
                    (let uu____16750 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16750))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16778 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16778
         then
           let uu____16781 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16781
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16795 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16795 with
         | (c,g_c) ->
             let uu____16807 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16807
             then
               let uu____16815 =
                 let uu____16817 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16817  in
               (uu____16815, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16825 =
                    let uu____16826 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16826
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16825
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16827 = check_trivial_precondition env c1  in
                match uu____16827 with
                | (ct,vc,g_pre) ->
                    ((let uu____16843 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16843
                      then
                        let uu____16848 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16848
                      else ());
                     (let uu____16853 =
                        let uu____16855 =
                          let uu____16856 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16856  in
                        discharge uu____16855  in
                      let uu____16857 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16853, uu____16857)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16891 =
        match uu___8_16891 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16901)::[] -> f fst1
        | uu____16926 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16938 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16938
          (fun _16939  -> FStar_TypeChecker_Common.NonTrivial _16939)
         in
      let op_or_e e =
        let uu____16950 =
          let uu____16951 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16951  in
        FStar_All.pipe_right uu____16950
          (fun _16954  -> FStar_TypeChecker_Common.NonTrivial _16954)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16961  -> FStar_TypeChecker_Common.NonTrivial _16961)
         in
      let op_or_t t =
        let uu____16972 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16972
          (fun _16975  -> FStar_TypeChecker_Common.NonTrivial _16975)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16982  -> FStar_TypeChecker_Common.NonTrivial _16982)
         in
      let short_op_ite uu___9_16988 =
        match uu___9_16988 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16998)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17025)::[] ->
            let uu____17066 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17066
              (fun _17067  -> FStar_TypeChecker_Common.NonTrivial _17067)
        | uu____17068 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17080 =
          let uu____17088 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17088)  in
        let uu____17096 =
          let uu____17106 =
            let uu____17114 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17114)  in
          let uu____17122 =
            let uu____17132 =
              let uu____17140 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17140)  in
            let uu____17148 =
              let uu____17158 =
                let uu____17166 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17166)  in
              let uu____17174 =
                let uu____17184 =
                  let uu____17192 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17192)  in
                [uu____17184; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17158 :: uu____17174  in
            uu____17132 :: uu____17148  in
          uu____17106 :: uu____17122  in
        uu____17080 :: uu____17096  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17254 =
            FStar_Util.find_map table
              (fun uu____17269  ->
                 match uu____17269 with
                 | (x,mk1) ->
                     let uu____17286 = FStar_Ident.lid_equals x lid  in
                     if uu____17286
                     then
                       let uu____17291 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17291
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17254 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17295 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17303 =
      let uu____17304 = FStar_Syntax_Util.un_uinst l  in
      uu____17304.FStar_Syntax_Syntax.n  in
    match uu____17303 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17309 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17345)::uu____17346 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17365 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17374,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17375))::uu____17376 -> bs
      | uu____17394 ->
          let uu____17395 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17395 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17399 =
                 let uu____17400 = FStar_Syntax_Subst.compress t  in
                 uu____17400.FStar_Syntax_Syntax.n  in
               (match uu____17399 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17404) ->
                    let uu____17425 =
                      FStar_Util.prefix_until
                        (fun uu___10_17465  ->
                           match uu___10_17465 with
                           | (uu____17473,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17474)) ->
                               false
                           | uu____17479 -> true) bs'
                       in
                    (match uu____17425 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17515,uu____17516) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17588,uu____17589) ->
                         let uu____17662 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17682  ->
                                   match uu____17682 with
                                   | (x,uu____17691) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17662
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17740  ->
                                     match uu____17740 with
                                     | (x,i) ->
                                         let uu____17759 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17759, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17770 -> bs))
  
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
            let uu____17799 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17799
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
          let uu____17830 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17830
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
        (let uu____17873 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17873
         then
           ((let uu____17878 = FStar_Ident.text_of_lid lident  in
             d uu____17878);
            (let uu____17880 = FStar_Ident.text_of_lid lident  in
             let uu____17882 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17880 uu____17882))
         else ());
        (let fv =
           let uu____17888 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17888
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
         let uu____17900 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2102_17902 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2102_17902.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2102_17902.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2102_17902.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2102_17902.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2102_17902.FStar_Syntax_Syntax.sigopts)
           }), uu____17900))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17920 =
        match uu___11_17920 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17923 -> false  in
      let reducibility uu___12_17931 =
        match uu___12_17931 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17938 -> false  in
      let assumption uu___13_17946 =
        match uu___13_17946 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17950 -> false  in
      let reification uu___14_17958 =
        match uu___14_17958 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17961 -> true
        | uu____17963 -> false  in
      let inferred uu___15_17971 =
        match uu___15_17971 with
        | FStar_Syntax_Syntax.Discriminator uu____17973 -> true
        | FStar_Syntax_Syntax.Projector uu____17975 -> true
        | FStar_Syntax_Syntax.RecordType uu____17981 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17991 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18004 -> false  in
      let has_eq uu___16_18012 =
        match uu___16_18012 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18016 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18095 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18102 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18135 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18135))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18166 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18166
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18186 ->
               let uu____18195 =
                 let uu____18197 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18203  ->
                           match uu___17_18203 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18206 -> false))
                    in
                 Prims.op_Negation uu____18197  in
               if uu____18195
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18213 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18220 -> ()
           | uu____18233 ->
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
      let uu____18247 =
        let uu____18249 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18255  ->
                  match uu___18_18255 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18258 -> false))
           in
        FStar_All.pipe_right uu____18249 Prims.op_Negation  in
      if uu____18247
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18279 =
            let uu____18285 =
              let uu____18287 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18287 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18285)  in
          FStar_Errors.raise_error uu____18279 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18305 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18313 =
            let uu____18315 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18315  in
          if uu____18313 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18326),uu____18327) ->
              ((let uu____18339 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18339
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18348 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18348
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18359 ->
              ((let uu____18369 =
                  let uu____18371 =
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
                  Prims.op_Negation uu____18371  in
                if uu____18369 then err'1 () else ());
               (let uu____18381 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18387  ->
                           match uu___19_18387 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18390 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18381
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18396 ->
              let uu____18403 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18403 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18411 ->
              let uu____18418 =
                let uu____18420 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18420  in
              if uu____18418 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18430 ->
              let uu____18431 =
                let uu____18433 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18433  in
              if uu____18431 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18443 ->
              let uu____18456 =
                let uu____18458 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18458  in
              if uu____18456 then err'1 () else ()
          | uu____18468 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18507 =
          let uu____18508 = FStar_Syntax_Subst.compress t1  in
          uu____18508.FStar_Syntax_Syntax.n  in
        match uu____18507 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18512 ->
            let uu____18527 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18527 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18536;
               FStar_Syntax_Syntax.index = uu____18537;
               FStar_Syntax_Syntax.sort = t2;_},uu____18539)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18548) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18574) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18580 -> false
      
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
        (let uu____18590 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18590
         then
           let uu____18595 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18595
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
                  let uu____18660 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18660 r  in
                let uu____18670 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18670 with
                | (uu____18679,signature) ->
                    let uu____18681 =
                      let uu____18682 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18682.FStar_Syntax_Syntax.n  in
                    (match uu____18681 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18690) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18738 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18753 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18755 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18753 eff_name.FStar_Ident.str
                                       uu____18755) r
                                 in
                              (match uu____18738 with
                               | (is,g) ->
                                   let uu____18768 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18770 =
                                             let uu____18771 =
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
                                                 = uu____18771;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18770
                                            in
                                         let uu____18790 =
                                           let uu____18797 =
                                             let uu____18798 =
                                               let uu____18813 =
                                                 let uu____18822 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18822]  in
                                               (uu____18813, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18798
                                              in
                                           FStar_Syntax_Syntax.mk uu____18797
                                            in
                                         uu____18790
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18853 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18853
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18862 =
                                           let uu____18867 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18867
                                            in
                                         uu____18862
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18768, g))
                          | uu____18876 -> fail1 signature)
                     | uu____18877 -> fail1 signature)
  
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
            let uu____18908 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18908
              (fun ed  ->
                 let uu____18916 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18916 u a_tm)
  
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
              let uu____18952 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18952 with
              | (uu____18957,sig_tm) ->
                  let fail1 t =
                    let uu____18965 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18965 r  in
                  let uu____18971 =
                    let uu____18972 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18972.FStar_Syntax_Syntax.n  in
                  (match uu____18971 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18976) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18999)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19021 -> fail1 sig_tm)
                   | uu____19022 -> fail1 sig_tm)
  
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
          (let uu____19053 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19053
           then
             let uu____19058 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19060 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19058 uu____19060
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19067 =
             let uu____19078 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19079 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19078, (ct.FStar_Syntax_Syntax.result_typ), uu____19079)
              in
           match uu____19067 with
           | (u,a,c_is) ->
               let uu____19127 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19127 with
                | (uu____19136,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19147 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19149 = FStar_Ident.string_of_lid tgt  in
                      let uu____19151 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19147 uu____19149 s uu____19151
                       in
                    let uu____19154 =
                      let uu____19187 =
                        let uu____19188 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19188.FStar_Syntax_Syntax.n  in
                      match uu____19187 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19252 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19252 with
                           | (a_b::bs1,c2) ->
                               let uu____19312 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19312, c2))
                      | uu____19400 ->
                          let uu____19401 =
                            let uu____19407 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19407)
                             in
                          FStar_Errors.raise_error uu____19401 r
                       in
                    (match uu____19154 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19525 =
                           let uu____19532 =
                             let uu____19533 =
                               let uu____19534 =
                                 let uu____19541 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19541, a)  in
                               FStar_Syntax_Syntax.NT uu____19534  in
                             [uu____19533]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19532
                             (fun b  ->
                                let uu____19558 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19560 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19562 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19564 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19558 uu____19560 uu____19562
                                  uu____19564) r
                            in
                         (match uu____19525 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19578 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19578
                                then
                                  let uu____19583 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19592 =
                                             let uu____19594 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19594
                                              in
                                           Prims.op_Hat s uu____19592) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19583
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19625 =
                                           let uu____19632 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19632, t)  in
                                         FStar_Syntax_Syntax.NT uu____19625)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19651 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19651
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19657 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19657
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19666 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19666)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19668 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19668
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19672 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19672 r
                                   in
                                let fml =
                                  let uu____19677 =
                                    let uu____19682 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19683 =
                                      let uu____19684 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19684
                                       in
                                    (uu____19682, uu____19683)  in
                                  match uu____19677 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19710 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19710
                                 then
                                   let uu____19716 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19716
                                 else ());
                                (let c1 =
                                   let uu____19722 =
                                     let uu____19723 =
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
                                         uu____19723;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19722
                                    in
                                 (let uu____19747 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19747
                                  then
                                    let uu____19752 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19752
                                  else ());
                                 (let uu____19757 =
                                    let uu____19758 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19759 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19758 uu____19759
                                     in
                                  (c1, uu____19757)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19773 .
    'Auu____19773 ->
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
              let uu____19802 =
                let uu____19807 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19807
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19802 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19850 =
                let uu____19851 =
                  let uu____19854 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19854
                    FStar_Syntax_Subst.compress
                   in
                uu____19851.FStar_Syntax_Syntax.n  in
              match uu____19850 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19877::bs,uu____19879)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19919 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19919
                    FStar_Pervasives_Native.fst
              | uu____20025 ->
                  let uu____20026 =
                    let uu____20032 =
                      let uu____20034 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20034
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20032)  in
                  FStar_Errors.raise_error uu____20026
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20061 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20070 =
                let uu____20081 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20117  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20124 =
                  let uu____20135 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20135]  in
                FStar_List.append uu____20081 uu____20124  in
              uu____20061 :: uu____20070  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20206 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20206 with
        | (uu____20211,t) ->
            let err n1 =
              let uu____20221 =
                let uu____20227 =
                  let uu____20229 = FStar_Ident.string_of_lid datacon  in
                  let uu____20231 = FStar_Util.string_of_int n1  in
                  let uu____20233 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20229 uu____20231 uu____20233
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20227)
                 in
              let uu____20237 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20221 uu____20237  in
            let uu____20238 =
              let uu____20239 = FStar_Syntax_Subst.compress t  in
              uu____20239.FStar_Syntax_Syntax.n  in
            (match uu____20238 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20243) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20298  ->
                           match uu____20298 with
                           | (uu____20306,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20315 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____20347 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____20347
                      FStar_Pervasives_Native.fst)
             | uu____20358 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20371 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20371
      then
        let uu____20374 =
          let uu____20387 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20387
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20374;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20422 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20422 with
           | (uu____20431,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20450 =
                 let uu____20451 =
                   let uu___2478_20452 = ct  in
                   let uu____20453 =
                     let uu____20464 =
                       let uu____20473 =
                         let uu____20474 =
                           let uu____20481 =
                             let uu____20482 =
                               let uu____20499 =
                                 let uu____20510 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20510; wp]  in
                               (lift_t, uu____20499)  in
                             FStar_Syntax_Syntax.Tm_app uu____20482  in
                           FStar_Syntax_Syntax.mk uu____20481  in
                         uu____20474 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20473
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20464]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2478_20452.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2478_20452.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20453;
                     FStar_Syntax_Syntax.flags =
                       (uu___2478_20452.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20451  in
               (uu____20450, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20610 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20610 with
           | (uu____20617,lift_t) ->
               let uu____20619 =
                 let uu____20626 =
                   let uu____20627 =
                     let uu____20644 =
                       let uu____20655 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20664 =
                         let uu____20675 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20684 =
                           let uu____20695 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20695]  in
                         uu____20675 :: uu____20684  in
                       uu____20655 :: uu____20664  in
                     (lift_t, uu____20644)  in
                   FStar_Syntax_Syntax.Tm_app uu____20627  in
                 FStar_Syntax_Syntax.mk uu____20626  in
               uu____20619 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20748 =
           let uu____20761 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20761 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20748;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20797  ->
                        fun uu____20798  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20821 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20821
  
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
  