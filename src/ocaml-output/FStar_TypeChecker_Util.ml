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
                                                                 FStar_TypeChecker_Rel.teq
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
                                                                   FStar_TypeChecker_Rel.teq
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
                                                     (let guard =
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
                                                      (let uu____5004 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env)
                                                           (FStar_Options.Other
                                                              "ResolveImplicitsHook")
                                                          in
                                                       if uu____5004
                                                       then
                                                         let uu____5009 =
                                                           let uu____5011 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           FStar_Range.string_of_range
                                                             uu____5011
                                                            in
                                                         let uu____5012 =
                                                           FStar_TypeChecker_Rel.guard_to_string
                                                             env guard
                                                            in
                                                         FStar_Util.print2
                                                           "///////////////////////////////EndBind at %s/////////////////////\nguard = %s\n"
                                                           uu____5009
                                                           uu____5012
                                                       else ());
                                                      (c, guard)))))))))
  
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
                let uu____5061 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5087 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5087 with
                  | (a,kwp) ->
                      let uu____5118 = destruct_wp_comp ct1  in
                      let uu____5125 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5118, uu____5125)
                   in
                match uu____5061 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5178 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5178]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5198 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5198]
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
                      let uu____5245 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5254 =
                        let uu____5265 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5274 =
                          let uu____5285 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5294 =
                            let uu____5305 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5314 =
                              let uu____5325 =
                                let uu____5334 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5334  in
                              [uu____5325]  in
                            uu____5305 :: uu____5314  in
                          uu____5285 :: uu____5294  in
                        uu____5265 :: uu____5274  in
                      uu____5245 :: uu____5254  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5387 =
                        let uu____5392 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5392 wp_args  in
                      uu____5387 FStar_Pervasives_Native.None
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
              let uu____5440 =
                let uu____5445 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5446 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5445, uu____5446)  in
              match uu____5440 with
              | (ct1,ct2) ->
                  let uu____5453 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5453 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5504 = lift_comps env c1 c2 b true  in
                       (match uu____5504 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5522 =
                              let uu____5527 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5528 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5527, uu____5528)  in
                            (match uu____5522 with
                             | (ct11,ct21) ->
                                 let uu____5535 =
                                   let uu____5540 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5540
                                   then
                                     let bind_t =
                                       let uu____5548 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5548
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5551 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5551,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5535 with
                                  | (c,g_bind) ->
                                      let uu____5558 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5558)))))
  
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
            let uu____5594 =
              let uu____5595 =
                let uu____5606 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5606]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5595;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5594  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5651 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5657  ->
              match uu___1_5657 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5660 -> false))
       in
    if uu____5651
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5672  ->
              match uu___2_5672 with
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
        let uu____5700 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5700
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5711 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5711  in
           let pure_assume_wp1 =
             let uu____5716 = FStar_TypeChecker_Env.get_range env  in
             let uu____5717 =
               let uu____5722 =
                 let uu____5723 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5723]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5722  in
             uu____5717 FStar_Pervasives_Native.None uu____5716  in
           let uu____5756 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5756)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5784 =
          let uu____5785 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5785 with
          | (c,g_c) ->
              let uu____5796 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5796
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5810 = weaken_comp env c f1  in
                     (match uu____5810 with
                      | (c1,g_w) ->
                          let uu____5821 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5821)))
           in
        let uu____5822 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5822 weaken
  
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
                 let uu____5879 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5879  in
               let pure_assert_wp1 =
                 let uu____5884 =
                   let uu____5889 =
                     let uu____5890 =
                       let uu____5899 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5899
                        in
                     [uu____5890]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5889
                    in
                 uu____5884 FStar_Pervasives_Native.None r  in
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
       (let uu____5991 = FStar_Options.debug_any ()  in
        if uu____5991
        then
          let uu____5994 = FStar_Util.string_of_int n1  in
          let uu____5996 =
            let uu____5998 =
              let uu____6000 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____6000  in
            FStar_Util.string_of_int uu____5998  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____5994
            uu____5996
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
            let uu____6055 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6055
            then (lc, g0)
            else
              (let flags =
                 let uu____6067 =
                   let uu____6075 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6075
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6067 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6105 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6113  ->
                               match uu___3_6113 with
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
                               | uu____6116 -> []))
                        in
                     FStar_List.append flags uu____6105
                  in
               let strengthen uu____6126 =
                 let uu____6127 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6127 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6146 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6146 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6153 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6153
                              then
                                let uu____6157 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6159 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6157 uu____6159
                              else ());
                             (let uu____6164 =
                                strengthen_comp env reason c f flags  in
                              match uu____6164 with
                              | (c1,g_s) ->
                                  let uu____6175 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6175))))
                  in
               let uu____6176 =
                 let uu____6177 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6177
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6176,
                 (let uu___721_6179 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___721_6179.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___721_6179.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___721_6179.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6188  ->
            match uu___4_6188 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6192 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6221 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6221
          then e
          else
            (let uu____6228 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6231 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6231)
                in
             if uu____6228
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
                | uu____6301 -> false  in
              if is_unit1
              then
                let uu____6308 =
                  let uu____6310 =
                    let uu____6311 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6311
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6310
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6308
                 then
                   let uu____6320 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6320 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6364 =
                           let uu____6367 =
                             let uu____6368 =
                               let uu____6375 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6375, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6368  in
                           [uu____6367]  in
                         FStar_Syntax_Subst.subst uu____6364 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6388 = close_wp_comp env [x] c  in
                    (uu____6388, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6391 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6419  ->
            match uu____6419 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6439 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6439 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6452 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6452
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6462 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6462
                       then
                         let uu____6467 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6467
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6474 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6474
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6483 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6483
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6490 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6490
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6506 =
                  let uu____6507 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6507
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6515 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6515, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6518 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6518 with
                     | (c1,g_c1) ->
                         let uu____6529 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6529 with
                          | (c2,g_c2) ->
                              let trivial_guard1 =
                                let uu____6541 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6544 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6544
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6541
                                 in
                              (debug1
                                 (fun uu____6570  ->
                                    let uu____6571 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6573 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6578 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6571 uu____6573 uu____6578);
                               (let aux uu____6596 =
                                  let uu____6597 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6597
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6628
                                        ->
                                        let uu____6629 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6629
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6661 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6661
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6708 =
                                  let aux_with_trivial_guard uu____6738 =
                                    let uu____6739 = aux ()  in
                                    match uu____6739 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard1, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6797 =
                                    let uu____6799 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6799  in
                                  if uu____6797
                                  then
                                    let uu____6815 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6815
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard1,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6842 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6842))
                                  else
                                    (let uu____6859 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6859
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___825_6890 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___825_6890.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___825_6890.FStar_Syntax_Syntax.index);
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
                                           let uu____6921 =
                                             let uu____6926 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6926
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6921 with
                                            | (c21,g_close) ->
                                                let uu____6947 =
                                                  let uu____6955 =
                                                    let uu____6956 =
                                                      let uu____6959 =
                                                        let uu____6962 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6962; g_close]
                                                         in
                                                      g_c1 :: uu____6959  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6956
                                                     in
                                                  (c21, uu____6955, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6947)
                                       | (uu____6975,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6987 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6987 with
                                            | (c21,g_close) ->
                                                let uu____7010 =
                                                  let uu____7018 =
                                                    let uu____7019 =
                                                      let uu____7022 =
                                                        let uu____7025 =
                                                          let uu____7026 =
                                                            let uu____7027 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____7027]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____7026
                                                            g_c2
                                                           in
                                                        [uu____7025; g_close]
                                                         in
                                                      g_c1 :: uu____7022  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7019
                                                     in
                                                  (c21, uu____7018,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____7010)
                                       | (uu____7056,uu____7057) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7072 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7072
                                        then
                                          let uu____7087 =
                                            let uu____7095 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7095, trivial_guard1,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7087
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7108 = try_simplify ()  in
                                match uu____7108 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug1
                                       (fun uu____7143  ->
                                          let uu____7144 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7144);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7160  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7191 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7191 with
                                        | (c,g_bind) ->
                                            let uu____7202 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7202)
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
                                        let uu____7229 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7229 with
                                        | (m,uu____7241,lift2) ->
                                            let uu____7243 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7243 with
                                             | (c23,g2) ->
                                                 let uu____7254 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7254 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7270 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7270
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7280 =
                                                          let uu____7285 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7286 =
                                                            let uu____7287 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7296 =
                                                              let uu____7307
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7307]
                                                               in
                                                            uu____7287 ::
                                                              uu____7296
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7285
                                                            uu____7286
                                                           in
                                                        uu____7280
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7340 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7340 with
                                                       | (c,g_s) ->
                                                           let uu____7355 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7355))))
                                         in
                                      let uu____7356 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7372 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7372, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7356 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7388 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7388
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7397 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7397
                                             then
                                               (debug1
                                                  (fun uu____7411  ->
                                                     let uu____7412 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7414 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7412 uu____7414);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7421 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7421
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7426 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7429 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7429)
                                                   in
                                                if uu____7426
                                                then
                                                  let e1' =
                                                    let uu____7454 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7454
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7466  ->
                                                        let uu____7467 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7469 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7467
                                                          uu____7469);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7484  ->
                                                        let uu____7485 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7487 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7485
                                                          uu____7487);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7494 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7494
                                                       in
                                                    let uu____7495 =
                                                      let uu____7500 =
                                                        let uu____7501 =
                                                          let uu____7502 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7502]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7501
                                                         in
                                                      weaken_comp uu____7500
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7495 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7528 =
                                                            let uu____7529 =
                                                              let uu____7530
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7530]
                                                               in
                                                            let uu____7549 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7529
                                                              uu____7549
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7528
                                                           in
                                                        let uu____7550 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7550
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7561 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7561))))))
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
      | uu____7578 -> g2
  
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
            (let uu____7602 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7602)
           in
        let flags =
          if should_return1
          then
            let uu____7610 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7610
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7628 =
          let uu____7629 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7629 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7642 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7642
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7650 =
                  let uu____7652 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7652  in
                (if uu____7650
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___950_7661 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___950_7661.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___950_7661.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___950_7661.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7662 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7662, g_c)
                 else
                   (let uu____7665 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7665, g_c)))
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
                   let uu____7676 =
                     let uu____7677 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7677
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7676
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7680 =
                   let uu____7685 =
                     let uu____7686 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7686
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7685  in
                 match uu____7680 with
                 | (bind_c,g_bind) ->
                     let uu____7695 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7696 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7695, uu____7696))
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
            fun uu____7732  ->
              match uu____7732 with
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
                    let uu____7744 =
                      ((let uu____7748 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7748) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7744
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7766 =
        let uu____7767 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7767  in
      FStar_Syntax_Syntax.fvar uu____7766 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7817 =
                    let uu____7822 =
                      let uu____7823 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7823 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7822 [u_a]
                     in
                  match uu____7817 with
                  | (uu____7834,conjunction) ->
                      let uu____7836 =
                        let uu____7845 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7860 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7845, uu____7860)  in
                      (match uu____7836 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7906 =
                               let uu____7908 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7908 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7906)
                              in
                           let uu____7912 =
                             let uu____7957 =
                               let uu____7958 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7958.FStar_Syntax_Syntax.n  in
                             match uu____7957 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____8007) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____8039 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____8039 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8111 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8111 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8259 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8259)))
                             | uu____8292 ->
                                 let uu____8293 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8293 r
                              in
                           (match uu____7912 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8418 =
                                  let uu____8425 =
                                    let uu____8426 =
                                      let uu____8427 =
                                        let uu____8434 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8434, a)  in
                                      FStar_Syntax_Syntax.NT uu____8427  in
                                    [uu____8426]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8425
                                    (fun b  ->
                                       let uu____8450 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8452 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8454 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8450 uu____8452 uu____8454) r
                                   in
                                (match uu____8418 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8492 =
                                                let uu____8499 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8499, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8492) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8538 =
                                           let uu____8539 =
                                             let uu____8542 =
                                               let uu____8543 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8543.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8542
                                              in
                                           uu____8539.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8538 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8554,uu____8555::is) ->
                                             let uu____8597 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8597
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8630 ->
                                             let uu____8631 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8631 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8647 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8647)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8652 =
                                           let uu____8653 =
                                             let uu____8656 =
                                               let uu____8657 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8657.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8656
                                              in
                                           uu____8653.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8652 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8668,uu____8669::is) ->
                                             let uu____8711 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8711
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8744 ->
                                             let uu____8745 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8745 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8761 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8761)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8766 =
                                         let uu____8767 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8767.FStar_Syntax_Syntax.n  in
                                       match uu____8766 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8772,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8827 ->
                                           let uu____8828 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8828 r
                                        in
                                     let uu____8837 =
                                       let uu____8838 =
                                         let uu____8839 =
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
                                             uu____8839;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8838
                                        in
                                     let uu____8862 =
                                       let uu____8863 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8863 g_guard
                                        in
                                     (uu____8837, uu____8862))))
  
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
                fun uu____8908  ->
                  let if_then_else1 =
                    let uu____8914 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8914 FStar_Util.must  in
                  let uu____8921 = destruct_wp_comp ct1  in
                  match uu____8921 with
                  | (uu____8932,uu____8933,wp_t) ->
                      let uu____8935 = destruct_wp_comp ct2  in
                      (match uu____8935 with
                       | (uu____8946,uu____8947,wp_e) ->
                           let wp =
                             let uu____8952 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8953 =
                               let uu____8958 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8959 =
                                 let uu____8960 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8969 =
                                   let uu____8980 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8989 =
                                     let uu____9000 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____9009 =
                                       let uu____9020 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____9020]  in
                                     uu____9000 :: uu____9009  in
                                   uu____8980 :: uu____8989  in
                                 uu____8960 :: uu____8969  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8958
                                 uu____8959
                                in
                             uu____8953 FStar_Pervasives_Native.None
                               uu____8952
                              in
                           let uu____9069 = mk_comp ed u_a a wp []  in
                           (uu____9069, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____9123 =
              let uu____9124 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9124]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9123  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9171  ->
                   match uu____9171 with
                   | (uu____9185,eff_label,uu____9187,uu____9188) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9201 =
            let uu____9209 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9247  ->
                      match uu____9247 with
                      | (uu____9262,uu____9263,flags,uu____9265) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9282  ->
                                  match uu___5_9282 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9285 -> false))))
               in
            if uu____9209
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9201 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9322 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9324 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9324
                then
                  let uu____9331 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9331, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9338 =
                         let uu____9347 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9347]  in
                       let uu____9366 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9338 uu____9366  in
                     let kwp =
                       let uu____9372 =
                         let uu____9381 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9381]  in
                       let uu____9400 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9372 uu____9400  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9407 =
                         let uu____9408 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9408]  in
                       let uu____9427 =
                         let uu____9430 =
                           let uu____9437 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9437
                            in
                         let uu____9438 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9430 uu____9438  in
                       FStar_Syntax_Util.abs uu____9407 uu____9427
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
                     let uu____9462 =
                       should_not_inline_whole_match ||
                         (let uu____9465 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9465)
                        in
                     if uu____9462 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9477 =
                       let uu____9490 =
                         let uu____9495 =
                           let uu____9506 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9550  ->
                                     match uu____9550 with
                                     | (g,uu____9565,uu____9566,uu____9567)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9506
                             (FStar_List.fold_left
                                (fun uu____9611  ->
                                   fun g  ->
                                     match uu____9611 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9652 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9652
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9495
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9490
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9477
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9753 =
                     FStar_List.fold_right2
                       (fun uu____9816  ->
                          fun bcond  ->
                            fun uu____9818  ->
                              match (uu____9816, uu____9818) with
                              | ((g,eff_label,uu____9878,cthen),(uu____9880,celse,g_comp))
                                  ->
                                  let uu____9927 =
                                    let uu____9932 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9932
                                     in
                                  (match uu____9927 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9944 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9944
                                          in
                                       let uu____9945 =
                                         let uu____9956 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             false
                                            in
                                         match uu____9956 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9984 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9985 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9984, uu____9985,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9945 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____10036 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____10036
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____10071 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____10071
                                               in
                                            let g_lift_else1 =
                                              let uu____10073 =
                                                let uu____10074 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____10074
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____10073
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____10078 =
                                              let uu____10083 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____10083
                                               in
                                            (match uu____10078 with
                                             | (c,g_conjunction) ->
                                                 let uu____10094 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____10094)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9753 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____10111 =
                           let uu____10112 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____10112]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____10111
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____10155::[] -> (comp, g_comp1)
                        | uu____10198 ->
                            let uu____10215 =
                              let uu____10217 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10217
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10215
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
                               let uu____10230 = destruct_wp_comp comp1  in
                               match uu____10230 with
                               | (uu____10241,uu____10242,wp) ->
                                   let ite_wp =
                                     let uu____10245 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10245
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10255 =
                                       let uu____10260 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10261 =
                                         let uu____10262 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10271 =
                                           let uu____10282 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10282]  in
                                         uu____10262 :: uu____10271  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10260 uu____10261
                                        in
                                     uu____10255 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10315 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10315, g_comp1))))
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
          let uu____10350 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10350 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10366 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10372 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10366 uu____10372
              else
                (let uu____10381 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10387 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10381 uu____10387)
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
          let uu____10412 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10412
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10415 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10415
        then u_res
        else
          (let is_total =
             let uu____10422 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10422
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10433 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10433 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10436 =
                    let uu____10442 =
                      let uu____10444 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10444
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10442)
                     in
                  FStar_Errors.raise_error uu____10436
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
      let uu____10468 = destruct_wp_comp ct  in
      match uu____10468 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10487 = FStar_TypeChecker_Env.get_range env  in
            let uu____10488 =
              let uu____10493 =
                let uu____10494 =
                  let uu____10495 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10495 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10494
                 in
              let uu____10502 =
                let uu____10503 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10512 =
                  let uu____10523 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10523]  in
                uu____10503 :: uu____10512  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10493 uu____10502  in
            uu____10488 FStar_Pervasives_Native.None uu____10487  in
          let uu____10556 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10556)
  
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
                  let uu____10611 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10611 with
                  | FStar_Pervasives_Native.Some uu____10626 ->
                      ((let uu____10644 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10644
                        then
                          let uu____10648 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10648
                        else ());
                       (let coercion =
                          let uu____10654 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10654
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10661 =
                            let uu____10662 =
                              let uu____10663 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10663
                               in
                            (FStar_Pervasives_Native.None, uu____10662)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10661
                           in
                        let e1 =
                          let uu____10669 =
                            let uu____10674 =
                              let uu____10675 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10675]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10674
                             in
                          uu____10669 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10709 =
                          let uu____10715 =
                            let uu____10717 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10717
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10715)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10709);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10736 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10754 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10765 -> false 
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
      let uu____10789 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10789 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10834 =
              let uu____10849 =
                let uu____10850 = FStar_Syntax_Subst.compress h1  in
                uu____10850.FStar_Syntax_Syntax.n  in
              (uu____10849, args)  in
            match uu____10834 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10897,uu____10898) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10931) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10952,branches),uu____10954) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11018 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11019 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11019 with
                               | (uu____11020,uu____11021,br_body) ->
                                   let uu____11039 =
                                     let uu____11040 =
                                       let uu____11045 =
                                         let uu____11046 =
                                           let uu____11049 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11049
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11046
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11045  in
                                     FStar_All.pipe_right br_body uu____11040
                                      in
                                   (match uu____11039 with
                                    | No  -> No
                                    | uu____11060 -> Maybe))) No)
            | uu____11061 -> No  in
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
            (((let uu____11113 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11113) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11132 =
                 let uu____11133 = FStar_Syntax_Subst.compress t1  in
                 uu____11133.FStar_Syntax_Syntax.n  in
               match uu____11132 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11138 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11148 =
                 let uu____11149 = FStar_Syntax_Subst.compress t1  in
                 uu____11149.FStar_Syntax_Syntax.n  in
               match uu____11148 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11154 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11165 =
                 let uu____11166 = FStar_Syntax_Subst.compress t2  in
                 uu____11166.FStar_Syntax_Syntax.n  in
               match uu____11165 with
               | FStar_Syntax_Syntax.Tm_type uu____11170 -> true
               | uu____11172 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11175 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11175 with
             | (head1,args) ->
                 ((let uu____11225 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11225
                   then
                     let uu____11229 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11231 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11233 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11235 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11229 uu____11231 uu____11233 uu____11235
                   else ());
                  (let mk_erased u t =
                     let uu____11253 =
                       let uu____11256 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11256 [u]  in
                     let uu____11257 =
                       let uu____11268 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11268]  in
                     FStar_Syntax_Util.mk_app uu____11253 uu____11257  in
                   let uu____11293 =
                     let uu____11308 =
                       let uu____11309 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11309.FStar_Syntax_Syntax.n  in
                     (uu____11308, args)  in
                   match uu____11293 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11347 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11347 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11387 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11387 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11427 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11427 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11467 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11467 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11488 ->
                       let uu____11503 =
                         let uu____11508 = check_erased env res_typ  in
                         let uu____11509 = check_erased env exp_t  in
                         (uu____11508, uu____11509)  in
                       (match uu____11503 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11518 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11518 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11529 =
                                   let uu____11534 =
                                     let uu____11535 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11535]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11534
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11529 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11570 =
                              let uu____11575 =
                                let uu____11576 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11576]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11575
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11570 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11609 ->
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
        let uu____11644 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11644 with
        | (hd1,args) ->
            let uu____11693 =
              let uu____11708 =
                let uu____11709 = FStar_Syntax_Subst.compress hd1  in
                uu____11709.FStar_Syntax_Syntax.n  in
              (uu____11708, args)  in
            (match uu____11693 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11747 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11774  -> FStar_Pervasives_Native.Some _11774)
                   uu____11747
             | uu____11775 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11828 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11828
           then
             let uu____11831 = FStar_Syntax_Print.term_to_string e  in
             let uu____11833 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11835 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11831 uu____11833 uu____11835
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11845 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11845 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11870 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11896 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11896, false)
             else
               (let uu____11906 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11906, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11919) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11931 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11931
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1392_11947 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1392_11947.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1392_11947.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1392_11947.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11954 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11954 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11970 =
                      let uu____11971 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11971 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11991 =
                            let uu____11993 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11993 = FStar_Syntax_Util.Equal  in
                          if uu____11991
                          then
                            ((let uu____12000 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12000
                              then
                                let uu____12004 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12006 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12004 uu____12006
                              else ());
                             (let uu____12011 = set_result_typ1 c  in
                              (uu____12011, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12018 ->
                                   true
                               | uu____12026 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12035 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12035
                                  in
                               let lc1 =
                                 let uu____12037 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12038 =
                                   let uu____12039 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12039)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12037 uu____12038
                                  in
                               ((let uu____12043 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12043
                                 then
                                   let uu____12047 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12049 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12051 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12053 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12047 uu____12049 uu____12051
                                     uu____12053
                                 else ());
                                (let uu____12058 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12058 with
                                 | (c1,g_lc) ->
                                     let uu____12069 = set_result_typ1 c1  in
                                     let uu____12070 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12069, uu____12070)))
                             else
                               ((let uu____12074 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12074
                                 then
                                   let uu____12078 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12080 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12078 uu____12080
                                 else ());
                                (let uu____12085 = set_result_typ1 c  in
                                 (uu____12085, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1429_12089 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1429_12089.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1429_12089.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1429_12089.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12099 =
                      let uu____12100 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12100
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12110 =
                           let uu____12111 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12111.FStar_Syntax_Syntax.n  in
                         match uu____12110 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12118,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12120;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12121;_},uu____12122)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1445_12148 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1445_12148.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1445_12148.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1445_12148.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12149 ->
                             let uu____12150 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12150 with
                              | (c,g_c) ->
                                  ((let uu____12162 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12162
                                    then
                                      let uu____12166 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12168 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12170 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12172 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12166 uu____12168 uu____12170
                                        uu____12172
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
                                        let uu____12185 =
                                          let uu____12190 =
                                            let uu____12191 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12191]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12190
                                           in
                                        uu____12185
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12218 =
                                      let uu____12223 =
                                        FStar_All.pipe_left
                                          (fun _12244  ->
                                             FStar_Pervasives_Native.Some
                                               _12244)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12245 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12246 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12247 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12223
                                        uu____12245 e uu____12246 uu____12247
                                       in
                                    match uu____12218 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1463_12255 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1463_12255.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1463_12255.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12257 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12257
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12260 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12260 with
                                         | (c2,g_lc) ->
                                             ((let uu____12272 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12272
                                               then
                                                 let uu____12276 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12276
                                               else ());
                                              (let uu____12281 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12281))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12290  ->
                              match uu___6_12290 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12293 -> []))
                       in
                    let lc1 =
                      let uu____12295 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12295 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1479_12297 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1479_12297.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1479_12297.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1479_12297.FStar_TypeChecker_Common.implicits)
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
        let uu____12333 =
          let uu____12336 =
            let uu____12341 =
              let uu____12342 =
                let uu____12351 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12351  in
              [uu____12342]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12341  in
          uu____12336 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12333  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12374 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12374
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12393 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12409 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12426 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12426
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12442)::(ens,uu____12444)::uu____12445 ->
                    let uu____12488 =
                      let uu____12491 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12491  in
                    let uu____12492 =
                      let uu____12493 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12493  in
                    (uu____12488, uu____12492)
                | uu____12496 ->
                    let uu____12507 =
                      let uu____12513 =
                        let uu____12515 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12515
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12513)
                       in
                    FStar_Errors.raise_error uu____12507
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12535)::uu____12536 ->
                    let uu____12563 =
                      let uu____12568 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12568
                       in
                    (match uu____12563 with
                     | (us_r,uu____12600) ->
                         let uu____12601 =
                           let uu____12606 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12606
                            in
                         (match uu____12601 with
                          | (us_e,uu____12638) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12641 =
                                  let uu____12642 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12642
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12641
                                  us_r
                                 in
                              let as_ens =
                                let uu____12644 =
                                  let uu____12645 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12645
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12644
                                  us_e
                                 in
                              let req =
                                let uu____12649 =
                                  let uu____12654 =
                                    let uu____12655 =
                                      let uu____12666 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12666]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12655
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12654
                                   in
                                uu____12649 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12706 =
                                  let uu____12711 =
                                    let uu____12712 =
                                      let uu____12723 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12723]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12712
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12711
                                   in
                                uu____12706 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12760 =
                                let uu____12763 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12763  in
                              let uu____12764 =
                                let uu____12765 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12765  in
                              (uu____12760, uu____12764)))
                | uu____12768 -> failwith "Impossible"))
  
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
        (let uu____12807 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12807
         then
           let uu____12812 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12814 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12812
             uu____12814
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
          (let uu____12873 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12873
           then
             let uu____12878 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12880 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12878
               uu____12880
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12891 =
      let uu____12893 =
        let uu____12894 = FStar_Syntax_Subst.compress t  in
        uu____12894.FStar_Syntax_Syntax.n  in
      match uu____12893 with
      | FStar_Syntax_Syntax.Tm_app uu____12898 -> false
      | uu____12916 -> true  in
    if uu____12891
    then t
    else
      (let uu____12921 = FStar_Syntax_Util.head_and_args t  in
       match uu____12921 with
       | (head1,args) ->
           let uu____12964 =
             let uu____12966 =
               let uu____12967 = FStar_Syntax_Subst.compress head1  in
               uu____12967.FStar_Syntax_Syntax.n  in
             match uu____12966 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12972 -> false  in
           if uu____12964
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13004 ->
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
          ((let uu____13051 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13051
            then
              let uu____13054 = FStar_Syntax_Print.term_to_string e  in
              let uu____13056 = FStar_Syntax_Print.term_to_string t  in
              let uu____13058 =
                let uu____13060 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13060
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13054 uu____13056 uu____13058
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13096 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13096 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13130 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13208  ->
                          match uu____13208 with
                          | (uu____13216,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13223 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13223 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13130 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13342 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13342 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13356 =
                      let uu____13362 =
                        let uu____13364 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13366 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13368 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13364 uu____13366 uu____13368
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13362)
                       in
                    let uu____13372 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13356 uu____13372
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13390 =
              match uu___7_13390 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13433 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13433 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13564,uu____13551)
                           when _13564 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13597,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13599))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13633 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13633 with
                            | (v1,uu____13674,g) ->
                                ((let uu____13689 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13689
                                  then
                                    let uu____13692 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13692
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13702 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13702 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13795 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13795))))
                       | (uu____13822,(x,FStar_Pervasives_Native.Some
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
                                 let uu____13861 =
                                   let uu____13868 = FStar_Dyn.mkdyn env  in
                                   (uu____13868, tau)  in
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   uu____13861
                             | FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                                 attr ->
                                 FStar_Syntax_Syntax.Ctx_uvar_meta_attr attr
                              in
                           let uu____13874 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict
                               (FStar_Pervasives_Native.Some meta_t)
                              in
                           (match uu____13874 with
                            | (v1,uu____13915,g) ->
                                ((let uu____13930 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13930
                                  then
                                    let uu____13933 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13933
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13943 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13943 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____14036 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____14036))))
                       | (uu____14063,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14111 =
                       let uu____14138 = inst_n_binders t1  in
                       aux [] uu____14138 bs1  in
                     (match uu____14111 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14210) -> (e, torig, guard)
                           | (uu____14241,[]) when
                               let uu____14272 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14272 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14274 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14302 ->
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
            | uu____14315 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14327 =
      let uu____14331 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14331
        (FStar_List.map
           (fun u  ->
              let uu____14343 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14343 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14327 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14371 = FStar_Util.set_is_empty x  in
      if uu____14371
      then []
      else
        (let s =
           let uu____14389 =
             let uu____14392 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14392  in
           FStar_All.pipe_right uu____14389 FStar_Util.set_elements  in
         (let uu____14408 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14408
          then
            let uu____14413 =
              let uu____14415 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14415  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14413
          else ());
         (let r =
            let uu____14424 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14424  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14463 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14463
                     then
                       let uu____14468 =
                         let uu____14470 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14470
                          in
                       let uu____14474 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14476 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14468 uu____14474 uu____14476
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
        let uu____14506 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14506 FStar_Util.set_elements  in
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
        | ([],uu____14545) -> generalized_univ_names
        | (uu____14552,[]) -> explicit_univ_names
        | uu____14559 ->
            let uu____14568 =
              let uu____14574 =
                let uu____14576 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14576
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14574)
               in
            FStar_Errors.raise_error uu____14568 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14598 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14598
       then
         let uu____14603 = FStar_Syntax_Print.term_to_string t  in
         let uu____14605 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14603 uu____14605
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14614 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14614
        then
          let uu____14619 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14619
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14628 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14628
         then
           let uu____14633 = FStar_Syntax_Print.term_to_string t  in
           let uu____14635 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14633 uu____14635
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
        let uu____14719 =
          let uu____14721 =
            FStar_Util.for_all
              (fun uu____14735  ->
                 match uu____14735 with
                 | (uu____14745,uu____14746,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14721  in
        if uu____14719
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14798 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14798
              then
                let uu____14801 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14801
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14808 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14808
               then
                 let uu____14811 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14811
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14829 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14829 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14863 =
             match uu____14863 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14900 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14900
                   then
                     let uu____14905 =
                       let uu____14907 =
                         let uu____14911 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14911
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14907
                         (FStar_String.concat ", ")
                        in
                     let uu____14959 =
                       let uu____14961 =
                         let uu____14965 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14965
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14978 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14980 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14978
                                   uu____14980))
                          in
                       FStar_All.pipe_right uu____14961
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14905
                       uu____14959
                   else ());
                  (let univs2 =
                     let uu____14994 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____15006 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____15006) univs1
                       uu____14994
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15013 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15013
                    then
                      let uu____15018 =
                        let uu____15020 =
                          let uu____15024 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____15024
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15020
                          (FStar_String.concat ", ")
                         in
                      let uu____15072 =
                        let uu____15074 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15088 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15090 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15088
                                    uu____15090))
                           in
                        FStar_All.pipe_right uu____15074
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15018 uu____15072
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____15111 =
             let uu____15128 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15128  in
           match uu____15111 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15218 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15218
                 then ()
                 else
                   (let uu____15223 = lec_hd  in
                    match uu____15223 with
                    | (lb1,uu____15231,uu____15232) ->
                        let uu____15233 = lec2  in
                        (match uu____15233 with
                         | (lb2,uu____15241,uu____15242) ->
                             let msg =
                               let uu____15245 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15247 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15245 uu____15247
                                in
                             let uu____15250 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15250))
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
                 let uu____15318 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15318
                 then ()
                 else
                   (let uu____15323 = lec_hd  in
                    match uu____15323 with
                    | (lb1,uu____15331,uu____15332) ->
                        let uu____15333 = lec2  in
                        (match uu____15333 with
                         | (lb2,uu____15341,uu____15342) ->
                             let msg =
                               let uu____15345 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15347 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15345 uu____15347
                                in
                             let uu____15350 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15350))
                  in
               let lecs1 =
                 let uu____15361 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15414 = univs_and_uvars_of_lec this_lec  in
                        match uu____15414 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15361 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15519 = lec_hd  in
                   match uu____15519 with
                   | (lbname,e,c) ->
                       let uu____15529 =
                         let uu____15535 =
                           let uu____15537 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15539 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15541 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15537 uu____15539 uu____15541
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15535)
                          in
                       let uu____15545 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15529 uu____15545
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15564 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15564 with
                         | FStar_Pervasives_Native.Some uu____15573 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15581 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15585 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15585 with
                              | (bs,kres) ->
                                  ((let uu____15605 =
                                      let uu____15606 =
                                        let uu____15609 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15609
                                         in
                                      uu____15606.FStar_Syntax_Syntax.n  in
                                    match uu____15605 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15610
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15614 =
                                          let uu____15616 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15616  in
                                        if uu____15614
                                        then fail1 kres
                                        else ()
                                    | uu____15621 -> fail1 kres);
                                   (let a =
                                      let uu____15623 =
                                        let uu____15626 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15629  ->
                                             FStar_Pervasives_Native.Some
                                               _15629) uu____15626
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15623
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15637 ->
                                          let uu____15638 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15638
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
                      (fun uu____15741  ->
                         match uu____15741 with
                         | (lbname,e,c) ->
                             let uu____15787 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15848 ->
                                   let uu____15861 = (e, c)  in
                                   (match uu____15861 with
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
                                                (fun uu____15901  ->
                                                   match uu____15901 with
                                                   | (x,uu____15907) ->
                                                       let uu____15908 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15908)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15926 =
                                                let uu____15928 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15928
                                                 in
                                              if uu____15926
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
                                          let uu____15937 =
                                            let uu____15938 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15938.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15937 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15963 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15963 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15974 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15978 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15978, gen_tvars))
                                in
                             (match uu____15787 with
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
        (let uu____16125 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16125
         then
           let uu____16128 =
             let uu____16130 =
               FStar_List.map
                 (fun uu____16145  ->
                    match uu____16145 with
                    | (lb,uu____16154,uu____16155) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16130 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16128
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16181  ->
                match uu____16181 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16210 = gen env is_rec lecs  in
           match uu____16210 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16309  ->
                       match uu____16309 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16371 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16371
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16419  ->
                           match uu____16419 with
                           | (l,us,e,c,gvs) ->
                               let uu____16453 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16455 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16457 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16459 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16461 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16453 uu____16455 uu____16457
                                 uu____16459 uu____16461))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16506  ->
                match uu____16506 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16550 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16550, t, c, gvs)) univnames_lecs
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
        let uu____16605 =
          let uu____16609 =
            let uu____16611 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16611  in
          FStar_Pervasives_Native.Some uu____16609  in
        FStar_Profiling.profile
          (fun uu____16628  -> generalize' env is_rec lecs) uu____16605
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
              let uu____16685 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16685 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16691 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16691
                    (fun _16694  -> FStar_Pervasives_Native.Some _16694)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16703 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16703 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16709 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun _16712  -> FStar_Pervasives_Native.Some _16712)
                       uu____16709)
             in
          let uu____16713 = maybe_coerce_lc env1 e lc t2  in
          match uu____16713 with
          | (e1,lc1,g_c) ->
              let uu____16729 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16729 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16738 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16744 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16738 uu____16744
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16753 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16753
                     then
                       let uu____16758 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16758
                     else ());
                    (let uu____16764 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16764))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16792 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16792
         then
           let uu____16795 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16795
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16809 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16809 with
         | (c,g_c) ->
             let uu____16821 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16821
             then
               let uu____16829 =
                 let uu____16831 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16831  in
               (uu____16829, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16839 =
                    let uu____16840 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16840
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16839
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16841 = check_trivial_precondition env c1  in
                match uu____16841 with
                | (ct,vc,g_pre) ->
                    ((let uu____16857 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16857
                      then
                        let uu____16862 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16862
                      else ());
                     (let uu____16867 =
                        let uu____16869 =
                          let uu____16870 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16870  in
                        discharge uu____16869  in
                      let uu____16871 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16867, uu____16871)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16905 =
        match uu___8_16905 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16915)::[] -> f fst1
        | uu____16940 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16952 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16952
          (fun _16953  -> FStar_TypeChecker_Common.NonTrivial _16953)
         in
      let op_or_e e =
        let uu____16964 =
          let uu____16965 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16965  in
        FStar_All.pipe_right uu____16964
          (fun _16968  -> FStar_TypeChecker_Common.NonTrivial _16968)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16975  -> FStar_TypeChecker_Common.NonTrivial _16975)
         in
      let op_or_t t =
        let uu____16986 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16986
          (fun _16989  -> FStar_TypeChecker_Common.NonTrivial _16989)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16996  -> FStar_TypeChecker_Common.NonTrivial _16996)
         in
      let short_op_ite uu___9_17002 =
        match uu___9_17002 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17012)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17039)::[] ->
            let uu____17080 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17080
              (fun _17081  -> FStar_TypeChecker_Common.NonTrivial _17081)
        | uu____17082 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17094 =
          let uu____17102 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17102)  in
        let uu____17110 =
          let uu____17120 =
            let uu____17128 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17128)  in
          let uu____17136 =
            let uu____17146 =
              let uu____17154 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17154)  in
            let uu____17162 =
              let uu____17172 =
                let uu____17180 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17180)  in
              let uu____17188 =
                let uu____17198 =
                  let uu____17206 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17206)  in
                [uu____17198; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17172 :: uu____17188  in
            uu____17146 :: uu____17162  in
          uu____17120 :: uu____17136  in
        uu____17094 :: uu____17110  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17268 =
            FStar_Util.find_map table
              (fun uu____17283  ->
                 match uu____17283 with
                 | (x,mk1) ->
                     let uu____17300 = FStar_Ident.lid_equals x lid  in
                     if uu____17300
                     then
                       let uu____17305 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17305
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17268 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17309 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17317 =
      let uu____17318 = FStar_Syntax_Util.un_uinst l  in
      uu____17318.FStar_Syntax_Syntax.n  in
    match uu____17317 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17323 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17359)::uu____17360 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17379 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17388,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17389))::uu____17390 -> bs
      | uu____17408 ->
          let uu____17409 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17409 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17413 =
                 let uu____17414 = FStar_Syntax_Subst.compress t  in
                 uu____17414.FStar_Syntax_Syntax.n  in
               (match uu____17413 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17418) ->
                    let uu____17439 =
                      FStar_Util.prefix_until
                        (fun uu___10_17479  ->
                           match uu___10_17479 with
                           | (uu____17487,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17488)) ->
                               false
                           | uu____17493 -> true) bs'
                       in
                    (match uu____17439 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17529,uu____17530) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17602,uu____17603) ->
                         let uu____17676 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17696  ->
                                   match uu____17696 with
                                   | (x,uu____17705) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17676
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17754  ->
                                     match uu____17754 with
                                     | (x,i) ->
                                         let uu____17773 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17773, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17784 -> bs))
  
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
            let uu____17813 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17813
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
          let uu____17844 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17844
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
        (let uu____17887 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17887
         then
           ((let uu____17892 = FStar_Ident.text_of_lid lident  in
             d uu____17892);
            (let uu____17894 = FStar_Ident.text_of_lid lident  in
             let uu____17896 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17894 uu____17896))
         else ());
        (let fv =
           let uu____17902 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17902
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
         let uu____17914 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2105_17916 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2105_17916.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2105_17916.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2105_17916.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2105_17916.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2105_17916.FStar_Syntax_Syntax.sigopts)
           }), uu____17914))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17934 =
        match uu___11_17934 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17937 -> false  in
      let reducibility uu___12_17945 =
        match uu___12_17945 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17952 -> false  in
      let assumption uu___13_17960 =
        match uu___13_17960 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17964 -> false  in
      let reification uu___14_17972 =
        match uu___14_17972 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17975 -> true
        | uu____17977 -> false  in
      let inferred uu___15_17985 =
        match uu___15_17985 with
        | FStar_Syntax_Syntax.Discriminator uu____17987 -> true
        | FStar_Syntax_Syntax.Projector uu____17989 -> true
        | FStar_Syntax_Syntax.RecordType uu____17995 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18005 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18018 -> false  in
      let has_eq uu___16_18026 =
        match uu___16_18026 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18030 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18109 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18116 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18149 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18149))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18180 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18180
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18200 ->
               let uu____18209 =
                 let uu____18211 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18217  ->
                           match uu___17_18217 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18220 -> false))
                    in
                 Prims.op_Negation uu____18211  in
               if uu____18209
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18227 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18234 -> ()
           | uu____18247 ->
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
      let uu____18261 =
        let uu____18263 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18269  ->
                  match uu___18_18269 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18272 -> false))
           in
        FStar_All.pipe_right uu____18263 Prims.op_Negation  in
      if uu____18261
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18293 =
            let uu____18299 =
              let uu____18301 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18301 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18299)  in
          FStar_Errors.raise_error uu____18293 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18319 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18327 =
            let uu____18329 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18329  in
          if uu____18327 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18340),uu____18341) ->
              ((let uu____18353 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18353
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18362 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18362
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18373 ->
              ((let uu____18383 =
                  let uu____18385 =
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
                  Prims.op_Negation uu____18385  in
                if uu____18383 then err'1 () else ());
               (let uu____18395 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18401  ->
                           match uu___19_18401 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18404 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18395
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18410 ->
              let uu____18417 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18417 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18425 ->
              let uu____18432 =
                let uu____18434 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18434  in
              if uu____18432 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18444 ->
              let uu____18445 =
                let uu____18447 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18447  in
              if uu____18445 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18457 ->
              let uu____18470 =
                let uu____18472 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18472  in
              if uu____18470 then err'1 () else ()
          | uu____18482 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18521 =
          let uu____18522 = FStar_Syntax_Subst.compress t1  in
          uu____18522.FStar_Syntax_Syntax.n  in
        match uu____18521 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18526 ->
            let uu____18541 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18541 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18550;
               FStar_Syntax_Syntax.index = uu____18551;
               FStar_Syntax_Syntax.sort = t2;_},uu____18553)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18562) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18588) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18594 -> false
      
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
        (let uu____18604 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18604
         then
           let uu____18609 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18609
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
                  let uu____18674 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18674 r  in
                let uu____18684 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18684 with
                | (uu____18693,signature) ->
                    let uu____18695 =
                      let uu____18696 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18696.FStar_Syntax_Syntax.n  in
                    (match uu____18695 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18704) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18752 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18767 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18769 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18767 eff_name.FStar_Ident.str
                                       uu____18769) r
                                 in
                              (match uu____18752 with
                               | (is,g) ->
                                   let uu____18782 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18784 =
                                             let uu____18785 =
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
                                                 = uu____18785;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18784
                                            in
                                         let uu____18804 =
                                           let uu____18811 =
                                             let uu____18812 =
                                               let uu____18827 =
                                                 let uu____18836 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18836]  in
                                               (uu____18827, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18812
                                              in
                                           FStar_Syntax_Syntax.mk uu____18811
                                            in
                                         uu____18804
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18867 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18867
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18876 =
                                           let uu____18881 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18881
                                            in
                                         uu____18876
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18782, g))
                          | uu____18890 -> fail1 signature)
                     | uu____18891 -> fail1 signature)
  
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
            let uu____18922 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18922
              (fun ed  ->
                 let uu____18930 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18930 u a_tm)
  
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
              let uu____18966 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18966 with
              | (uu____18971,sig_tm) ->
                  let fail1 t =
                    let uu____18979 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18979 r  in
                  let uu____18985 =
                    let uu____18986 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18986.FStar_Syntax_Syntax.n  in
                  (match uu____18985 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18990) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19013)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19035 -> fail1 sig_tm)
                   | uu____19036 -> fail1 sig_tm)
  
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
          (let uu____19067 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19067
           then
             let uu____19072 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19074 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19072 uu____19074
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19081 =
             let uu____19092 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19093 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19092, (ct.FStar_Syntax_Syntax.result_typ), uu____19093)
              in
           match uu____19081 with
           | (u,a,c_is) ->
               let uu____19141 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19141 with
                | (uu____19150,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19161 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19163 = FStar_Ident.string_of_lid tgt  in
                      let uu____19165 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19161 uu____19163 s uu____19165
                       in
                    let uu____19168 =
                      let uu____19201 =
                        let uu____19202 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19202.FStar_Syntax_Syntax.n  in
                      match uu____19201 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19266 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19266 with
                           | (a_b::bs1,c2) ->
                               let uu____19326 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19326, c2))
                      | uu____19414 ->
                          let uu____19415 =
                            let uu____19421 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19421)
                             in
                          FStar_Errors.raise_error uu____19415 r
                       in
                    (match uu____19168 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19539 =
                           let uu____19546 =
                             let uu____19547 =
                               let uu____19548 =
                                 let uu____19555 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19555, a)  in
                               FStar_Syntax_Syntax.NT uu____19548  in
                             [uu____19547]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19546
                             (fun b  ->
                                let uu____19572 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19574 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19576 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19578 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19572 uu____19574 uu____19576
                                  uu____19578) r
                            in
                         (match uu____19539 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19592 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19592
                                then
                                  let uu____19597 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19606 =
                                             let uu____19608 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19608
                                              in
                                           Prims.op_Hat s uu____19606) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19597
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19639 =
                                           let uu____19646 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19646, t)  in
                                         FStar_Syntax_Syntax.NT uu____19639)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19665 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19665
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19671 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19671
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19680 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19680)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19682 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19682
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19686 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19686 r
                                   in
                                let fml =
                                  let uu____19691 =
                                    let uu____19696 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19697 =
                                      let uu____19698 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19698
                                       in
                                    (uu____19696, uu____19697)  in
                                  match uu____19691 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19724 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19724
                                 then
                                   let uu____19730 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19730
                                 else ());
                                (let c1 =
                                   let uu____19736 =
                                     let uu____19737 =
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
                                         uu____19737;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19736
                                    in
                                 (let uu____19761 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19761
                                  then
                                    let uu____19766 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19766
                                  else ());
                                 (let uu____19771 =
                                    let uu____19772 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19773 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19772 uu____19773
                                     in
                                  (c1, uu____19771)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19787 .
    'Auu____19787 ->
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
              let uu____19816 =
                let uu____19821 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19821
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19816 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19864 =
                let uu____19865 =
                  let uu____19868 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19868
                    FStar_Syntax_Subst.compress
                   in
                uu____19865.FStar_Syntax_Syntax.n  in
              match uu____19864 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19891::bs,uu____19893)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19933 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19933
                    FStar_Pervasives_Native.fst
              | uu____20039 ->
                  let uu____20040 =
                    let uu____20046 =
                      let uu____20048 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20048
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20046)  in
                  FStar_Errors.raise_error uu____20040
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20075 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20084 =
                let uu____20095 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20131  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20138 =
                  let uu____20149 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20149]  in
                FStar_List.append uu____20095 uu____20138  in
              uu____20075 :: uu____20084  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20220 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20220 with
        | (uu____20225,t) ->
            let err n1 =
              let uu____20235 =
                let uu____20241 =
                  let uu____20243 = FStar_Ident.string_of_lid datacon  in
                  let uu____20245 = FStar_Util.string_of_int n1  in
                  let uu____20247 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20243 uu____20245 uu____20247
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20241)
                 in
              let uu____20251 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20235 uu____20251  in
            let uu____20252 =
              let uu____20253 = FStar_Syntax_Subst.compress t  in
              uu____20253.FStar_Syntax_Syntax.n  in
            (match uu____20252 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20257) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20312  ->
                           match uu____20312 with
                           | (uu____20320,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20329 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____20361 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____20361
                      FStar_Pervasives_Native.fst)
             | uu____20372 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20385 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20385
      then
        let uu____20388 =
          let uu____20401 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20401
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20388;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20436 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20436 with
           | (uu____20445,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20464 =
                 let uu____20465 =
                   let uu___2481_20466 = ct  in
                   let uu____20467 =
                     let uu____20478 =
                       let uu____20487 =
                         let uu____20488 =
                           let uu____20495 =
                             let uu____20496 =
                               let uu____20513 =
                                 let uu____20524 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20524; wp]  in
                               (lift_t, uu____20513)  in
                             FStar_Syntax_Syntax.Tm_app uu____20496  in
                           FStar_Syntax_Syntax.mk uu____20495  in
                         uu____20488 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20487
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20478]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2481_20466.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2481_20466.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20467;
                     FStar_Syntax_Syntax.flags =
                       (uu___2481_20466.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20465  in
               (uu____20464, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20624 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20624 with
           | (uu____20631,lift_t) ->
               let uu____20633 =
                 let uu____20640 =
                   let uu____20641 =
                     let uu____20658 =
                       let uu____20669 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20678 =
                         let uu____20689 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20698 =
                           let uu____20709 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20709]  in
                         uu____20689 :: uu____20698  in
                       uu____20669 :: uu____20678  in
                     (lift_t, uu____20658)  in
                   FStar_Syntax_Syntax.Tm_app uu____20641  in
                 FStar_Syntax_Syntax.mk uu____20640  in
               uu____20633 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20762 =
           let uu____20775 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20775 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20762;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20811  ->
                        fun uu____20812  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20835 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20835
  
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
  