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
          let uu____91 = (FStar_Options.eager_subtyping ()) || solve_deferred
             in
          if uu____91
          then
            let uu____94 =
              FStar_All.pipe_right g.FStar_TypeChecker_Common.deferred
                (FStar_List.partition
                   (fun uu____146  ->
                      match uu____146 with
                      | (uu____153,p) ->
                          FStar_TypeChecker_Rel.flex_prob_closing env xs p))
               in
            match uu____94 with
            | (solve_now,defer) ->
                ((let uu____188 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel")
                     in
                  if uu____188
                  then
                    (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                     FStar_List.iter
                       (fun uu____205  ->
                          match uu____205 with
                          | (s,p) ->
                              let uu____215 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____215)
                       solve_now;
                     FStar_Util.print_string " ...DEFERRED THE REST:\n";
                     FStar_List.iter
                       (fun uu____230  ->
                          match uu____230 with
                          | (s,p) ->
                              let uu____240 =
                                FStar_TypeChecker_Rel.prob_to_string env p
                                 in
                              FStar_Util.print2 "%s: %s\n" s uu____240) defer;
                     FStar_Util.print_string "END\n")
                  else ());
                 (let g1 =
                    FStar_TypeChecker_Rel.solve_deferred_constraints env
                      (let uu___49_248 = g  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___49_248.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred = solve_now;
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___49_248.FStar_TypeChecker_Common.univ_ineqs);
                         FStar_TypeChecker_Common.implicits =
                           (uu___49_248.FStar_TypeChecker_Common.implicits)
                       })
                     in
                  let g2 =
                    let uu___52_250 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___52_250.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred = defer;
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___52_250.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits =
                        (uu___52_250.FStar_TypeChecker_Common.implicits)
                    }  in
                  g2))
          else g
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____267 =
        let uu____269 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____269  in
      if uu____267
      then
        let us =
          let uu____274 =
            let uu____278 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____278
             in
          FStar_All.pipe_right uu____274 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____297 =
            let uu____303 =
              let uu____305 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____305
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____303)  in
          FStar_Errors.log_issue r uu____297);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool))
  =
  fun env  ->
    fun uu____328  ->
      match uu____328 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____339;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____341;
          FStar_Syntax_Syntax.lbpos = uu____342;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____377 = FStar_Syntax_Subst.open_univ_vars univ_vars e
                  in
               (match uu____377 with
                | (univ_vars1,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____415) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____422) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____477) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____513 = FStar_Options.ml_ish ()  in
                                if uu____513
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____535 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____535
                            then
                              let uu____538 = FStar_Range.string_of_range r
                                 in
                              let uu____540 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____538 uu____540
                            else ());
                           FStar_Util.Inl t2)
                      | uu____545 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____547 = aux e1  in
                      match uu____547 with
                      | FStar_Util.Inr c ->
                          let uu____553 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____553
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____558 =
                               let uu____564 =
                                 let uu____566 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____566
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____564)
                                in
                             FStar_Errors.raise_error uu____558 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars1, t2, true))
           | uu____575 ->
               let uu____576 = FStar_Syntax_Subst.open_univ_vars univ_vars t1
                  in
               (match uu____576 with
                | (univ_vars1,t2) -> (univ_vars1, t2, false)))
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term))
  =
  fun pat  ->
    let mk f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____640 =
      match uu____640 with
      | (p,i) ->
          let uu____660 = decorated_pattern_as_term p  in
          (match uu____660 with
           | (vars,te) ->
               let uu____683 =
                 let uu____688 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____688)  in
               (vars, uu____683))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____702 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____702)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____706 = mk (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____710 = mk (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____710)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____733 =
          let uu____752 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____752 FStar_List.unzip  in
        (match uu____733 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____890 =
               let uu____891 =
                 let uu____892 =
                   let uu____909 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____909, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____892  in
               mk uu____891  in
             (vars1, uu____890))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____948,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____958,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd::uu____972 -> FStar_Pervasives_Native.Some hd)
  
let (lcomp_univ_opt :
  FStar_TypeChecker_Common.lcomp ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option *
      FStar_TypeChecker_Common.guard_t))
  =
  fun lc  ->
    let uu____987 =
      FStar_All.pipe_right lc FStar_TypeChecker_Common.lcomp_comp  in
    FStar_All.pipe_right uu____987
      (fun uu____1015  ->
         match uu____1015 with | (c,g) -> ((comp_univ_opt c), g))
  
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
            let uu____1088 =
              let uu____1089 =
                let uu____1100 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____1100]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____1089;
                FStar_Syntax_Syntax.flags = flags
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____1088
  
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
    fun is_layered  ->
      fun r  ->
        let err uu____1184 =
          let uu____1185 =
            let uu____1191 =
              let uu____1193 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1195 = FStar_Util.string_of_bool is_layered  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1193 uu____1195
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1191)  in
          FStar_Errors.raise_error uu____1185 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered
        then
          match repr1.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_app (uu____1207,uu____1208::is) ->
              FStar_All.pipe_right is
                (FStar_List.map FStar_Pervasives_Native.fst)
          | uu____1276 -> err ()
        else
          (match repr1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (uu____1281,c) ->
               let uu____1303 =
                 FStar_All.pipe_right c FStar_Syntax_Util.comp_to_comp_typ
                  in
               FStar_All.pipe_right uu____1303
                 (fun ct  ->
                    FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                      (FStar_List.map FStar_Pervasives_Native.fst))
           | uu____1338 -> err ())
  
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
                let uu____1374 =
                  let uu____1379 =
                    FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                      ret_wp
                     in
                  let uu____1380 =
                    let uu____1381 = FStar_Syntax_Syntax.as_arg a  in
                    let uu____1390 =
                      let uu____1401 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____1401]  in
                    uu____1381 :: uu____1390  in
                  FStar_Syntax_Syntax.mk_Tm_app uu____1379 uu____1380  in
                uu____1374 FStar_Pervasives_Native.None r  in
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
              (let uu____1474 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1474
               then
                 let uu____1479 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1481 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1483 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1485 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1479 uu____1481 uu____1483 uu____1485
               else ());
              (let uu____1490 =
                 let uu____1495 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1495 [u_a]  in
               match uu____1490 with
               | (uu____1500,return_t) ->
                   let return_t_shape_error s =
                     let uu____1515 =
                       let uu____1517 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1519 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1517 uu____1519 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1515)  in
                   let uu____1523 =
                     let uu____1552 =
                       let uu____1553 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1553.FStar_Syntax_Syntax.n  in
                     match uu____1552 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1613 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1613 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1682 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1682))
                     | uu____1703 ->
                         let uu____1704 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1704 r
                      in
                   (match uu____1523 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1787 =
                          let uu____1794 =
                            let uu____1795 =
                              let uu____1796 =
                                let uu____1803 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1803, a)  in
                              FStar_Syntax_Syntax.NT uu____1796  in
                            let uu____1814 =
                              let uu____1817 =
                                let uu____1818 =
                                  let uu____1825 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1825, e)  in
                                FStar_Syntax_Syntax.NT uu____1818  in
                              [uu____1817]  in
                            uu____1795 :: uu____1814  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1794
                            (fun b  ->
                               let uu____1841 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1843 =
                                 let uu____1845 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1845
                                  in
                               let uu____1848 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1841 uu____1843 uu____1848) r
                           in
                        (match uu____1787 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1885 =
                                        let uu____1892 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1892, t)  in
                                      FStar_Syntax_Syntax.NT uu____1885) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1918 =
                                 let uu____1921 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1922 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1921 uu____1922
                                   r
                                  in
                               FStar_All.pipe_right uu____1918
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst))
                                in
                             let c =
                               let uu____1929 =
                                 let uu____1930 =
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
                                     uu____1930;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1929  in
                             ((let uu____1954 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1954
                               then
                                 let uu____1959 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1959
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
              let uu____2003 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____2003
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2013 = mk_wp_return env ed u_a a e r  in
                 (uu____2013, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2038 =
          FStar_All.pipe_right
            (let uu___251_2040 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2040.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2040.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2040.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2040.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2038
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2061 =
          let uu____2066 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2067 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2066, uu____2067)  in
        match uu____2061 with
        | (l1,l2) ->
            let uu____2070 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2070 with
             | FStar_Pervasives_Native.Some (m,uu____2080,uu____2081) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2094 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2094 with
                  | FStar_Pervasives_Native.Some (m,uu____2108) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2141 =
                        let uu____2147 =
                          let uu____2149 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2151 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2149
                            uu____2151
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2147)
                         in
                      FStar_Errors.raise_error uu____2141
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2171 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____2171
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
            let uu____2230 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2230 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2258 = lift_comp env c11 lift1  in
                (match uu____2258 with
                 | (c12,g1) ->
                     let uu____2275 =
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
                          let uu____2314 = lift_comp env_x c21 lift2  in
                          match uu____2314 with
                          | (c22,g2) ->
                              let uu____2325 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2325))
                        in
                     (match uu____2275 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2372 =
                  let uu____2373 =
                    let uu____2379 =
                      let uu____2381 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2383 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2381
                        uu____2383
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2379)
                     in
                  FStar_Errors.raise_error uu____2373 rng  in
                ((let uu____2398 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2398
                  then
                    let uu____2403 =
                      let uu____2405 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2405
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2407 =
                      let uu____2409 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2409
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2411 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2403 uu____2407 uu____2411
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
                      let uu____2467 =
                        let uu____2472 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2473 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2474 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2475 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2472 uu____2473 uu____2474
                          ct.FStar_Syntax_Syntax.result_typ uu____2475 rng
                         in
                      match uu____2467 with
                      | (c_ret,g_ret) ->
                          let uu____2482 =
                            let uu____2487 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2487 [] rng
                             in
                          (match uu____2482 with
                           | (c,g_bind) ->
                               let uu____2494 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2494))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2539 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2539
                      then
                        let uu____2575 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2575 with
                        | (p,f_bind) ->
                            let uu____2642 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2642
                             then
                               let uu____2655 = bind_with_return c12 p f_bind
                                  in
                               match uu____2655 with
                               | (c13,g) ->
                                   let uu____2672 =
                                     let uu____2681 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2681, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2672
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2710 =
                      let uu____2721 = try_lift c11 c21  in
                      match uu____2721 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2762 = try_lift c21 c11  in
                          (match uu____2762 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2710 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2819 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2819
                          then
                            let uu____2824 = FStar_Ident.string_of_lid p  in
                            let uu____2826 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2828 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2824 uu____2826 uu____2828
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
            let uu____2881 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2881 with
            | (l,c11,c21,g1,g2) ->
                let uu____2905 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2905)
  
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
          let uu____2961 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2961
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2973 =
      let uu____2974 = FStar_Syntax_Subst.compress t  in
      uu____2974.FStar_Syntax_Syntax.n  in
    match uu____2973 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2978 -> true
    | uu____2994 -> false
  
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
              let uu____3064 =
                let uu____3066 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3066  in
              if uu____3064
              then f
              else (let uu____3073 = reason1 ()  in label uu____3073 r f)
  
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
            let uu___396_3094 = g  in
            let uu____3095 =
              let uu____3096 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3096  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3095;
              FStar_TypeChecker_Common.deferred =
                (uu___396_3094.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3094.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3094.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3117 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3117
        then c
        else
          (let uu____3122 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3122
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3164 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3164 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3192 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3192]  in
                       let us =
                         let uu____3214 =
                           let uu____3217 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3217]  in
                         u_res :: uu____3214  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3223 =
                         let uu____3228 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close
                            in
                         let uu____3229 =
                           let uu____3230 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3239 =
                             let uu____3250 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3259 =
                               let uu____3270 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3270]  in
                             uu____3250 :: uu____3259  in
                           uu____3230 :: uu____3239  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3228 uu____3229
                          in
                       uu____3223 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3312 = destruct_wp_comp c1  in
              match uu____3312 with
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
                let uu____3352 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3352
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
                  let uu____3402 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3402
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3415  ->
            match uu___0_3415 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3418 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3443 =
            let uu____3446 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3446 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3443
            (fun c  ->
               (let uu____3470 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3470) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3474 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3474)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3485 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3485 with
                | (head,uu____3502) ->
                    let uu____3523 =
                      let uu____3524 = FStar_Syntax_Util.un_uinst head  in
                      uu____3524.FStar_Syntax_Syntax.n  in
                    (match uu____3523 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3529 =
                           let uu____3531 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3531
                            in
                         Prims.op_Negation uu____3529
                     | uu____3532 -> true)))
              &&
              (let uu____3535 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3535)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v  ->
          let c =
            let uu____3563 =
              let uu____3565 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3565  in
            if uu____3563
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3572 = FStar_Syntax_Util.is_unit t  in
               if uu____3572
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
                    let uu____3581 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3581
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3587 =
                         let uu____3588 =
                           let uu____3593 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3594 =
                             let uu____3595 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3604 =
                               let uu____3615 = FStar_Syntax_Syntax.as_arg v
                                  in
                               [uu____3615]  in
                             uu____3595 :: uu____3604  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3593
                             uu____3594
                            in
                         uu____3588 FStar_Pervasives_Native.None
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3587)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3649 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3649
           then
             let uu____3654 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3656 = FStar_Syntax_Print.term_to_string v  in
             let uu____3658 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3654 uu____3656 uu____3658
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
      fun n  ->
        fun p  ->
          fun bind_t  ->
            fun ct1  ->
              fun b  ->
                fun ct2  ->
                  fun flags  ->
                    fun r1  ->
                      (let uu____3731 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3731
                       then
                         let uu____3736 =
                           let uu____3738 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3738  in
                         let uu____3739 =
                           let uu____3741 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3741  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3736 uu____3739
                       else ());
                      (let uu____3745 =
                         let uu____3752 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3753 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3754 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3752, uu____3753, uu____3754)  in
                       match uu____3745 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3762 =
                             let uu____3773 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3774 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3773,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3774)
                              in
                           (match uu____3762 with
                            | (u1,t1,is1) ->
                                let uu____3808 =
                                  let uu____3819 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3820 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3819,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3820)
                                   in
                                (match uu____3808 with
                                 | (u2,t2,is2) ->
                                     let uu____3854 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3854 with
                                      | (uu____3863,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3878 =
                                              let uu____3880 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3880 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3878)
                                             in
                                          let uu____3884 =
                                            let uu____3929 =
                                              let uu____3930 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3930.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3929 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4006 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4006 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4091 =
                                                       let uu____4118 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4118
                                                         (fun uu____4203  ->
                                                            match uu____4203
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4284
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4297
                                                                  =
                                                                  let uu____4304
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4304
                                                                   in
                                                                (l1,
                                                                  uu____4284,
                                                                  uu____4297))
                                                        in
                                                     (match uu____4091 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4464 ->
                                                let uu____4465 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4465 r1
                                             in
                                          (match uu____3884 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4590 =
                                                 let uu____4597 =
                                                   let uu____4598 =
                                                     let uu____4599 =
                                                       let uu____4606 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4606, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4599
                                                      in
                                                   let uu____4617 =
                                                     let uu____4620 =
                                                       let uu____4621 =
                                                         let uu____4628 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4628, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4621
                                                        in
                                                     [uu____4620]  in
                                                   uu____4598 :: uu____4617
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4597
                                                   (fun b1  ->
                                                      let uu____4644 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4646 =
                                                        let uu____4648 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4650 =
                                                          FStar_Ident.string_of_lid
                                                            n
                                                           in
                                                        let uu____4652 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4648
                                                          uu____4650
                                                          uu____4652
                                                         in
                                                      let uu____4655 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4644 uu____4646
                                                        uu____4655) r1
                                                  in
                                               (match uu____4590 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4692 =
                                                               let uu____4699
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4699,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4692)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4726 =
                                                          let uu____4729 =
                                                            let uu____4730 =
                                                              let uu____4731
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4731.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4730
                                                             in
                                                          let uu____4740 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4729
                                                            uu____4740 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4726
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4753
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4753)
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
                                                        let uu____4772 =
                                                          let uu____4773 =
                                                            let uu____4776 =
                                                              let uu____4777
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4777.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4776
                                                             in
                                                          uu____4773.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4772 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4810 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4810
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4820
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    let uu____4828
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4828
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4849
                                                                    =
                                                                    let uu____4852
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4852
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4827,
                                                                    uu____4849)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4820
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4866
                                                                   =
                                                                   let uu____4869
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4870
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4869
                                                                    uu____4870
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4866
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4876 ->
                                                            failwith
                                                              "imspossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4893 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4901
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4901)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4893
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4915 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4915
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4917 =
                                                        let uu____4922 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4923 =
                                                          let uu____4924 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4924
                                                           in
                                                        (uu____4922,
                                                          uu____4923)
                                                         in
                                                      match uu____4917 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4950 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4951 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4950 uu____4951
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4954 =
                                                        let uu____4955 =
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
                                                            = uu____4955;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4954
                                                       in
                                                    ((let uu____4975 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4975
                                                      then
                                                        let uu____4980 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4980
                                                      else ());
                                                     (let uu____4985 =
                                                        let uu____4986 =
                                                          let uu____4989 =
                                                            let uu____4992 =
                                                              let uu____4995
                                                                =
                                                                let uu____4998
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____4998]
                                                                 in
                                                              g_guard ::
                                                                uu____4995
                                                               in
                                                            f_guard ::
                                                              uu____4992
                                                             in
                                                          g_uvars ::
                                                            uu____4989
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4986
                                                         in
                                                      (c, uu____4985)))))))))
  
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
                let uu____5043 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5069 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5069 with
                  | (a,kwp) ->
                      let uu____5100 = destruct_wp_comp ct1  in
                      let uu____5107 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5100, uu____5107)
                   in
                match uu____5043 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5160 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5160]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5180 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5180]
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
                      let uu____5227 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5236 =
                        let uu____5247 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5256 =
                          let uu____5267 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5276 =
                            let uu____5287 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5296 =
                              let uu____5307 =
                                let uu____5316 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5316  in
                              [uu____5307]  in
                            uu____5287 :: uu____5296  in
                          uu____5267 :: uu____5276  in
                        uu____5247 :: uu____5256  in
                      uu____5227 :: uu____5236  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5369 =
                        let uu____5374 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5374 wp_args  in
                      uu____5369 FStar_Pervasives_Native.None
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
              let uu____5422 =
                let uu____5427 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5428 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5427, uu____5428)  in
              match uu____5422 with
              | (ct1,ct2) ->
                  let uu____5435 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5435 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5486 = lift_comps env c1 c2 b true  in
                       (match uu____5486 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5504 =
                              let uu____5509 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5510 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5509, uu____5510)  in
                            (match uu____5504 with
                             | (ct11,ct21) ->
                                 let uu____5517 =
                                   let uu____5522 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5522
                                   then
                                     let bind_t =
                                       let uu____5530 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5530
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5533 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5533,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5517 with
                                  | (c,g_bind) ->
                                      let uu____5540 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5540)))))
  
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
            let uu____5576 =
              let uu____5577 =
                let uu____5588 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5588]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5577;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5576  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5633 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5639  ->
              match uu___1_5639 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5642 -> false))
       in
    if uu____5633
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5654  ->
              match uu___2_5654 with
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
        let uu____5682 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5682
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5693 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5693  in
           let pure_assume_wp1 =
             let uu____5698 = FStar_TypeChecker_Env.get_range env  in
             let uu____5699 =
               let uu____5704 =
                 let uu____5705 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5705]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5704  in
             uu____5699 FStar_Pervasives_Native.None uu____5698  in
           let uu____5738 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5738)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5766 =
          let uu____5767 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5767 with
          | (c,g_c) ->
              let uu____5778 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5778
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5792 = weaken_comp env c f1  in
                     (match uu____5792 with
                      | (c1,g_w) ->
                          let uu____5803 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5803)))
           in
        let uu____5804 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5804 weaken
  
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
                 let uu____5861 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5861  in
               let pure_assert_wp1 =
                 let uu____5866 =
                   let uu____5871 =
                     let uu____5872 =
                       let uu____5881 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5881
                        in
                     [uu____5872]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5871
                    in
                 uu____5866 FStar_Pervasives_Native.None r  in
               bind_pure_wp_with env pure_assert_wp1 c flags)
  
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
            let uu____5951 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5951
            then (lc, g0)
            else
              (let flags =
                 let uu____5963 =
                   let uu____5971 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5971
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5963 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6001 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6009  ->
                               match uu___3_6009 with
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
                               | uu____6012 -> []))
                        in
                     FStar_List.append flags uu____6001
                  in
               let strengthen uu____6022 =
                 let uu____6023 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6023 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6042 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6042 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6049 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6049
                              then
                                let uu____6053 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6055 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6053 uu____6055
                              else ());
                             (let uu____6060 =
                                strengthen_comp env reason c f flags  in
                              match uu____6060 with
                              | (c1,g_s) ->
                                  let uu____6071 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6071))))
                  in
               let uu____6072 =
                 let uu____6073 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6073
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6072,
                 (let uu___707_6075 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___707_6075.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___707_6075.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___707_6075.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6084  ->
            match uu___4_6084 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6088 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6117 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6117
          then e
          else
            (let uu____6124 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6127 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6127)
                in
             if uu____6124
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
              let is_unit =
                match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.unit_lid
                | uu____6197 -> false  in
              if is_unit
              then
                let uu____6204 =
                  let uu____6206 =
                    let uu____6207 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6207
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6206
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6204
                 then
                   let uu____6216 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6216 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6232 = close_wp_comp env [x] c  in
                    (uu____6232, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6235 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6263  ->
            match uu____6263 with
            | (b,lc2) ->
                let debug f =
                  let uu____6283 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6283 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6296 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6296
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6306 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6306
                       then
                         let uu____6311 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6311
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6318 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6318
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6327 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6327
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6334 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6334
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6350 =
                  let uu____6351 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6351
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6359 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6359, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6362 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6362 with
                     | (c1,g_c1) ->
                         let uu____6373 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6373 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6385 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6388 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6388
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6385
                                 in
                              (debug
                                 (fun uu____6414  ->
                                    let uu____6415 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6417 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6422 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6415 uu____6417 uu____6422);
                               (let aux uu____6440 =
                                  let uu____6441 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6441
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6472
                                        ->
                                        let uu____6473 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6473
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6505 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6505
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6552 =
                                  let aux_with_trivial_guard uu____6582 =
                                    let uu____6583 = aux ()  in
                                    match uu____6583 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6641 =
                                    let uu____6643 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6643  in
                                  if uu____6641
                                  then
                                    let uu____6659 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6659
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6686 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6686))
                                  else
                                    (let uu____6703 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6703
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___810_6734 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___810_6734.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___810_6734.FStar_Syntax_Syntax.index);
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
                                           let uu____6765 =
                                             let uu____6770 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6770
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6765 with
                                            | (c21,g_close) ->
                                                let uu____6791 =
                                                  let uu____6799 =
                                                    let uu____6800 =
                                                      let uu____6803 =
                                                        let uu____6806 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6806; g_close]
                                                         in
                                                      g_c1 :: uu____6803  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6800
                                                     in
                                                  (c21, uu____6799, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6791)
                                       | (uu____6819,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6831 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6831 with
                                            | (c21,g_close) ->
                                                let uu____6854 =
                                                  let uu____6862 =
                                                    let uu____6863 =
                                                      let uu____6866 =
                                                        let uu____6869 =
                                                          let uu____6870 =
                                                            let uu____6871 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6871]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6870
                                                            g_c2
                                                           in
                                                        [uu____6869; g_close]
                                                         in
                                                      g_c1 :: uu____6866  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6863
                                                     in
                                                  (c21, uu____6862,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6854)
                                       | (uu____6900,uu____6901) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6916 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6916
                                        then
                                          let uu____6931 =
                                            let uu____6939 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6939, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6931
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6952 = try_simplify ()  in
                                match uu____6952 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6987  ->
                                          let uu____6988 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6988);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____7004  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7035 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7035 with
                                        | (c,g_bind) ->
                                            let uu____7046 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7046)
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
                                        let uu____7073 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7073 with
                                        | (m,uu____7085,lift2) ->
                                            let uu____7087 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7087 with
                                             | (c23,g2) ->
                                                 let uu____7098 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7098 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7114 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7114
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7124 =
                                                          let uu____7129 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7130 =
                                                            let uu____7131 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7140 =
                                                              let uu____7151
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7151]
                                                               in
                                                            uu____7131 ::
                                                              uu____7140
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7129
                                                            uu____7130
                                                           in
                                                        uu____7124
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7184 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7184 with
                                                       | (c,g_s) ->
                                                           let uu____7199 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7199))))
                                         in
                                      let uu____7200 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7216 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7216, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7200 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7232 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7232
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7241 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7241
                                             then
                                               (debug
                                                  (fun uu____7255  ->
                                                     let uu____7256 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7258 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7256 uu____7258);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7265 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7265
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7270 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7273 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7273)
                                                   in
                                                if uu____7270
                                                then
                                                  let e1' =
                                                    let uu____7298 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7298
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7310  ->
                                                        let uu____7311 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7313 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7311
                                                          uu____7313);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7328  ->
                                                        let uu____7329 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7331 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7329
                                                          uu____7331);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7338 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7338
                                                       in
                                                    let uu____7339 =
                                                      let uu____7344 =
                                                        let uu____7345 =
                                                          let uu____7346 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7346]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7345
                                                         in
                                                      weaken_comp uu____7344
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7339 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7372 =
                                                            let uu____7373 =
                                                              let uu____7374
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7374]
                                                               in
                                                            let uu____7393 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7373
                                                              uu____7393
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7372
                                                           in
                                                        let uu____7394 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7394
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7405 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7405))))))
                                          else mk_bind1 c1 b c2 trivial_guard))))))
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
      | uu____7422 -> g2
  
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
            (let uu____7446 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7446)
           in
        let flags =
          if should_return1
          then
            let uu____7454 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7454
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7472 =
          let uu____7473 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7473 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7486 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7486
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7494 =
                  let uu____7496 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7496  in
                (if uu____7494
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___935_7505 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___935_7505.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___935_7505.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___935_7505.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7506 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7506, g_c)
                 else
                   (let uu____7509 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7509, g_c)))
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
                 let ret =
                   let uu____7520 =
                     let uu____7521 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7521
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7520
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7524 =
                   let uu____7529 =
                     let uu____7530 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7530
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7529  in
                 match uu____7524 with
                 | (bind_c,g_bind) ->
                     let uu____7539 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7540 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7539, uu____7540))
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_TypeChecker_Common.mk_lcomp
            lc.FStar_TypeChecker_Common.eff_name
            lc.FStar_TypeChecker_Common.res_typ flags refine
  
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
            fun uu____7576  ->
              match uu____7576 with
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
                    let uu____7588 =
                      ((let uu____7592 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7592) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7588
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7610 =
        let uu____7611 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7611  in
      FStar_Syntax_Syntax.fvar uu____7610 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7661 =
                    let uu____7666 =
                      let uu____7667 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7667 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7666 [u_a]
                     in
                  match uu____7661 with
                  | (uu____7678,conjunction) ->
                      let uu____7680 =
                        let uu____7689 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7704 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7689, uu____7704)  in
                      (match uu____7680 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7750 =
                               let uu____7752 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7752 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7750)
                              in
                           let uu____7756 =
                             let uu____7801 =
                               let uu____7802 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7802.FStar_Syntax_Syntax.n  in
                             match uu____7801 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7851) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7883 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7883 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7955 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7955 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8103 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8103)))
                             | uu____8136 ->
                                 let uu____8137 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8137 r
                              in
                           (match uu____7756 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8262 =
                                  let uu____8269 =
                                    let uu____8270 =
                                      let uu____8271 =
                                        let uu____8278 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8278, a)  in
                                      FStar_Syntax_Syntax.NT uu____8271  in
                                    [uu____8270]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8269
                                    (fun b  ->
                                       let uu____8294 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8296 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8298 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8294 uu____8296 uu____8298) r
                                   in
                                (match uu____8262 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8336 =
                                                let uu____8343 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8343, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8336) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8382 =
                                           let uu____8383 =
                                             let uu____8386 =
                                               let uu____8387 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8387.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8386
                                              in
                                           uu____8383.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8382 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8398,uu____8399::is) ->
                                             let uu____8441 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8441
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8474 ->
                                             let uu____8475 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8475 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8491 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8491)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8496 =
                                           let uu____8497 =
                                             let uu____8500 =
                                               let uu____8501 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8501.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8500
                                              in
                                           uu____8497.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8496 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8512,uu____8513::is) ->
                                             let uu____8555 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8555
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8588 ->
                                             let uu____8589 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8589 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8605 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8605)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8610 =
                                         let uu____8611 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8611.FStar_Syntax_Syntax.n  in
                                       match uu____8610 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8616,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8671 ->
                                           let uu____8672 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8672 r
                                        in
                                     let uu____8681 =
                                       let uu____8682 =
                                         let uu____8683 =
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
                                             uu____8683;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8682
                                        in
                                     let uu____8706 =
                                       let uu____8707 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8707 g_guard
                                        in
                                     (uu____8681, uu____8706))))
  
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
                fun uu____8752  ->
                  let if_then_else =
                    let uu____8758 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8758 FStar_Util.must  in
                  let uu____8765 = destruct_wp_comp ct1  in
                  match uu____8765 with
                  | (uu____8776,uu____8777,wp_t) ->
                      let uu____8779 = destruct_wp_comp ct2  in
                      (match uu____8779 with
                       | (uu____8790,uu____8791,wp_e) ->
                           let wp =
                             let uu____8796 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8797 =
                               let uu____8802 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else
                                  in
                               let uu____8803 =
                                 let uu____8804 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8813 =
                                   let uu____8824 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8833 =
                                     let uu____8844 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8853 =
                                       let uu____8864 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8864]  in
                                     uu____8844 :: uu____8853  in
                                   uu____8824 :: uu____8833  in
                                 uu____8804 :: uu____8813  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8802
                                 uu____8803
                                in
                             uu____8797 FStar_Pervasives_Native.None
                               uu____8796
                              in
                           let uu____8913 = mk_comp ed u_a a wp []  in
                           (uu____8913, FStar_TypeChecker_Env.trivial_guard))
  
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        let post_k =
          let uu____8933 =
            let uu____8942 = FStar_Syntax_Syntax.null_binder t  in
            [uu____8942]  in
          let uu____8961 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8933 uu____8961  in
        let kwp =
          let uu____8967 =
            let uu____8976 = FStar_Syntax_Syntax.null_binder post_k  in
            [uu____8976]  in
          let uu____8995 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8967 uu____8995  in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k  in
        let wp =
          let uu____9002 =
            let uu____9003 = FStar_Syntax_Syntax.mk_binder post  in
            [uu____9003]  in
          let uu____9022 = fvar_const env FStar_Parser_Const.false_lid  in
          FStar_Syntax_Util.abs uu____9002 uu____9022
            (FStar_Pervasives_Native.Some
               (FStar_Syntax_Util.mk_residual_comp
                  FStar_Parser_Const.effect_Tot_lid
                  FStar_Pervasives_Native.None [FStar_Syntax_Syntax.TOTAL]))
           in
        let md =
          FStar_TypeChecker_Env.get_effect_decl env
            FStar_Parser_Const.effect_PURE_lid
           in
        mk_comp md u t wp []
  
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
            let uu____9081 =
              let uu____9082 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9082]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9081  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9129  ->
                   match uu____9129 with
                   | (uu____9143,eff_label,uu____9145,uu____9146) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9159 =
            let uu____9167 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9205  ->
                      match uu____9205 with
                      | (uu____9220,uu____9221,flags,uu____9223) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9240  ->
                                  match uu___5_9240 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9243 -> false))))
               in
            if uu____9167
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9159 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9280 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9282 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9282
                then
                  let uu____9289 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9289, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9310 =
                       should_not_inline_whole_match ||
                         (let uu____9313 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9313)
                        in
                     if uu____9310 then cthen true else cthen false  in
                   let uu____9320 =
                     let uu____9331 =
                       let uu____9344 =
                         let uu____9349 =
                           let uu____9360 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9410  ->
                                     match uu____9410 with
                                     | (g,uu____9429,uu____9430,uu____9431)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9360
                             (FStar_List.fold_left
                                (fun uu____9479  ->
                                   fun g  ->
                                     match uu____9479 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9520 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9520
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9349
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9344
                         (fun l  ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l)
                        in
                     FStar_All.pipe_right uu____9331
                       (fun uu____9618  ->
                          match uu____9618 with
                          | (l1,l2) ->
                              let uu____9659 = FStar_List.hd l2  in
                              (l1, uu____9659))
                      in
                   match uu____9320 with
                   | (neg_branch_conds,exhaustiveness_branch_cond) ->
                       let uu____9688 =
                         match lcases with
                         | [] ->
                             let uu____9719 =
                               comp_pure_wp_false env u_res_t res_t  in
                             (FStar_Pervasives_Native.None, uu____9719,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9722 ->
                             let uu____9739 =
                               let uu____9772 =
                                 let uu____9783 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one))
                                    in
                                 FStar_All.pipe_right uu____9783
                                   (fun uu____9855  ->
                                      match uu____9855 with
                                      | (l1,l2) ->
                                          let uu____9896 = FStar_List.hd l2
                                             in
                                          (l1, uu____9896))
                                  in
                               match uu____9772 with
                               | (neg_branch_conds1,neg_last) ->
                                   let uu____9953 =
                                     let uu____9992 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____9992
                                       (fun uu____10204  ->
                                          match uu____10204 with
                                          | (l1,l2) ->
                                              let uu____10355 =
                                                FStar_List.hd l2  in
                                              (l1, uu____10355))
                                      in
                                   (match uu____9953 with
                                    | (lcases1,(g_last,eff_last,uu____10457,c_last))
                                        ->
                                        let uu____10527 =
                                          let lc =
                                            maybe_return eff_last c_last  in
                                          let uu____10533 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc
                                             in
                                          match uu____10533 with
                                          | (c,g) ->
                                              let uu____10544 =
                                                let uu____10545 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last
                                                   in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10545
                                                 in
                                              (c, uu____10544)
                                           in
                                        (match uu____10527 with
                                         | (c,g) ->
                                             let uu____10580 =
                                               let uu____10581 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10581
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env)
                                                in
                                             (lcases1, neg_branch_conds1,
                                               uu____10580, c, g)))
                                in
                             (match uu____9739 with
                              | (lcases1,neg_branch_conds1,md,comp,g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10713  ->
                                       fun neg_cond  ->
                                         fun uu____10715  ->
                                           match (uu____10713, uu____10715)
                                           with
                                           | ((g,eff_label,uu____10775,cthen),
                                              (uu____10777,celse,g_comp1)) ->
                                               let uu____10824 =
                                                 let uu____10829 =
                                                   maybe_return eff_label
                                                     cthen
                                                    in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10829
                                                  in
                                               (match uu____10824 with
                                                | (cthen1,g_then) ->
                                                    let uu____10840 =
                                                      let uu____10851 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false
                                                         in
                                                      match uu____10851 with
                                                      | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                          ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m
                                                             in
                                                          let uu____10879 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          let uu____10880 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          (md1, uu____10879,
                                                            uu____10880,
                                                            g_lift_then,
                                                            g_lift_else)
                                                       in
                                                    (match uu____10840 with
                                                     | (md1,ct_then,ct_else,g_lift_then,g_lift_else)
                                                         ->
                                                         let fn =
                                                           let uu____10931 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered
                                                              in
                                                           if uu____10931
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction
                                                            in
                                                         let uu____10965 =
                                                           let uu____10970 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10970
                                                            in
                                                         (match uu____10965
                                                          with
                                                          | (c,g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10982
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then
                                                                   in
                                                                let uu____10983
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10982
                                                                  uu____10983
                                                                 in
                                                              let g_else =
                                                                let uu____10985
                                                                  =
                                                                  let uu____10986
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g  in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10986
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10985
                                                                 in
                                                              let uu____10989
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction]
                                                                 in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10989)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp))
                          in
                       (match uu____9688 with
                        | (md,comp,g_comp) ->
                            let uu____11005 =
                              let uu____11010 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false
                                   in
                                let check1 =
                                  let uu____11017 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____11017 check
                                   in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags
                                 in
                              match uu____11010 with
                              | (c,g) ->
                                  let uu____11028 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g
                                     in
                                  (c, uu____11028)
                               in
                            (match uu____11005 with
                             | (comp1,g_comp1) ->
                                 let g_comp2 =
                                   let uu____11036 =
                                     let uu____11037 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     [uu____11037]  in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____11036 g_comp1
                                    in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____11080::[] -> (comp1, g_comp2)
                                  | uu____11123 ->
                                      let uu____11140 =
                                        let uu____11142 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11142
                                          FStar_Syntax_Util.is_layered
                                         in
                                      if uu____11140
                                      then (comp1, g_comp2)
                                      else
                                        (let comp2 =
                                           FStar_TypeChecker_Env.comp_to_comp_typ
                                             env comp1
                                            in
                                         let md1 =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env
                                             comp2.FStar_Syntax_Syntax.effect_name
                                            in
                                         let uu____11155 =
                                           destruct_wp_comp comp2  in
                                         match uu____11155 with
                                         | (uu____11166,uu____11167,wp) ->
                                             let ite_wp =
                                               let uu____11170 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11170 FStar_Util.must
                                                in
                                             let wp1 =
                                               let uu____11180 =
                                                 let uu____11185 =
                                                   FStar_TypeChecker_Env.inst_effect_fun_with
                                                     [u_res_t] env md1 ite_wp
                                                    in
                                                 let uu____11186 =
                                                   let uu____11187 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       res_t
                                                      in
                                                   let uu____11196 =
                                                     let uu____11207 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp
                                                        in
                                                     [uu____11207]  in
                                                   uu____11187 :: uu____11196
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____11185 uu____11186
                                                  in
                                               uu____11180
                                                 FStar_Pervasives_Native.None
                                                 wp.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____11240 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags
                                                in
                                             (uu____11240, g_comp2))))))
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
          let uu____11275 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____11275 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11291 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____11297 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____11291 uu____11297
              else
                (let uu____11306 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____11312 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____11306 uu____11312)
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
          let uu____11337 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____11337
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____11340 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____11340
        then u_res
        else
          (let is_total =
             let uu____11347 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____11347
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11358 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____11358 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11361 =
                    let uu____11367 =
                      let uu____11369 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11369
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11367)
                     in
                  FStar_Errors.raise_error uu____11361
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
      let uu____11393 = destruct_wp_comp ct  in
      match uu____11393 with
      | (u_t,t,wp) ->
          let vc =
            let uu____11412 = FStar_TypeChecker_Env.get_range env  in
            let uu____11413 =
              let uu____11418 =
                let uu____11419 =
                  let uu____11420 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____11420 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____11419
                 in
              let uu____11427 =
                let uu____11428 = FStar_Syntax_Syntax.as_arg t  in
                let uu____11437 =
                  let uu____11448 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____11448]  in
                uu____11428 :: uu____11437  in
              FStar_Syntax_Syntax.mk_Tm_app uu____11418 uu____11427  in
            uu____11413 FStar_Pervasives_Native.None uu____11412  in
          let uu____11481 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____11481)
  
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
                  let uu____11536 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____11536 with
                  | FStar_Pervasives_Native.Some uu____11551 ->
                      ((let uu____11569 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____11569
                        then
                          let uu____11573 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11573
                        else ());
                       (let coercion =
                          let uu____11579 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____11579
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____11586 =
                            let uu____11587 =
                              let uu____11588 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11588
                               in
                            (FStar_Pervasives_Native.None, uu____11587)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11586
                           in
                        let e1 =
                          let uu____11594 =
                            let uu____11599 =
                              let uu____11600 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____11600]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____11599
                             in
                          uu____11594 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____11634 =
                          let uu____11640 =
                            let uu____11642 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11642
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11640)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11634);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____11661 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11679 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11690 -> false 
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
      let uu____11714 = FStar_Syntax_Util.head_and_args t2  in
      match uu____11714 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____11759 =
              let uu____11774 =
                let uu____11775 = FStar_Syntax_Subst.compress h1  in
                uu____11775.FStar_Syntax_Syntax.n  in
              (uu____11774, args)  in
            match uu____11759 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11822,uu____11823) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11856) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11877,branches),uu____11879) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11943 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11944 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11944 with
                               | (uu____11945,uu____11946,br_body) ->
                                   let uu____11964 =
                                     let uu____11965 =
                                       let uu____11970 =
                                         let uu____11971 =
                                           let uu____11974 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11974
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11971
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11970  in
                                     FStar_All.pipe_right br_body uu____11965
                                      in
                                   (match uu____11964 with
                                    | No  -> No
                                    | uu____11985 -> Maybe))) No)
            | uu____11986 -> No  in
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
            (((let uu____12038 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____12038) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12057 =
                 let uu____12058 = FStar_Syntax_Subst.compress t1  in
                 uu____12058.FStar_Syntax_Syntax.n  in
               match uu____12057 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____12063 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12073 =
                 let uu____12074 = FStar_Syntax_Subst.compress t1  in
                 uu____12074.FStar_Syntax_Syntax.n  in
               match uu____12073 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____12079 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____12090 =
                 let uu____12091 = FStar_Syntax_Subst.compress t2  in
                 uu____12091.FStar_Syntax_Syntax.n  in
               match uu____12090 with
               | FStar_Syntax_Syntax.Tm_type uu____12095 -> true
               | uu____12097 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____12100 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____12100 with
             | (head,args) ->
                 ((let uu____12150 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____12150
                   then
                     let uu____12154 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____12156 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____12158 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____12160 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12154 uu____12156 uu____12158 uu____12160
                   else ());
                  (let mk_erased u t =
                     let uu____12178 =
                       let uu____12181 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12181 [u]  in
                     let uu____12182 =
                       let uu____12193 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____12193]  in
                     FStar_Syntax_Util.mk_app uu____12178 uu____12182  in
                   let uu____12218 =
                     let uu____12233 =
                       let uu____12234 = FStar_Syntax_Util.un_uinst head  in
                       uu____12234.FStar_Syntax_Syntax.n  in
                     (uu____12233, args)  in
                   match uu____12218 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12272 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____12272 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12312 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12312 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12352 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12352 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12392 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12392 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12413 ->
                       let uu____12428 =
                         let uu____12433 = check_erased env res_typ  in
                         let uu____12434 = check_erased env exp_t  in
                         (uu____12433, uu____12434)  in
                       (match uu____12428 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12443 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____12443 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____12454 =
                                   let uu____12459 =
                                     let uu____12460 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____12460]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12459
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____12454 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12495 =
                              let uu____12500 =
                                let uu____12501 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____12501]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12500
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____12495 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12534 ->
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
        let uu____12569 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____12569 with
        | (hd,args) ->
            let uu____12618 =
              let uu____12633 =
                let uu____12634 = FStar_Syntax_Subst.compress hd  in
                uu____12634.FStar_Syntax_Syntax.n  in
              (uu____12633, args)  in
            (match uu____12618 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12672 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____12699  ->
                      FStar_Pervasives_Native.Some uu____12699) uu____12672
             | uu____12700 -> FStar_Pervasives_Native.None)
  
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
          (let uu____12753 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____12753
           then
             let uu____12756 = FStar_Syntax_Print.term_to_string e  in
             let uu____12758 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____12760 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12756 uu____12758 uu____12760
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12770 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____12770 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12795 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12821 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12821, false)
             else
               (let uu____12831 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12831, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12844) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12856 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12856
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1422_12872 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1422_12872.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1422_12872.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1422_12872.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____12879 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12879 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12895 =
                      let uu____12896 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12896 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____12916 =
                            let uu____12918 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____12918 = FStar_Syntax_Util.Equal  in
                          if uu____12916
                          then
                            ((let uu____12925 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12925
                              then
                                let uu____12929 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12931 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12929 uu____12931
                              else ());
                             (let uu____12936 = set_result_typ c  in
                              (uu____12936, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12943 ->
                                   true
                               | uu____12951 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12960 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12960
                                  in
                               let lc1 =
                                 let uu____12962 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12963 =
                                   let uu____12964 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12964)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12962 uu____12963
                                  in
                               ((let uu____12968 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12968
                                 then
                                   let uu____12972 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12974 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12976 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12978 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12972 uu____12974 uu____12976
                                     uu____12978
                                 else ());
                                (let uu____12983 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12983 with
                                 | (c1,g_lc) ->
                                     let uu____12994 = set_result_typ c1  in
                                     let uu____12995 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12994, uu____12995)))
                             else
                               ((let uu____12999 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12999
                                 then
                                   let uu____13003 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____13005 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____13003 uu____13005
                                 else ());
                                (let uu____13010 = set_result_typ c  in
                                 (uu____13010, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1459_13014 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1459_13014.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1459_13014.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1459_13014.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____13024 =
                      let uu____13025 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____13025
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____13035 =
                           let uu____13036 = FStar_Syntax_Subst.compress f1
                              in
                           uu____13036.FStar_Syntax_Syntax.n  in
                         match uu____13035 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____13043,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13045;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13046;_},uu____13047)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1475_13073 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1475_13073.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1475_13073.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1475_13073.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____13074 ->
                             let uu____13075 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____13075 with
                              | (c,g_c) ->
                                  ((let uu____13087 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____13087
                                    then
                                      let uu____13091 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____13093 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____13095 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____13097 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____13091 uu____13093 uu____13095
                                        uu____13097
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
                                      if apply_guard
                                      then
                                        let uu____13110 =
                                          let uu____13115 =
                                            let uu____13116 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____13116]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____13115
                                           in
                                        uu____13110
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____13143 =
                                      let uu____13148 =
                                        FStar_All.pipe_left
                                          (fun uu____13169  ->
                                             FStar_Pervasives_Native.Some
                                               uu____13169)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____13170 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____13171 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____13172 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____13148
                                        uu____13170 e uu____13171 uu____13172
                                       in
                                    match uu____13143 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1493_13180 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1493_13180.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1493_13180.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____13182 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____13182
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____13185 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____13185 with
                                         | (c2,g_lc) ->
                                             ((let uu____13197 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____13197
                                               then
                                                 let uu____13201 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____13201
                                               else ());
                                              (let uu____13206 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____13206))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13215  ->
                              match uu___6_13215 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13218 -> []))
                       in
                    let lc1 =
                      let uu____13220 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____13220 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1509_13222 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1509_13222.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1509_13222.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1509_13222.FStar_TypeChecker_Common.implicits)
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
        let uu____13258 =
          let uu____13261 =
            let uu____13266 =
              let uu____13267 =
                let uu____13276 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____13276  in
              [uu____13267]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____13266  in
          uu____13261 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____13258  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____13299 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____13299
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13318 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13334 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13351 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____13351
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____13367)::(ens,uu____13369)::uu____13370 ->
                    let uu____13413 =
                      let uu____13416 = norm req  in
                      FStar_Pervasives_Native.Some uu____13416  in
                    let uu____13417 =
                      let uu____13418 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____13418  in
                    (uu____13413, uu____13417)
                | uu____13421 ->
                    let uu____13432 =
                      let uu____13438 =
                        let uu____13440 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13440
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13438)
                       in
                    FStar_Errors.raise_error uu____13432
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____13460)::uu____13461 ->
                    let uu____13488 =
                      let uu____13493 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13493
                       in
                    (match uu____13488 with
                     | (us_r,uu____13525) ->
                         let uu____13526 =
                           let uu____13531 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13531
                            in
                         (match uu____13526 with
                          | (us_e,uu____13563) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____13566 =
                                  let uu____13567 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13567
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13566
                                  us_r
                                 in
                              let as_ens =
                                let uu____13569 =
                                  let uu____13570 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13570
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13569
                                  us_e
                                 in
                              let req =
                                let uu____13574 =
                                  let uu____13579 =
                                    let uu____13580 =
                                      let uu____13591 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____13591]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____13580
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____13579
                                   in
                                uu____13574 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____13631 =
                                  let uu____13636 =
                                    let uu____13637 =
                                      let uu____13648 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____13648]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____13637
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____13636
                                   in
                                uu____13631 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____13685 =
                                let uu____13688 = norm req  in
                                FStar_Pervasives_Native.Some uu____13688  in
                              let uu____13689 =
                                let uu____13690 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____13690  in
                              (uu____13685, uu____13689)))
                | uu____13693 -> failwith "Impossible"))
  
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
        (let uu____13732 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____13732
         then
           let uu____13737 = FStar_Syntax_Print.term_to_string tm  in
           let uu____13739 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13737
             uu____13739
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
      fun head  ->
        fun arg  ->
          let tm =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head, [arg]))
              FStar_Pervasives_Native.None head.FStar_Syntax_Syntax.pos
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
          (let uu____13798 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____13798
           then
             let uu____13803 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13805 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13803
               uu____13805
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13816 =
      let uu____13818 =
        let uu____13819 = FStar_Syntax_Subst.compress t  in
        uu____13819.FStar_Syntax_Syntax.n  in
      match uu____13818 with
      | FStar_Syntax_Syntax.Tm_app uu____13823 -> false
      | uu____13841 -> true  in
    if uu____13816
    then t
    else
      (let uu____13846 = FStar_Syntax_Util.head_and_args t  in
       match uu____13846 with
       | (head,args) ->
           let uu____13889 =
             let uu____13891 =
               let uu____13892 = FStar_Syntax_Subst.compress head  in
               uu____13892.FStar_Syntax_Syntax.n  in
             match uu____13891 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13897 -> false  in
           if uu____13889
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13929 ->
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
          ((let uu____13976 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13976
            then
              let uu____13979 = FStar_Syntax_Print.term_to_string e  in
              let uu____13981 = FStar_Syntax_Print.term_to_string t  in
              let uu____13983 =
                let uu____13985 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13985
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13979 uu____13981 uu____13983
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____14021 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____14021 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____14055 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____14133  ->
                          match uu____14133 with
                          | (uu____14141,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14148 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____14148 = FStar_Syntax_Util.Equal)))
                   in
                match uu____14055 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____14267 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____14267 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____14281 =
                      let uu____14287 =
                        let uu____14289 = FStar_Util.string_of_int n_expected
                           in
                        let uu____14291 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____14293 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14289 uu____14291 uu____14293
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14287)
                       in
                    let uu____14297 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____14281 uu____14297
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_14315 =
              match uu___7_14315 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____14358 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____14358 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____14489,uu____14476) when
                           uu____14489 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14522,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____14524))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14558 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____14558 with
                            | (v,uu____14599,g) ->
                                ((let uu____14614 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14614
                                  then
                                    let uu____14617 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14617
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14627 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14627 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14720 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14720))))
                       | (uu____14747,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14784 =
                             let uu____14797 =
                               let uu____14804 =
                                 let uu____14809 = FStar_Dyn.mkdyn env  in
                                 (uu____14809, tau)  in
                               FStar_Pervasives_Native.Some uu____14804  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____14797
                              in
                           (match uu____14784 with
                            | (v,uu____14842,g) ->
                                ((let uu____14857 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14857
                                  then
                                    let uu____14860 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14860
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14870 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14870 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14963 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14963))))
                       | (uu____14990,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____15038 =
                       let uu____15065 = inst_n_binders t1  in
                       aux [] uu____15065 bs1  in
                     (match uu____15038 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____15137) -> (e, torig, guard)
                           | (uu____15168,[]) when
                               let uu____15199 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____15199 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15201 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15229 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____15242 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____15254 =
      let uu____15258 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____15258
        (FStar_List.map
           (fun u  ->
              let uu____15270 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____15270 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____15254 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____15298 = FStar_Util.set_is_empty x  in
      if uu____15298
      then []
      else
        (let s =
           let uu____15318 =
             let uu____15321 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____15321  in
           FStar_All.pipe_right uu____15318 FStar_Util.set_elements  in
         (let uu____15339 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____15339
          then
            let uu____15344 =
              let uu____15346 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____15346  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15344
          else ());
         (let r =
            let uu____15355 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____15355  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____15400 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____15400
                     then
                       let uu____15405 =
                         let uu____15407 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15407
                          in
                       let uu____15411 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____15413 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15405 uu____15411 uu____15413
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
      let univnames =
        let uu____15443 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____15443 FStar_Util.set_elements  in
      univnames
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____15482) -> generalized_univ_names
        | (uu____15489,[]) -> explicit_univ_names
        | uu____15496 ->
            let uu____15505 =
              let uu____15511 =
                let uu____15513 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15513
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15511)
               in
            FStar_Errors.raise_error uu____15505 t.FStar_Syntax_Syntax.pos
  
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
      let univnames = gather_free_univnames env t  in
      (let uu____15535 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____15535
       then
         let uu____15540 = FStar_Syntax_Print.term_to_string t  in
         let uu____15542 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15540 uu____15542
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____15551 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____15551
        then
          let uu____15556 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____15556
        else ());
       (let gen = gen_univs env univs  in
        (let uu____15565 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____15565
         then
           let uu____15570 = FStar_Syntax_Print.term_to_string t  in
           let uu____15572 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15570 uu____15572
         else ());
        (let univs1 = check_universe_generalization univnames gen t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs1 t1  in
         (univs1, ts))))
  
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
        let uu____15656 =
          let uu____15658 =
            FStar_Util.for_all
              (fun uu____15672  ->
                 match uu____15672 with
                 | (uu____15682,uu____15683,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____15658  in
        if uu____15656
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15735 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____15735
              then
                let uu____15738 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15738
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____15745 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____15745
               then
                 let uu____15748 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15748
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____15766 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____15766 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____15800 =
             match uu____15800 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15837 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15837
                   then
                     let uu____15842 =
                       let uu____15844 =
                         let uu____15848 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____15848
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15844
                         (FStar_String.concat ", ")
                        in
                     let uu____15904 =
                       let uu____15906 =
                         let uu____15910 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15910
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15923 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15925 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15923
                                   uu____15925))
                          in
                       FStar_All.pipe_right uu____15906
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15842
                       uu____15904
                   else ());
                  (let univs1 =
                     let uu____15939 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____15951 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____15951) univs
                       uu____15939
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15958 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15958
                    then
                      let uu____15963 =
                        let uu____15965 =
                          let uu____15969 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____15969
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15965
                          (FStar_String.concat ", ")
                         in
                      let uu____16025 =
                        let uu____16027 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____16041 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____16043 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____16041
                                    uu____16043))
                           in
                        FStar_All.pipe_right uu____16027
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15963 uu____16025
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____16064 =
             let uu____16081 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____16081  in
           match uu____16064 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16171 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____16171
                 then ()
                 else
                   (let uu____16176 = lec_hd  in
                    match uu____16176 with
                    | (lb1,uu____16184,uu____16185) ->
                        let uu____16186 = lec2  in
                        (match uu____16186 with
                         | (lb2,uu____16194,uu____16195) ->
                             let msg =
                               let uu____16198 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16200 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16198 uu____16200
                                in
                             let uu____16203 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16203))
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
                 let uu____16271 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____16271
                 then ()
                 else
                   (let uu____16276 = lec_hd  in
                    match uu____16276 with
                    | (lb1,uu____16284,uu____16285) ->
                        let uu____16286 = lec2  in
                        (match uu____16286 with
                         | (lb2,uu____16294,uu____16295) ->
                             let msg =
                               let uu____16298 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16300 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16298 uu____16300
                                in
                             let uu____16303 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16303))
                  in
               let lecs1 =
                 let uu____16314 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____16367 = univs_and_uvars_of_lec this_lec  in
                        match uu____16367 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16314 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16477 = lec_hd  in
                   match uu____16477 with
                   | (lbname,e,c) ->
                       let uu____16487 =
                         let uu____16493 =
                           let uu____16495 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____16497 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____16499 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16495 uu____16497 uu____16499
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16493)
                          in
                       FStar_Errors.raise_error uu____16487 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____16521 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____16521 with
                         | FStar_Pervasives_Native.Some uu____16530 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16538 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____16542 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____16542 with
                              | (bs,kres) ->
                                  ((let uu____16562 =
                                      let uu____16563 =
                                        let uu____16566 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____16566
                                         in
                                      uu____16563.FStar_Syntax_Syntax.n  in
                                    match uu____16562 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16567
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____16571 =
                                          let uu____16573 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____16573  in
                                        if uu____16571
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16578 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16580 =
                                        let uu____16583 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____16586  ->
                                             FStar_Pervasives_Native.Some
                                               uu____16586) uu____16583
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____16580
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16594 ->
                                          let uu____16595 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____16595
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
               let gen_univs1 = gen_univs env univs  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____16698  ->
                         match uu____16698 with
                         | (lbname,e,c) ->
                             let uu____16744 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____16805 ->
                                   let uu____16818 = (e, c)  in
                                   (match uu____16818 with
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
                                                (fun uu____16858  ->
                                                   match uu____16858 with
                                                   | (x,uu____16864) ->
                                                       let uu____16865 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16865)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16883 =
                                                let uu____16885 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16885
                                                 in
                                              if uu____16883
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
                                          let uu____16894 =
                                            let uu____16895 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16895.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16894 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16920 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16920 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16931 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16935 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16935, gen_tvars))
                                in
                             (match uu____16744 with
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
        (let uu____17082 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____17082
         then
           let uu____17085 =
             let uu____17087 =
               FStar_List.map
                 (fun uu____17102  ->
                    match uu____17102 with
                    | (lb,uu____17111,uu____17112) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____17087 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____17085
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____17138  ->
                match uu____17138 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____17167 = gen env is_rec lecs  in
           match uu____17167 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17266  ->
                       match uu____17266 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17328 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____17328
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17376  ->
                           match uu____17376 with
                           | (l,us,e,c,gvs) ->
                               let uu____17410 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____17412 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____17414 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____17416 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17418 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17410 uu____17412 uu____17414
                                 uu____17416 uu____17418))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____17463  ->
                match uu____17463 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____17507 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____17507, t, c, gvs)) univnames_lecs
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
        let uu____17562 =
          let uu____17566 =
            let uu____17568 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____17568  in
          FStar_Pervasives_Native.Some uu____17566  in
        FStar_Profiling.profile
          (fun uu____17585  -> generalize' env is_rec lecs) uu____17562
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
          let check env2 t1 t21 =
            if env2.FStar_TypeChecker_Env.use_eq_strict
            then
              let uu____17642 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____17642 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17648 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____17648
                    (fun uu____17651  ->
                       FStar_Pervasives_Native.Some uu____17651)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17660 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____17660 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17666 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____17669  ->
                          FStar_Pervasives_Native.Some uu____17669)
                       uu____17666)
             in
          let uu____17670 = maybe_coerce_lc env1 e lc t2  in
          match uu____17670 with
          | (e1,lc1,g_c) ->
              let uu____17686 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____17686 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17695 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____17701 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____17695 uu____17701
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17710 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17710
                     then
                       let uu____17715 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17715
                     else ());
                    (let uu____17721 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____17721))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____17749 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____17749
         then
           let uu____17752 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17752
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____17766 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____17766 with
         | (c,g_c) ->
             let uu____17778 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____17778
             then
               let uu____17786 =
                 let uu____17788 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____17788  in
               (uu____17786, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____17796 =
                    let uu____17797 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____17797
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____17796
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____17798 = check_trivial_precondition env c1  in
                match uu____17798 with
                | (ct,vc,g_pre) ->
                    ((let uu____17814 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____17814
                      then
                        let uu____17819 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17819
                      else ());
                     (let uu____17824 =
                        let uu____17826 =
                          let uu____17827 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17827  in
                        discharge uu____17826  in
                      let uu____17828 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____17824, uu____17828)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17862 =
        match uu___8_17862 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____17872)::[] -> f fst
        | uu____17897 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17909 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17909
          (fun uu____17910  ->
             FStar_TypeChecker_Common.NonTrivial uu____17910)
         in
      let op_or_e e =
        let uu____17921 =
          let uu____17922 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17922  in
        FStar_All.pipe_right uu____17921
          (fun uu____17925  ->
             FStar_TypeChecker_Common.NonTrivial uu____17925)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17932  ->
             FStar_TypeChecker_Common.NonTrivial uu____17932)
         in
      let op_or_t t =
        let uu____17943 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____17943
          (fun uu____17946  ->
             FStar_TypeChecker_Common.NonTrivial uu____17946)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17953  ->
             FStar_TypeChecker_Common.NonTrivial uu____17953)
         in
      let short_op_ite uu___9_17959 =
        match uu___9_17959 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17969)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17996)::[] ->
            let uu____18037 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____18037
              (fun uu____18038  ->
                 FStar_TypeChecker_Common.NonTrivial uu____18038)
        | uu____18039 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____18051 =
          let uu____18059 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____18059)  in
        let uu____18067 =
          let uu____18077 =
            let uu____18085 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____18085)  in
          let uu____18093 =
            let uu____18103 =
              let uu____18111 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____18111)  in
            let uu____18119 =
              let uu____18129 =
                let uu____18137 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____18137)  in
              let uu____18145 =
                let uu____18155 =
                  let uu____18163 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____18163)  in
                [uu____18155; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____18129 :: uu____18145  in
            uu____18103 :: uu____18119  in
          uu____18077 :: uu____18093  in
        uu____18051 :: uu____18067  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____18225 =
            FStar_Util.find_map table
              (fun uu____18240  ->
                 match uu____18240 with
                 | (x,mk) ->
                     let uu____18257 = FStar_Ident.lid_equals x lid  in
                     if uu____18257
                     then
                       let uu____18262 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____18262
                     else FStar_Pervasives_Native.None)
             in
          (match uu____18225 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18266 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____18274 =
      let uu____18275 = FStar_Syntax_Util.un_uinst l  in
      uu____18275.FStar_Syntax_Syntax.n  in
    match uu____18274 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18280 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____18316)::uu____18317 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____18336 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____18345,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18346))::uu____18347 -> bs
      | uu____18365 ->
          let uu____18366 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____18366 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18370 =
                 let uu____18371 = FStar_Syntax_Subst.compress t  in
                 uu____18371.FStar_Syntax_Syntax.n  in
               (match uu____18370 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____18375) ->
                    let uu____18396 =
                      FStar_Util.prefix_until
                        (fun uu___10_18436  ->
                           match uu___10_18436 with
                           | (uu____18444,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18445)) ->
                               false
                           | uu____18450 -> true) bs'
                       in
                    (match uu____18396 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____18486,uu____18487) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____18559,uu____18560) ->
                         let uu____18633 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18654  ->
                                   match uu____18654 with
                                   | (x,uu____18663) ->
                                       let uu____18668 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____18668 "'"))
                            in
                         if uu____18633
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18714  ->
                                     match uu____18714 with
                                     | (x,i) ->
                                         let uu____18733 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____18733, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18744 -> bs))
  
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
            let uu____18773 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____18773
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
          let uu____18804 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____18804
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
        (let uu____18847 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18847
         then
           ((let uu____18852 = FStar_Ident.string_of_lid lident  in
             d uu____18852);
            (let uu____18854 = FStar_Ident.string_of_lid lident  in
             let uu____18856 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18854 uu____18856))
         else ());
        (let fv =
           let uu____18862 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18862
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
         let uu____18874 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2131_18876 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2131_18876.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2131_18876.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2131_18876.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2131_18876.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2131_18876.FStar_Syntax_Syntax.sigopts)
           }), uu____18874))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18894 =
        match uu___11_18894 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18897 -> false  in
      let reducibility uu___12_18905 =
        match uu___12_18905 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18912 -> false  in
      let assumption uu___13_18920 =
        match uu___13_18920 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18924 -> false  in
      let reification uu___14_18932 =
        match uu___14_18932 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18935 -> true
        | uu____18937 -> false  in
      let inferred uu___15_18945 =
        match uu___15_18945 with
        | FStar_Syntax_Syntax.Discriminator uu____18947 -> true
        | FStar_Syntax_Syntax.Projector uu____18949 -> true
        | FStar_Syntax_Syntax.RecordType uu____18955 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18965 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18978 -> false  in
      let has_eq uu___16_18986 =
        match uu___16_18986 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18990 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____19069 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____19076 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____19109 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____19109))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____19140 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____19140
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19160 ->
               let uu____19169 =
                 let uu____19171 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19177  ->
                           match uu___17_19177 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____19180 -> false))
                    in
                 Prims.op_Negation uu____19171  in
               if uu____19169
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19187 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19194 -> ()
           | uu____19207 ->
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
      let uu____19221 =
        let uu____19223 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19229  ->
                  match uu___18_19229 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____19232 -> false))
           in
        FStar_All.pipe_right uu____19223 Prims.op_Negation  in
      if uu____19221
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____19253 =
            let uu____19259 =
              let uu____19261 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19261 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19259)  in
          FStar_Errors.raise_error uu____19253 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____19279 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19287 =
            let uu____19289 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____19289  in
          if uu____19287 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____19300),uu____19301) ->
              ((let uu____19313 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____19313
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19322 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____19322
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19333 ->
              ((let uu____19343 =
                  let uu____19345 =
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
                  Prims.op_Negation uu____19345  in
                if uu____19343 then err'1 () else ());
               (let uu____19355 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19361  ->
                           match uu___19_19361 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____19364 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____19355
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19370 ->
              let uu____19377 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____19377 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19385 ->
              let uu____19392 =
                let uu____19394 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____19394  in
              if uu____19392 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19404 ->
              let uu____19405 =
                let uu____19407 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____19407  in
              if uu____19405 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19417 ->
              let uu____19430 =
                let uu____19432 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____19432  in
              if uu____19430 then err'1 () else ()
          | uu____19442 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____19481 =
          let uu____19482 = FStar_Syntax_Subst.compress t1  in
          uu____19482.FStar_Syntax_Syntax.n  in
        match uu____19481 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19486 ->
            let uu____19501 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____19501 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19510;
               FStar_Syntax_Syntax.index = uu____19511;
               FStar_Syntax_Syntax.sort = t2;_},uu____19513)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____19522) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____19548) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19554 -> false
      
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
        (let uu____19564 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____19564
         then
           let uu____19569 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19569
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
                let fail t =
                  let uu____19634 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____19634 r  in
                let uu____19644 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____19644 with
                | (uu____19653,signature) ->
                    let uu____19655 =
                      let uu____19656 = FStar_Syntax_Subst.compress signature
                         in
                      uu____19656.FStar_Syntax_Syntax.n  in
                    (match uu____19655 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19664) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19712 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____19728 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____19730 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____19732 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19728 uu____19730 uu____19732) r
                                 in
                              (match uu____19712 with
                               | (is,g) ->
                                   let uu____19745 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____19747 =
                                             let uu____19748 =
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
                                                 = uu____19748;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19747
                                            in
                                         let uu____19767 =
                                           let uu____19774 =
                                             let uu____19775 =
                                               let uu____19790 =
                                                 let uu____19799 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____19799]  in
                                               (uu____19790, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____19775
                                              in
                                           FStar_Syntax_Syntax.mk uu____19774
                                            in
                                         uu____19767
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19830 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____19830
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19839 =
                                           let uu____19844 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____19844
                                            in
                                         uu____19839
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____19745, g))
                          | uu____19853 -> fail signature)
                     | uu____19854 -> fail signature)
  
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
            let uu____19885 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19885
              (fun ed  ->
                 let uu____19893 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19893 u a_tm)
  
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
              let uu____19929 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19929 with
              | (uu____19934,sig_tm) ->
                  let fail t =
                    let uu____19942 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19942 r  in
                  let uu____19948 =
                    let uu____19949 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19949.FStar_Syntax_Syntax.n  in
                  (match uu____19948 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19953) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19976)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19998 -> fail sig_tm)
                   | uu____19999 -> fail sig_tm)
  
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
          (let uu____20030 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____20030
           then
             let uu____20035 = FStar_Syntax_Print.comp_to_string c  in
             let uu____20037 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____20035 uu____20037
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20044 =
             let uu____20055 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____20056 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____20055, (ct.FStar_Syntax_Syntax.result_typ), uu____20056)
              in
           match uu____20044 with
           | (u,a,c_is) ->
               let uu____20104 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____20104 with
                | (uu____20113,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20124 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____20126 = FStar_Ident.string_of_lid tgt  in
                      let uu____20128 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20124 uu____20126 s uu____20128
                       in
                    let uu____20131 =
                      let uu____20164 =
                        let uu____20165 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____20165.FStar_Syntax_Syntax.n  in
                      match uu____20164 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20229 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____20229 with
                           | (a_b::bs1,c2) ->
                               let uu____20289 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____20289, c2))
                      | uu____20377 ->
                          let uu____20378 =
                            let uu____20384 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20384)
                             in
                          FStar_Errors.raise_error uu____20378 r
                       in
                    (match uu____20131 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____20502 =
                           let uu____20509 =
                             let uu____20510 =
                               let uu____20511 =
                                 let uu____20518 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____20518, a)  in
                               FStar_Syntax_Syntax.NT uu____20511  in
                             [uu____20510]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20509
                             (fun b  ->
                                let uu____20535 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____20537 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____20539 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____20541 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20535 uu____20537 uu____20539
                                  uu____20541) r
                            in
                         (match uu____20502 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____20555 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____20555
                                then
                                  let uu____20560 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____20569 =
                                             let uu____20571 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____20571
                                              in
                                           Prims.op_Hat s uu____20569) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20560
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____20602 =
                                           let uu____20609 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____20609, t)  in
                                         FStar_Syntax_Syntax.NT uu____20602)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____20628 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____20628
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____20634 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____20634
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____20643 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20643)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____20645 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____20645
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____20649 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20649 r
                                   in
                                let fml =
                                  let uu____20654 =
                                    let uu____20659 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____20660 =
                                      let uu____20661 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____20661
                                       in
                                    (uu____20659, uu____20660)  in
                                  match uu____20654 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____20687 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____20687
                                 then
                                   let uu____20693 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20693
                                 else ());
                                (let c1 =
                                   let uu____20699 =
                                     let uu____20700 =
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
                                         uu____20700;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____20699
                                    in
                                 (let uu____20724 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____20724
                                  then
                                    let uu____20729 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20729
                                  else ());
                                 (let uu____20734 =
                                    let uu____20735 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____20736 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20735 uu____20736
                                     in
                                  (c1, uu____20734)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu20750 .
    'uuuuuu20750 ->
      FStar_Syntax_Syntax.sub_eff ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.typ ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun sub  ->
      fun u  ->
        fun a  ->
          fun e  ->
            let lift =
              let uu____20779 =
                let uu____20784 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____20784
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____20779 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____20827 =
                let uu____20828 =
                  let uu____20831 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____20831
                    FStar_Syntax_Subst.compress
                   in
                uu____20828.FStar_Syntax_Syntax.n  in
              match uu____20827 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20854::bs,uu____20856)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20896 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20896
                    FStar_Pervasives_Native.fst
              | uu____21002 ->
                  let uu____21003 =
                    let uu____21009 =
                      let uu____21011 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____21011
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____21009)  in
                  FStar_Errors.raise_error uu____21003
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____21038 = FStar_Syntax_Syntax.as_arg a  in
              let uu____21047 =
                let uu____21058 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____21094  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____21101 =
                  let uu____21112 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____21112]  in
                FStar_List.append uu____21058 uu____21101  in
              uu____21038 :: uu____21047  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____21183 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____21183 with
        | (uu____21188,t) ->
            let err n =
              let uu____21198 =
                let uu____21204 =
                  let uu____21206 = FStar_Ident.string_of_lid datacon  in
                  let uu____21208 = FStar_Util.string_of_int n  in
                  let uu____21210 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21206 uu____21208 uu____21210
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21204)
                 in
              let uu____21214 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____21198 uu____21214  in
            let uu____21215 =
              let uu____21216 = FStar_Syntax_Subst.compress t  in
              uu____21216.FStar_Syntax_Syntax.n  in
            (match uu____21215 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____21220) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21275  ->
                           match uu____21275 with
                           | (uu____21283,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____21292 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21326 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____21339 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____21339
      then
        let uu____21342 =
          let uu____21355 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21355
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21342;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____21390 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____21390 with
           | (uu____21399,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____21418 =
                 let uu____21419 =
                   let uu___2507_21420 = ct  in
                   let uu____21421 =
                     let uu____21432 =
                       let uu____21441 =
                         let uu____21442 =
                           let uu____21449 =
                             let uu____21450 =
                               let uu____21467 =
                                 let uu____21478 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____21478; wp]  in
                               (lift_t, uu____21467)  in
                             FStar_Syntax_Syntax.Tm_app uu____21450  in
                           FStar_Syntax_Syntax.mk uu____21449  in
                         uu____21442 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____21441
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____21432]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2507_21420.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2507_21420.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21421;
                     FStar_Syntax_Syntax.flags =
                       (uu___2507_21420.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____21419  in
               (uu____21418, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____21578 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____21578 with
           | (uu____21585,lift_t) ->
               let uu____21587 =
                 let uu____21594 =
                   let uu____21595 =
                     let uu____21612 =
                       let uu____21623 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____21632 =
                         let uu____21643 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____21652 =
                           let uu____21663 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____21663]  in
                         uu____21643 :: uu____21652  in
                       uu____21623 :: uu____21632  in
                     (lift_t, uu____21612)  in
                   FStar_Syntax_Syntax.Tm_app uu____21595  in
                 FStar_Syntax_Syntax.mk uu____21594  in
               uu____21587 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____21716 =
           let uu____21729 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____21729 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21716;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21765  ->
                        fun uu____21766  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____21789 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21789
  
let (update_env_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      fun n  ->
        fun p  ->
          fun ty  ->
            FStar_TypeChecker_Env.add_polymonadic_bind env m n p
              (fun env1  ->
                 fun c1  ->
                   fun bv_opt  ->
                     fun c2  ->
                       fun flags  ->
                         fun r  ->
                           mk_indexed_bind env1 m n p ty c1 bv_opt c2 flags r)
  