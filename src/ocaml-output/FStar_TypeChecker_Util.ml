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
  
type lift_context =
  | Lift_for_bind 
  | Lift_for_match 
let (uu___is_Lift_for_bind : lift_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lift_for_bind  -> true | uu____2185 -> false
  
let (uu___is_Lift_for_match : lift_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lift_for_match  -> true | uu____2196 -> false
  
let (lift_comps_sep_guards :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          lift_context ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t *
              FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun lift_context1  ->
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2250 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2250 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2278 = lift_comp env c11 lift1  in
                (match uu____2278 with
                 | (c12,g1) ->
                     let uu____2295 =
                       if lift_context1 = Lift_for_match
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
                          let uu____2334 = lift_comp env_x c21 lift2  in
                          match uu____2334 with
                          | (c22,g2) ->
                              let uu____2345 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2345))
                        in
                     (match uu____2295 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2392 =
                  let uu____2393 =
                    let uu____2399 =
                      let uu____2401 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2403 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2401
                        uu____2403
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2399)
                     in
                  FStar_Errors.raise_error uu____2393 rng  in
                ((let uu____2418 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2418
                  then
                    let uu____2423 =
                      let uu____2425 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2425
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2427 =
                      let uu____2429 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2429
                        FStar_Syntax_Print.comp_to_string
                       in
                    FStar_Util.print3
                      "Lifting comps %s and %s with lift context %s{\n"
                      uu____2423 uu____2427
                      (match lift_context1 with
                       | Lift_for_bind  -> "bind"
                       | Lift_for_match  -> "match")
                  else ());
                 if lift_context1 = Lift_for_bind
                 then err ()
                 else
                   (let bind_with_return ct ret_eff f_bind =
                      let x_bv =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          ct.FStar_Syntax_Syntax.result_typ
                         in
                      let uu____2488 =
                        let uu____2493 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2494 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2495 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2496 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2493 uu____2494 uu____2495
                          ct.FStar_Syntax_Syntax.result_typ uu____2496 rng
                         in
                      match uu____2488 with
                      | (c_ret,g_ret) ->
                          let uu____2503 =
                            let uu____2508 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2508 [] rng
                             in
                          (match uu____2503 with
                           | (c,g_bind) ->
                               let uu____2515 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2515))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2560 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2560
                      then
                        let uu____2596 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2596 with
                        | (p,f_bind) ->
                            let uu____2663 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2663
                             then
                               let uu____2676 = bind_with_return c12 p f_bind
                                  in
                               match uu____2676 with
                               | (c13,g) ->
                                   let uu____2693 =
                                     let uu____2702 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2702, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2693
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2731 =
                      let uu____2742 = try_lift c11 c21  in
                      match uu____2742 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2783 = try_lift c21 c11  in
                          (match uu____2783 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2731 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2840 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2840
                          then
                            let uu____2845 = FStar_Ident.string_of_lid p  in
                            let uu____2847 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2849 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2845 uu____2847 uu____2849
                          else ());
                         (p, c12, c22, g1, g2))))
  
let (lift_comps :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
          lift_context ->
            (FStar_Ident.lident * FStar_Syntax_Syntax.comp *
              FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        fun b  ->
          fun lift_context1  ->
            let uu____2900 = lift_comps_sep_guards env c1 c2 b lift_context1
               in
            match uu____2900 with
            | (l,c11,c21,g1,g2) ->
                let uu____2924 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2924)
  
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
          let uu____2980 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2980
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2992 =
      let uu____2993 = FStar_Syntax_Subst.compress t  in
      uu____2993.FStar_Syntax_Syntax.n  in
    match uu____2992 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2997 -> true
    | uu____3013 -> false
  
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
              let uu____3083 =
                let uu____3085 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3085  in
              if uu____3083
              then f
              else (let uu____3092 = reason1 ()  in label uu____3092 r f)
  
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
            let uu___398_3113 = g  in
            let uu____3114 =
              let uu____3115 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3115  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3114;
              FStar_TypeChecker_Common.deferred =
                (uu___398_3113.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___398_3113.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___398_3113.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3136 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3136
        then c
        else
          (let uu____3141 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3141
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3183 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3183 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3211 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3211]  in
                       let us =
                         let uu____3233 =
                           let uu____3236 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3236]  in
                         u_res :: uu____3233  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3242 =
                         let uu____3247 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close
                            in
                         let uu____3248 =
                           let uu____3249 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3258 =
                             let uu____3269 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3278 =
                               let uu____3289 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3289]  in
                             uu____3269 :: uu____3278  in
                           uu____3249 :: uu____3258  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3247 uu____3248
                          in
                       uu____3242 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3331 = destruct_wp_comp c1  in
              match uu____3331 with
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
                let uu____3371 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3371
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
                  let uu____3421 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3421
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3434  ->
            match uu___0_3434 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3437 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3462 =
            let uu____3465 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3465 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3462
            (fun c  ->
               (let uu____3489 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3489) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3493 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3493)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3504 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3504 with
                | (head,uu____3521) ->
                    let uu____3542 =
                      let uu____3543 = FStar_Syntax_Util.un_uinst head  in
                      uu____3543.FStar_Syntax_Syntax.n  in
                    (match uu____3542 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3548 =
                           let uu____3550 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3550
                            in
                         Prims.op_Negation uu____3548
                     | uu____3551 -> true)))
              &&
              (let uu____3554 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3554)
  
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
            let uu____3582 =
              let uu____3584 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3584  in
            if uu____3582
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3591 = FStar_Syntax_Util.is_unit t  in
               if uu____3591
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
                    let uu____3600 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3600
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3606 =
                         let uu____3607 =
                           let uu____3612 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3613 =
                             let uu____3614 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3623 =
                               let uu____3634 = FStar_Syntax_Syntax.as_arg v
                                  in
                               [uu____3634]  in
                             uu____3614 :: uu____3623  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3612
                             uu____3613
                            in
                         uu____3607 FStar_Pervasives_Native.None
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3606)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3668 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3668
           then
             let uu____3673 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3675 = FStar_Syntax_Print.term_to_string v  in
             let uu____3677 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3673 uu____3675 uu____3677
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
                      (let uu____3750 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3750
                       then
                         let uu____3755 =
                           let uu____3757 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3757  in
                         let uu____3758 =
                           let uu____3760 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3760  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3755 uu____3758
                       else ());
                      (let uu____3764 =
                         let uu____3771 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3772 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3773 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3771, uu____3772, uu____3773)  in
                       match uu____3764 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3781 =
                             let uu____3792 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3793 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3792,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3793)
                              in
                           (match uu____3781 with
                            | (u1,t1,is1) ->
                                let uu____3827 =
                                  let uu____3838 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3839 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3838,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3839)
                                   in
                                (match uu____3827 with
                                 | (u2,t2,is2) ->
                                     let uu____3873 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3873 with
                                      | (uu____3882,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3897 =
                                              let uu____3899 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3899 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3897)
                                             in
                                          let uu____3903 =
                                            let uu____3948 =
                                              let uu____3949 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3949.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3948 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4025 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4025 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4110 =
                                                       let uu____4137 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4137
                                                         (fun uu____4222  ->
                                                            match uu____4222
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4303
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4316
                                                                  =
                                                                  let uu____4323
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4323
                                                                   in
                                                                (l1,
                                                                  uu____4303,
                                                                  uu____4316))
                                                        in
                                                     (match uu____4110 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4483 ->
                                                let uu____4484 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4484 r1
                                             in
                                          (match uu____3903 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4609 =
                                                 let uu____4616 =
                                                   let uu____4617 =
                                                     let uu____4618 =
                                                       let uu____4625 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4625, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4618
                                                      in
                                                   let uu____4636 =
                                                     let uu____4639 =
                                                       let uu____4640 =
                                                         let uu____4647 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4647, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4640
                                                        in
                                                     [uu____4639]  in
                                                   uu____4617 :: uu____4636
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4616
                                                   (fun b1  ->
                                                      let uu____4663 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4665 =
                                                        let uu____4667 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4669 =
                                                          FStar_Ident.string_of_lid
                                                            n
                                                           in
                                                        let uu____4671 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4667
                                                          uu____4669
                                                          uu____4671
                                                         in
                                                      let uu____4674 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4663 uu____4665
                                                        uu____4674) r1
                                                  in
                                               (match uu____4609 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4711 =
                                                               let uu____4718
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4718,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4711)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4745 =
                                                          let uu____4748 =
                                                            let uu____4749 =
                                                              let uu____4750
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4750.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4749
                                                             in
                                                          let uu____4759 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4748
                                                            uu____4759 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4745
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4772
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4772)
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
                                                        let uu____4791 =
                                                          let uu____4792 =
                                                            let uu____4795 =
                                                              let uu____4796
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4796.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4795
                                                             in
                                                          uu____4792.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4791 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4829 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4829
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4839
                                                                    =
                                                                    let uu____4846
                                                                    =
                                                                    let uu____4847
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4847
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4868
                                                                    =
                                                                    let uu____4871
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4871
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4846,
                                                                    uu____4868)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4839
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4885
                                                                   =
                                                                   let uu____4888
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4889
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4888
                                                                    uu____4889
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4885
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4895 ->
                                                            failwith
                                                              "imspossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4912 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4920
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4920)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4912
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4934 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4934
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4936 =
                                                        let uu____4941 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4942 =
                                                          let uu____4943 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4943
                                                           in
                                                        (uu____4941,
                                                          uu____4942)
                                                         in
                                                      match uu____4936 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4969 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4970 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4969 uu____4970
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4973 =
                                                        let uu____4974 =
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
                                                            = uu____4974;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4973
                                                       in
                                                    ((let uu____4994 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4994
                                                      then
                                                        let uu____4999 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4999
                                                      else ());
                                                     (let uu____5004 =
                                                        let uu____5005 =
                                                          let uu____5008 =
                                                            let uu____5011 =
                                                              let uu____5014
                                                                =
                                                                let uu____5017
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____5017]
                                                                 in
                                                              g_guard ::
                                                                uu____5014
                                                               in
                                                            f_guard ::
                                                              uu____5011
                                                             in
                                                          g_uvars ::
                                                            uu____5008
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____5005
                                                         in
                                                      (c, uu____5004)))))))))
  
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
                let uu____5062 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5088 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5088 with
                  | (a,kwp) ->
                      let uu____5119 = destruct_wp_comp ct1  in
                      let uu____5126 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5119, uu____5126)
                   in
                match uu____5062 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5179 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5179]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5199 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5199]
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
                      let uu____5246 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5255 =
                        let uu____5266 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5275 =
                          let uu____5286 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5295 =
                            let uu____5306 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5315 =
                              let uu____5326 =
                                let uu____5335 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5335  in
                              [uu____5326]  in
                            uu____5306 :: uu____5315  in
                          uu____5286 :: uu____5295  in
                        uu____5266 :: uu____5275  in
                      uu____5246 :: uu____5255  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5388 =
                        let uu____5393 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5393 wp_args  in
                      uu____5388 FStar_Pervasives_Native.None
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
              let uu____5441 =
                let uu____5446 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5447 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5446, uu____5447)  in
              match uu____5441 with
              | (ct1,ct2) ->
                  let uu____5454 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5454 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5505 = lift_comps env c1 c2 b Lift_for_bind
                          in
                       (match uu____5505 with
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
            let uu____5969 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5969
            then (lc, g0)
            else
              (let flags =
                 let uu____5981 =
                   let uu____5989 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5989
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5981 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6019 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6027  ->
                               match uu___3_6027 with
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
                               | uu____6030 -> []))
                        in
                     FStar_List.append flags uu____6019
                  in
               let strengthen uu____6040 =
                 let uu____6041 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6041 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6060 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6060 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6067 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6067
                              then
                                let uu____6071 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6073 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6071 uu____6073
                              else ());
                             (let uu____6078 =
                                strengthen_comp env reason c f flags  in
                              match uu____6078 with
                              | (c1,g_s) ->
                                  let uu____6089 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6089))))
                  in
               let uu____6090 =
                 let uu____6091 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6091
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6090,
                 (let uu___709_6093 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___709_6093.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___709_6093.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___709_6093.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6102  ->
            match uu___4_6102 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6106 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6135 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6135
          then e
          else
            (let uu____6142 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6145 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6145)
                in
             if uu____6142
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
                | uu____6215 -> false  in
              if is_unit
              then
                let uu____6222 =
                  let uu____6224 =
                    let uu____6225 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6225
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6224
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6222
                 then
                   let uu____6234 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6234 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6250 = close_wp_comp env [x] c  in
                    (uu____6250, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6253 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6281  ->
            match uu____6281 with
            | (b,lc2) ->
                let debug f =
                  let uu____6301 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6301 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6314 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6314
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6324 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6324
                       then
                         let uu____6329 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6329
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6336 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6336
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6345 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6345
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6352 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6352
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6368 =
                  let uu____6369 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6369
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6377 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6377, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6380 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6380 with
                     | (c1,g_c1) ->
                         let uu____6391 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6391 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6403 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6406 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6406
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6403
                                 in
                              (debug
                                 (fun uu____6432  ->
                                    let uu____6433 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6435 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6440 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6433 uu____6435 uu____6440);
                               (let aux uu____6458 =
                                  let uu____6459 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6459
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6490
                                        ->
                                        let uu____6491 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6491
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6523 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6523
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6570 =
                                  let aux_with_trivial_guard uu____6600 =
                                    let uu____6601 = aux ()  in
                                    match uu____6601 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6659 =
                                    let uu____6661 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6661  in
                                  if uu____6659
                                  then
                                    let uu____6677 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6677
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6704 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6704))
                                  else
                                    (let uu____6721 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6721
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___812_6752 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___812_6752.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___812_6752.FStar_Syntax_Syntax.index);
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
                                           let uu____6783 =
                                             let uu____6788 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6788
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6783 with
                                            | (c21,g_close) ->
                                                let uu____6809 =
                                                  let uu____6817 =
                                                    let uu____6818 =
                                                      let uu____6821 =
                                                        let uu____6824 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6824; g_close]
                                                         in
                                                      g_c1 :: uu____6821  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6818
                                                     in
                                                  (c21, uu____6817, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6809)
                                       | (uu____6837,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6849 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6849 with
                                            | (c21,g_close) ->
                                                let uu____6872 =
                                                  let uu____6880 =
                                                    let uu____6881 =
                                                      let uu____6884 =
                                                        let uu____6887 =
                                                          let uu____6888 =
                                                            let uu____6889 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6889]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6888
                                                            g_c2
                                                           in
                                                        [uu____6887; g_close]
                                                         in
                                                      g_c1 :: uu____6884  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6881
                                                     in
                                                  (c21, uu____6880,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6872)
                                       | (uu____6918,uu____6919) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6934 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6934
                                        then
                                          let uu____6949 =
                                            let uu____6957 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6957, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6949
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6970 = try_simplify ()  in
                                match uu____6970 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____7005  ->
                                          let uu____7006 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7006);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____7022  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7053 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7053 with
                                        | (c,g_bind) ->
                                            let uu____7064 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7064)
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
                                        let uu____7091 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7091 with
                                        | (m,uu____7103,lift2) ->
                                            let uu____7105 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7105 with
                                             | (c23,g2) ->
                                                 let uu____7116 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7116 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7132 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7132
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7142 =
                                                          let uu____7147 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7148 =
                                                            let uu____7149 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7158 =
                                                              let uu____7169
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7169]
                                                               in
                                                            uu____7149 ::
                                                              uu____7158
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7147
                                                            uu____7148
                                                           in
                                                        uu____7142
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7202 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7202 with
                                                       | (c,g_s) ->
                                                           let uu____7217 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7217))))
                                         in
                                      let uu____7218 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7234 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7234, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7218 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7250 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7250
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7259 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7259
                                             then
                                               (debug
                                                  (fun uu____7273  ->
                                                     let uu____7274 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7276 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7274 uu____7276);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7283 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7283
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7288 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7291 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7291)
                                                   in
                                                if uu____7288
                                                then
                                                  let e1' =
                                                    let uu____7316 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7316
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7328  ->
                                                        let uu____7329 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7331 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7329
                                                          uu____7331);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7346  ->
                                                        let uu____7347 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7349 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7347
                                                          uu____7349);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7356 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7356
                                                       in
                                                    let uu____7357 =
                                                      let uu____7362 =
                                                        let uu____7363 =
                                                          let uu____7364 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7364]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7363
                                                         in
                                                      weaken_comp uu____7362
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7357 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7390 =
                                                            let uu____7391 =
                                                              let uu____7392
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7392]
                                                               in
                                                            let uu____7411 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7391
                                                              uu____7411
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7390
                                                           in
                                                        let uu____7412 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7412
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7423 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7423))))))
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
      | uu____7440 -> g2
  
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
            (let uu____7464 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7464)
           in
        let flags =
          if should_return1
          then
            let uu____7472 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7472
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7490 =
          let uu____7491 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7491 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7504 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7504
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7512 =
                  let uu____7514 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7514  in
                (if uu____7512
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___937_7523 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___937_7523.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___937_7523.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___937_7523.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7524 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7524, g_c)
                 else
                   (let uu____7527 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7527, g_c)))
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
                   let uu____7538 =
                     let uu____7539 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7539
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7538
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7542 =
                   let uu____7547 =
                     let uu____7548 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7548
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7547  in
                 match uu____7542 with
                 | (bind_c,g_bind) ->
                     let uu____7557 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7558 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7557, uu____7558))
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
            fun uu____7594  ->
              match uu____7594 with
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
                    let uu____7606 =
                      ((let uu____7610 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7610) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7606
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7628 =
        let uu____7629 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7629  in
      FStar_Syntax_Syntax.fvar uu____7628 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7679 =
                    let uu____7684 =
                      let uu____7685 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7685 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7684 [u_a]
                     in
                  match uu____7679 with
                  | (uu____7696,conjunction) ->
                      let uu____7698 =
                        let uu____7707 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7722 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7707, uu____7722)  in
                      (match uu____7698 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7768 =
                               let uu____7770 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7770 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7768)
                              in
                           let uu____7774 =
                             let uu____7819 =
                               let uu____7820 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7820.FStar_Syntax_Syntax.n  in
                             match uu____7819 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7869) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7901 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7901 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7973 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7973 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8121 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8121)))
                             | uu____8154 ->
                                 let uu____8155 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8155 r
                              in
                           (match uu____7774 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8280 =
                                  let uu____8287 =
                                    let uu____8288 =
                                      let uu____8289 =
                                        let uu____8296 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8296, a)  in
                                      FStar_Syntax_Syntax.NT uu____8289  in
                                    [uu____8288]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8287
                                    (fun b  ->
                                       let uu____8312 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8314 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8316 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8312 uu____8314 uu____8316) r
                                   in
                                (match uu____8280 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8354 =
                                                let uu____8361 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8361, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8354) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8400 =
                                           let uu____8401 =
                                             let uu____8404 =
                                               let uu____8405 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8405.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8404
                                              in
                                           uu____8401.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8400 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8416,uu____8417::is) ->
                                             let uu____8459 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8459
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8492 ->
                                             let uu____8493 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8493 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8509 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8509)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8514 =
                                           let uu____8515 =
                                             let uu____8518 =
                                               let uu____8519 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8519.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8518
                                              in
                                           uu____8515.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8514 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8530,uu____8531::is) ->
                                             let uu____8573 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8573
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8606 ->
                                             let uu____8607 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8607 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8623 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8623)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8628 =
                                         let uu____8629 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8629.FStar_Syntax_Syntax.n  in
                                       match uu____8628 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8634,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8689 ->
                                           let uu____8690 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8690 r
                                        in
                                     let uu____8699 =
                                       let uu____8700 =
                                         let uu____8701 =
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
                                             uu____8701;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8700
                                        in
                                     let uu____8724 =
                                       let uu____8725 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8725 g_guard
                                        in
                                     (uu____8699, uu____8724))))
  
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
                fun uu____8770  ->
                  let if_then_else =
                    let uu____8776 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8776 FStar_Util.must  in
                  let uu____8783 = destruct_wp_comp ct1  in
                  match uu____8783 with
                  | (uu____8794,uu____8795,wp_t) ->
                      let uu____8797 = destruct_wp_comp ct2  in
                      (match uu____8797 with
                       | (uu____8808,uu____8809,wp_e) ->
                           let wp =
                             let uu____8814 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8815 =
                               let uu____8820 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else
                                  in
                               let uu____8821 =
                                 let uu____8822 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8831 =
                                   let uu____8842 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8851 =
                                     let uu____8862 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8871 =
                                       let uu____8882 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8882]  in
                                     uu____8862 :: uu____8871  in
                                   uu____8842 :: uu____8851  in
                                 uu____8822 :: uu____8831  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8820
                                 uu____8821
                                in
                             uu____8815 FStar_Pervasives_Native.None
                               uu____8814
                              in
                           let uu____8931 = mk_comp ed u_a a wp []  in
                           (uu____8931, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____8985 =
              let uu____8986 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8986]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8985  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9033  ->
                   match uu____9033 with
                   | (uu____9047,eff_label,uu____9049,uu____9050) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9063 =
            let uu____9071 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9109  ->
                      match uu____9109 with
                      | (uu____9124,uu____9125,flags,uu____9127) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9144  ->
                                  match uu___5_9144 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9147 -> false))))
               in
            if uu____9071
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9063 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9184 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9186 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9186
                then
                  let uu____9193 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9193, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9200 =
                         let uu____9209 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9209]  in
                       let uu____9228 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9200 uu____9228  in
                     let kwp =
                       let uu____9234 =
                         let uu____9243 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9243]  in
                       let uu____9262 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9234 uu____9262  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9269 =
                         let uu____9270 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9270]  in
                       let uu____9289 =
                         let uu____9292 =
                           let uu____9299 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9299
                            in
                         let uu____9300 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9292 uu____9300  in
                       FStar_Syntax_Util.abs uu____9269 uu____9289
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
                     let uu____9324 =
                       should_not_inline_whole_match ||
                         (let uu____9327 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9327)
                        in
                     if uu____9324 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9339 =
                       let uu____9352 =
                         let uu____9357 =
                           let uu____9368 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9412  ->
                                     match uu____9412 with
                                     | (g,uu____9427,uu____9428,uu____9429)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9368
                             (FStar_List.fold_left
                                (fun uu____9473  ->
                                   fun g  ->
                                     match uu____9473 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9514 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9514
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9357
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9352
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9339
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9615 =
                     FStar_List.fold_right2
                       (fun uu____9678  ->
                          fun bcond  ->
                            fun uu____9680  ->
                              match (uu____9678, uu____9680) with
                              | ((g,eff_label,uu____9740,cthen),(uu____9742,celse,g_comp))
                                  ->
                                  let uu____9789 =
                                    let uu____9794 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9794
                                     in
                                  (match uu____9789 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9806 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9806
                                          in
                                       let uu____9807 =
                                         let uu____9818 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             Lift_for_match
                                            in
                                         match uu____9818 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9845 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9846 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9845, uu____9846,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9807 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____9897 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____9897
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____9932 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____9932
                                               in
                                            let g_lift_else1 =
                                              let uu____9934 =
                                                let uu____9935 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____9935
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____9934
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____9939 =
                                              let uu____9944 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____9944
                                               in
                                            (match uu____9939 with
                                             | (c,g_conjunction) ->
                                                 let uu____9955 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____9955)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9615 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____9972 =
                           let uu____9973 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____9973]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____9972
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____10016::[] -> (comp, g_comp1)
                        | uu____10059 ->
                            let uu____10076 =
                              let uu____10078 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10078
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10076
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
                               let uu____10091 = destruct_wp_comp comp1  in
                               match uu____10091 with
                               | (uu____10102,uu____10103,wp) ->
                                   let ite_wp =
                                     let uu____10106 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10106
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10116 =
                                       let uu____10121 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10122 =
                                         let uu____10123 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10132 =
                                           let uu____10143 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10143]  in
                                         uu____10123 :: uu____10132  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10121 uu____10122
                                        in
                                     uu____10116 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10176 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10176, g_comp1))))
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
          let uu____10211 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10211 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10227 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10233 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10227 uu____10233
              else
                (let uu____10242 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10248 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10242 uu____10248)
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
          let uu____10273 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10273
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10276 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10276
        then u_res
        else
          (let is_total =
             let uu____10283 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10283
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10294 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10294 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10297 =
                    let uu____10303 =
                      let uu____10305 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10305
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10303)
                     in
                  FStar_Errors.raise_error uu____10297
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
      let uu____10329 = destruct_wp_comp ct  in
      match uu____10329 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10348 = FStar_TypeChecker_Env.get_range env  in
            let uu____10349 =
              let uu____10354 =
                let uu____10355 =
                  let uu____10356 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10356 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10355
                 in
              let uu____10363 =
                let uu____10364 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10373 =
                  let uu____10384 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10384]  in
                uu____10364 :: uu____10373  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10354 uu____10363  in
            uu____10349 FStar_Pervasives_Native.None uu____10348  in
          let uu____10417 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10417)
  
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
                  let uu____10472 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10472 with
                  | FStar_Pervasives_Native.Some uu____10487 ->
                      ((let uu____10505 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10505
                        then
                          let uu____10509 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10509
                        else ());
                       (let coercion =
                          let uu____10515 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10515
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10522 =
                            let uu____10523 =
                              let uu____10524 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10524
                               in
                            (FStar_Pervasives_Native.None, uu____10523)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10522
                           in
                        let e1 =
                          let uu____10530 =
                            let uu____10535 =
                              let uu____10536 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10536]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10535
                             in
                          uu____10530 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10570 =
                          let uu____10576 =
                            let uu____10578 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10578
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10576)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10570);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10597 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10615 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10626 -> false 
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
      let uu____10650 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10650 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10695 =
              let uu____10710 =
                let uu____10711 = FStar_Syntax_Subst.compress h1  in
                uu____10711.FStar_Syntax_Syntax.n  in
              (uu____10710, args)  in
            match uu____10695 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10758,uu____10759) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10792) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10813,branches),uu____10815) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10879 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10880 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10880 with
                               | (uu____10881,uu____10882,br_body) ->
                                   let uu____10900 =
                                     let uu____10901 =
                                       let uu____10906 =
                                         let uu____10907 =
                                           let uu____10910 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10910
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10907
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10906  in
                                     FStar_All.pipe_right br_body uu____10901
                                      in
                                   (match uu____10900 with
                                    | No  -> No
                                    | uu____10921 -> Maybe))) No)
            | uu____10922 -> No  in
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
            (((let uu____10974 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10974) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10993 =
                 let uu____10994 = FStar_Syntax_Subst.compress t1  in
                 uu____10994.FStar_Syntax_Syntax.n  in
               match uu____10993 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10999 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11009 =
                 let uu____11010 = FStar_Syntax_Subst.compress t1  in
                 uu____11010.FStar_Syntax_Syntax.n  in
               match uu____11009 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11015 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11026 =
                 let uu____11027 = FStar_Syntax_Subst.compress t2  in
                 uu____11027.FStar_Syntax_Syntax.n  in
               match uu____11026 with
               | FStar_Syntax_Syntax.Tm_type uu____11031 -> true
               | uu____11033 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11036 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11036 with
             | (head,args) ->
                 ((let uu____11086 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11086
                   then
                     let uu____11090 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11092 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11094 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11096 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11090 uu____11092 uu____11094 uu____11096
                   else ());
                  (let mk_erased u t =
                     let uu____11114 =
                       let uu____11117 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11117 [u]  in
                     let uu____11118 =
                       let uu____11129 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11129]  in
                     FStar_Syntax_Util.mk_app uu____11114 uu____11118  in
                   let uu____11154 =
                     let uu____11169 =
                       let uu____11170 = FStar_Syntax_Util.un_uinst head  in
                       uu____11170.FStar_Syntax_Syntax.n  in
                     (uu____11169, args)  in
                   match uu____11154 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11208 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11208 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11248 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11248 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11288 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11288 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11328 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11328 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11349 ->
                       let uu____11364 =
                         let uu____11369 = check_erased env res_typ  in
                         let uu____11370 = check_erased env exp_t  in
                         (uu____11369, uu____11370)  in
                       (match uu____11364 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11379 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11379 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11390 =
                                   let uu____11395 =
                                     let uu____11396 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11396]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11395
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11390 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11431 =
                              let uu____11436 =
                                let uu____11437 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11437]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11436
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11431 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11470 ->
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
        let uu____11505 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11505 with
        | (hd,args) ->
            let uu____11554 =
              let uu____11569 =
                let uu____11570 = FStar_Syntax_Subst.compress hd  in
                uu____11570.FStar_Syntax_Syntax.n  in
              (uu____11569, args)  in
            (match uu____11554 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11608 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____11635  ->
                      FStar_Pervasives_Native.Some uu____11635) uu____11608
             | uu____11636 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11689 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11689
           then
             let uu____11692 = FStar_Syntax_Print.term_to_string e  in
             let uu____11694 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11696 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11692 uu____11694 uu____11696
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11706 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11706 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11731 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11757 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11757, false)
             else
               (let uu____11767 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11767, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11780) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11792 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11792
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1379_11808 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1379_11808.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1379_11808.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1379_11808.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____11815 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11815 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11831 =
                      let uu____11832 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11832 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11852 =
                            let uu____11854 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11854 = FStar_Syntax_Util.Equal  in
                          if uu____11852
                          then
                            ((let uu____11861 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11861
                              then
                                let uu____11865 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11867 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11865 uu____11867
                              else ());
                             (let uu____11872 = set_result_typ c  in
                              (uu____11872, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11879 ->
                                   true
                               | uu____11887 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11896 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11896
                                  in
                               let lc1 =
                                 let uu____11898 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11899 =
                                   let uu____11900 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11900)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11898 uu____11899
                                  in
                               ((let uu____11904 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11904
                                 then
                                   let uu____11908 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11910 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11912 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11914 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11908 uu____11910 uu____11912
                                     uu____11914
                                 else ());
                                (let uu____11919 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11919 with
                                 | (c1,g_lc) ->
                                     let uu____11930 = set_result_typ c1  in
                                     let uu____11931 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11930, uu____11931)))
                             else
                               ((let uu____11935 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11935
                                 then
                                   let uu____11939 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11941 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11939 uu____11941
                                 else ());
                                (let uu____11946 = set_result_typ c  in
                                 (uu____11946, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1416_11950 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1416_11950.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1416_11950.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1416_11950.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11960 =
                      let uu____11961 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11961
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11971 =
                           let uu____11972 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11972.FStar_Syntax_Syntax.n  in
                         match uu____11971 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11979,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11981;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11982;_},uu____11983)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1432_12009 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1432_12009.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1432_12009.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1432_12009.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12010 ->
                             let uu____12011 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12011 with
                              | (c,g_c) ->
                                  ((let uu____12023 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12023
                                    then
                                      let uu____12027 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12029 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12031 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12033 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12027 uu____12029 uu____12031
                                        uu____12033
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
                                        let uu____12046 =
                                          let uu____12051 =
                                            let uu____12052 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12052]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12051
                                           in
                                        uu____12046
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12079 =
                                      let uu____12084 =
                                        FStar_All.pipe_left
                                          (fun uu____12105  ->
                                             FStar_Pervasives_Native.Some
                                               uu____12105)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12106 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12107 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12108 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12084
                                        uu____12106 e uu____12107 uu____12108
                                       in
                                    match uu____12079 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1450_12116 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1450_12116.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1450_12116.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12118 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12118
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12121 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12121 with
                                         | (c2,g_lc) ->
                                             ((let uu____12133 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12133
                                               then
                                                 let uu____12137 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12137
                                               else ());
                                              (let uu____12142 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12142))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12151  ->
                              match uu___6_12151 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12154 -> []))
                       in
                    let lc1 =
                      let uu____12156 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12156 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1466_12158 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1466_12158.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1466_12158.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1466_12158.FStar_TypeChecker_Common.implicits)
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
        let uu____12194 =
          let uu____12197 =
            let uu____12202 =
              let uu____12203 =
                let uu____12212 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12212  in
              [uu____12203]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12202  in
          uu____12197 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12194  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12235 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12235
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12254 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12270 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12287 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12287
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12303)::(ens,uu____12305)::uu____12306 ->
                    let uu____12349 =
                      let uu____12352 = norm req  in
                      FStar_Pervasives_Native.Some uu____12352  in
                    let uu____12353 =
                      let uu____12354 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____12354  in
                    (uu____12349, uu____12353)
                | uu____12357 ->
                    let uu____12368 =
                      let uu____12374 =
                        let uu____12376 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12376
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12374)
                       in
                    FStar_Errors.raise_error uu____12368
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12396)::uu____12397 ->
                    let uu____12424 =
                      let uu____12429 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12429
                       in
                    (match uu____12424 with
                     | (us_r,uu____12461) ->
                         let uu____12462 =
                           let uu____12467 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12467
                            in
                         (match uu____12462 with
                          | (us_e,uu____12499) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12502 =
                                  let uu____12503 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12503
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12502
                                  us_r
                                 in
                              let as_ens =
                                let uu____12505 =
                                  let uu____12506 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12506
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12505
                                  us_e
                                 in
                              let req =
                                let uu____12510 =
                                  let uu____12515 =
                                    let uu____12516 =
                                      let uu____12527 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12527]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12516
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12515
                                   in
                                uu____12510 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12567 =
                                  let uu____12572 =
                                    let uu____12573 =
                                      let uu____12584 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12584]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12573
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12572
                                   in
                                uu____12567 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12621 =
                                let uu____12624 = norm req  in
                                FStar_Pervasives_Native.Some uu____12624  in
                              let uu____12625 =
                                let uu____12626 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____12626  in
                              (uu____12621, uu____12625)))
                | uu____12629 -> failwith "Impossible"))
  
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
        (let uu____12668 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12668
         then
           let uu____12673 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12675 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12673
             uu____12675
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
          (let uu____12734 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12734
           then
             let uu____12739 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12741 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12739
               uu____12741
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12752 =
      let uu____12754 =
        let uu____12755 = FStar_Syntax_Subst.compress t  in
        uu____12755.FStar_Syntax_Syntax.n  in
      match uu____12754 with
      | FStar_Syntax_Syntax.Tm_app uu____12759 -> false
      | uu____12777 -> true  in
    if uu____12752
    then t
    else
      (let uu____12782 = FStar_Syntax_Util.head_and_args t  in
       match uu____12782 with
       | (head,args) ->
           let uu____12825 =
             let uu____12827 =
               let uu____12828 = FStar_Syntax_Subst.compress head  in
               uu____12828.FStar_Syntax_Syntax.n  in
             match uu____12827 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12833 -> false  in
           if uu____12825
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12865 ->
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
          ((let uu____12912 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12912
            then
              let uu____12915 = FStar_Syntax_Print.term_to_string e  in
              let uu____12917 = FStar_Syntax_Print.term_to_string t  in
              let uu____12919 =
                let uu____12921 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12921
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12915 uu____12917 uu____12919
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____12957 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____12957 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____12991 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13069  ->
                          match uu____13069 with
                          | (uu____13077,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13084 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13084 = FStar_Syntax_Util.Equal)))
                   in
                match uu____12991 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13203 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13203 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13217 =
                      let uu____13223 =
                        let uu____13225 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13227 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13229 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13225 uu____13227 uu____13229
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13223)
                       in
                    let uu____13233 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13217 uu____13233
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13251 =
              match uu___7_13251 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13294 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13294 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____13425,uu____13412) when
                           uu____13425 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13458,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13460))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13494 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13494 with
                            | (v,uu____13535,g) ->
                                ((let uu____13550 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13550
                                  then
                                    let uu____13553 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13553
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13563 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13563 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13656 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13656))))
                       | (uu____13683,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13720 =
                             let uu____13733 =
                               let uu____13740 =
                                 let uu____13745 = FStar_Dyn.mkdyn env  in
                                 (uu____13745, tau)  in
                               FStar_Pervasives_Native.Some uu____13740  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13733
                              in
                           (match uu____13720 with
                            | (v,uu____13778,g) ->
                                ((let uu____13793 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13793
                                  then
                                    let uu____13796 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13796
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13806 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13806 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13899 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13899))))
                       | (uu____13926,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13974 =
                       let uu____14001 = inst_n_binders t1  in
                       aux [] uu____14001 bs1  in
                     (match uu____13974 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14073) -> (e, torig, guard)
                           | (uu____14104,[]) when
                               let uu____14135 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14135 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14137 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14165 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14178 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14190 =
      let uu____14194 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14194
        (FStar_List.map
           (fun u  ->
              let uu____14206 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14206 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14190 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14234 = FStar_Util.set_is_empty x  in
      if uu____14234
      then []
      else
        (let s =
           let uu____14252 =
             let uu____14255 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14255  in
           FStar_All.pipe_right uu____14252 FStar_Util.set_elements  in
         (let uu____14271 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14271
          then
            let uu____14276 =
              let uu____14278 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14278  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14276
          else ());
         (let r =
            let uu____14287 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14287  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14326 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14326
                     then
                       let uu____14331 =
                         let uu____14333 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14333
                          in
                       let uu____14337 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14339 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14331 uu____14337 uu____14339
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
        let uu____14369 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14369 FStar_Util.set_elements  in
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
        | ([],uu____14408) -> generalized_univ_names
        | (uu____14415,[]) -> explicit_univ_names
        | uu____14422 ->
            let uu____14431 =
              let uu____14437 =
                let uu____14439 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14439
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14437)
               in
            FStar_Errors.raise_error uu____14431 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14461 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14461
       then
         let uu____14466 = FStar_Syntax_Print.term_to_string t  in
         let uu____14468 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14466 uu____14468
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____14477 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14477
        then
          let uu____14482 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14482
        else ());
       (let gen = gen_univs env univs  in
        (let uu____14491 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14491
         then
           let uu____14496 = FStar_Syntax_Print.term_to_string t  in
           let uu____14498 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14496 uu____14498
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
        let uu____14582 =
          let uu____14584 =
            FStar_Util.for_all
              (fun uu____14598  ->
                 match uu____14598 with
                 | (uu____14608,uu____14609,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14584  in
        if uu____14582
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14661 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14661
              then
                let uu____14664 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14664
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14671 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14671
               then
                 let uu____14674 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14674
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14692 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14692 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14726 =
             match uu____14726 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14763 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14763
                   then
                     let uu____14768 =
                       let uu____14770 =
                         let uu____14774 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____14774
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14770
                         (FStar_String.concat ", ")
                        in
                     let uu____14822 =
                       let uu____14824 =
                         let uu____14828 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14828
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14841 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14843 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14841
                                   uu____14843))
                          in
                       FStar_All.pipe_right uu____14824
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14768
                       uu____14822
                   else ());
                  (let univs1 =
                     let uu____14857 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____14869 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____14869) univs
                       uu____14857
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14876 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14876
                    then
                      let uu____14881 =
                        let uu____14883 =
                          let uu____14887 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____14887
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14883
                          (FStar_String.concat ", ")
                         in
                      let uu____14935 =
                        let uu____14937 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14951 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14953 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14951
                                    uu____14953))
                           in
                        FStar_All.pipe_right uu____14937
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14881 uu____14935
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____14974 =
             let uu____14991 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14991  in
           match uu____14974 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15081 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15081
                 then ()
                 else
                   (let uu____15086 = lec_hd  in
                    match uu____15086 with
                    | (lb1,uu____15094,uu____15095) ->
                        let uu____15096 = lec2  in
                        (match uu____15096 with
                         | (lb2,uu____15104,uu____15105) ->
                             let msg =
                               let uu____15108 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15110 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15108 uu____15110
                                in
                             let uu____15113 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15113))
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
                 let uu____15181 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15181
                 then ()
                 else
                   (let uu____15186 = lec_hd  in
                    match uu____15186 with
                    | (lb1,uu____15194,uu____15195) ->
                        let uu____15196 = lec2  in
                        (match uu____15196 with
                         | (lb2,uu____15204,uu____15205) ->
                             let msg =
                               let uu____15208 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15210 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15208 uu____15210
                                in
                             let uu____15213 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15213))
                  in
               let lecs1 =
                 let uu____15224 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15277 = univs_and_uvars_of_lec this_lec  in
                        match uu____15277 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15224 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15387 = lec_hd  in
                   match uu____15387 with
                   | (lbname,e,c) ->
                       let uu____15397 =
                         let uu____15403 =
                           let uu____15405 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15407 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15409 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15405 uu____15407 uu____15409
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15403)
                          in
                       FStar_Errors.raise_error uu____15397 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15431 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15431 with
                         | FStar_Pervasives_Native.Some uu____15440 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15448 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15452 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15452 with
                              | (bs,kres) ->
                                  ((let uu____15472 =
                                      let uu____15473 =
                                        let uu____15476 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15476
                                         in
                                      uu____15473.FStar_Syntax_Syntax.n  in
                                    match uu____15472 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15477
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15481 =
                                          let uu____15483 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15483  in
                                        if uu____15481
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15488 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15490 =
                                        let uu____15493 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____15496  ->
                                             FStar_Pervasives_Native.Some
                                               uu____15496) uu____15493
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15490
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15504 ->
                                          let uu____15505 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15505
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
                      (fun uu____15608  ->
                         match uu____15608 with
                         | (lbname,e,c) ->
                             let uu____15654 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15715 ->
                                   let uu____15728 = (e, c)  in
                                   (match uu____15728 with
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
                                                (fun uu____15768  ->
                                                   match uu____15768 with
                                                   | (x,uu____15774) ->
                                                       let uu____15775 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15775)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15793 =
                                                let uu____15795 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15795
                                                 in
                                              if uu____15793
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
                                          let uu____15804 =
                                            let uu____15805 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15805.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15804 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15830 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15830 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15841 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15845 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15845, gen_tvars))
                                in
                             (match uu____15654 with
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
        (let uu____15992 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15992
         then
           let uu____15995 =
             let uu____15997 =
               FStar_List.map
                 (fun uu____16012  ->
                    match uu____16012 with
                    | (lb,uu____16021,uu____16022) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15997 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15995
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16048  ->
                match uu____16048 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16077 = gen env is_rec lecs  in
           match uu____16077 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16176  ->
                       match uu____16176 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16238 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16238
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16286  ->
                           match uu____16286 with
                           | (l,us,e,c,gvs) ->
                               let uu____16320 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16322 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16324 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16326 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16328 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16320 uu____16322 uu____16324
                                 uu____16326 uu____16328))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____16373  ->
                match uu____16373 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16417 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____16417, t, c, gvs)) univnames_lecs
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
        let uu____16472 =
          let uu____16476 =
            let uu____16478 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16478  in
          FStar_Pervasives_Native.Some uu____16476  in
        FStar_Profiling.profile
          (fun uu____16495  -> generalize' env is_rec lecs) uu____16472
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
              let uu____16552 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16552 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16558 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16558
                    (fun uu____16561  ->
                       FStar_Pervasives_Native.Some uu____16561)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16570 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16570 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16576 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____16579  ->
                          FStar_Pervasives_Native.Some uu____16579)
                       uu____16576)
             in
          let uu____16580 = maybe_coerce_lc env1 e lc t2  in
          match uu____16580 with
          | (e1,lc1,g_c) ->
              let uu____16596 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16596 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16605 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16611 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16605 uu____16611
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16620 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16620
                     then
                       let uu____16625 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16625
                     else ());
                    (let uu____16631 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16631))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16659 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16659
         then
           let uu____16662 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16662
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16676 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16676 with
         | (c,g_c) ->
             let uu____16688 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16688
             then
               let uu____16696 =
                 let uu____16698 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16698  in
               (uu____16696, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16706 =
                    let uu____16707 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16707
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16706
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16708 = check_trivial_precondition env c1  in
                match uu____16708 with
                | (ct,vc,g_pre) ->
                    ((let uu____16724 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16724
                      then
                        let uu____16729 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16729
                      else ());
                     (let uu____16734 =
                        let uu____16736 =
                          let uu____16737 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16737  in
                        discharge uu____16736  in
                      let uu____16738 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16734, uu____16738)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16772 =
        match uu___8_16772 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____16782)::[] -> f fst
        | uu____16807 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16819 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16819
          (fun uu____16820  ->
             FStar_TypeChecker_Common.NonTrivial uu____16820)
         in
      let op_or_e e =
        let uu____16831 =
          let uu____16832 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16832  in
        FStar_All.pipe_right uu____16831
          (fun uu____16835  ->
             FStar_TypeChecker_Common.NonTrivial uu____16835)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16842  ->
             FStar_TypeChecker_Common.NonTrivial uu____16842)
         in
      let op_or_t t =
        let uu____16853 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16853
          (fun uu____16856  ->
             FStar_TypeChecker_Common.NonTrivial uu____16856)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16863  ->
             FStar_TypeChecker_Common.NonTrivial uu____16863)
         in
      let short_op_ite uu___9_16869 =
        match uu___9_16869 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16879)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16906)::[] ->
            let uu____16947 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16947
              (fun uu____16948  ->
                 FStar_TypeChecker_Common.NonTrivial uu____16948)
        | uu____16949 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16961 =
          let uu____16969 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16969)  in
        let uu____16977 =
          let uu____16987 =
            let uu____16995 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16995)  in
          let uu____17003 =
            let uu____17013 =
              let uu____17021 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17021)  in
            let uu____17029 =
              let uu____17039 =
                let uu____17047 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17047)  in
              let uu____17055 =
                let uu____17065 =
                  let uu____17073 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17073)  in
                [uu____17065; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17039 :: uu____17055  in
            uu____17013 :: uu____17029  in
          uu____16987 :: uu____17003  in
        uu____16961 :: uu____16977  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17135 =
            FStar_Util.find_map table
              (fun uu____17150  ->
                 match uu____17150 with
                 | (x,mk) ->
                     let uu____17167 = FStar_Ident.lid_equals x lid  in
                     if uu____17167
                     then
                       let uu____17172 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17172
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17135 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17176 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17184 =
      let uu____17185 = FStar_Syntax_Util.un_uinst l  in
      uu____17185.FStar_Syntax_Syntax.n  in
    match uu____17184 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17190 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17226)::uu____17227 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17246 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17255,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17256))::uu____17257 -> bs
      | uu____17275 ->
          let uu____17276 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17276 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17280 =
                 let uu____17281 = FStar_Syntax_Subst.compress t  in
                 uu____17281.FStar_Syntax_Syntax.n  in
               (match uu____17280 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17285) ->
                    let uu____17306 =
                      FStar_Util.prefix_until
                        (fun uu___10_17346  ->
                           match uu___10_17346 with
                           | (uu____17354,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17355)) ->
                               false
                           | uu____17360 -> true) bs'
                       in
                    (match uu____17306 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17396,uu____17397) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17469,uu____17470) ->
                         let uu____17543 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17564  ->
                                   match uu____17564 with
                                   | (x,uu____17573) ->
                                       let uu____17578 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____17578 "'"))
                            in
                         if uu____17543
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17624  ->
                                     match uu____17624 with
                                     | (x,i) ->
                                         let uu____17643 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17643, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17654 -> bs))
  
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
            let uu____17683 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17683
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
          let uu____17714 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17714
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
        (let uu____17757 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17757
         then
           ((let uu____17762 = FStar_Ident.string_of_lid lident  in
             d uu____17762);
            (let uu____17764 = FStar_Ident.string_of_lid lident  in
             let uu____17766 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17764 uu____17766))
         else ());
        (let fv =
           let uu____17772 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17772
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
         let uu____17784 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2088_17786 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2088_17786.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2088_17786.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2088_17786.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2088_17786.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2088_17786.FStar_Syntax_Syntax.sigopts)
           }), uu____17784))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17804 =
        match uu___11_17804 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17807 -> false  in
      let reducibility uu___12_17815 =
        match uu___12_17815 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17822 -> false  in
      let assumption uu___13_17830 =
        match uu___13_17830 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17834 -> false  in
      let reification uu___14_17842 =
        match uu___14_17842 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17845 -> true
        | uu____17847 -> false  in
      let inferred uu___15_17855 =
        match uu___15_17855 with
        | FStar_Syntax_Syntax.Discriminator uu____17857 -> true
        | FStar_Syntax_Syntax.Projector uu____17859 -> true
        | FStar_Syntax_Syntax.RecordType uu____17865 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17875 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17888 -> false  in
      let has_eq uu___16_17896 =
        match uu___16_17896 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17900 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17979 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17986 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18019 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18019))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18050 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18050
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18070 ->
               let uu____18079 =
                 let uu____18081 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18087  ->
                           match uu___17_18087 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18090 -> false))
                    in
                 Prims.op_Negation uu____18081  in
               if uu____18079
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18097 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18104 -> ()
           | uu____18117 ->
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
      let uu____18131 =
        let uu____18133 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18139  ->
                  match uu___18_18139 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18142 -> false))
           in
        FStar_All.pipe_right uu____18133 Prims.op_Negation  in
      if uu____18131
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18163 =
            let uu____18169 =
              let uu____18171 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18171 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18169)  in
          FStar_Errors.raise_error uu____18163 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18189 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18197 =
            let uu____18199 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18199  in
          if uu____18197 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18210),uu____18211) ->
              ((let uu____18223 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18223
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18232 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18232
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18243 ->
              ((let uu____18253 =
                  let uu____18255 =
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
                  Prims.op_Negation uu____18255  in
                if uu____18253 then err'1 () else ());
               (let uu____18265 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18271  ->
                           match uu___19_18271 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18274 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18265
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18280 ->
              let uu____18287 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18287 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18295 ->
              let uu____18302 =
                let uu____18304 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18304  in
              if uu____18302 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18314 ->
              let uu____18315 =
                let uu____18317 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18317  in
              if uu____18315 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18327 ->
              let uu____18340 =
                let uu____18342 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18342  in
              if uu____18340 then err'1 () else ()
          | uu____18352 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18391 =
          let uu____18392 = FStar_Syntax_Subst.compress t1  in
          uu____18392.FStar_Syntax_Syntax.n  in
        match uu____18391 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18396 ->
            let uu____18411 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18411 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18420;
               FStar_Syntax_Syntax.index = uu____18421;
               FStar_Syntax_Syntax.sort = t2;_},uu____18423)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____18432) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____18458) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18464 -> false
      
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
        (let uu____18474 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18474
         then
           let uu____18479 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18479
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
                  let uu____18544 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18544 r  in
                let uu____18554 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18554 with
                | (uu____18563,signature) ->
                    let uu____18565 =
                      let uu____18566 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18566.FStar_Syntax_Syntax.n  in
                    (match uu____18565 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18574) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18622 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18638 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18640 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____18642 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18638 uu____18640 uu____18642) r
                                 in
                              (match uu____18622 with
                               | (is,g) ->
                                   let uu____18655 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18657 =
                                             let uu____18658 =
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
                                                 = uu____18658;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18657
                                            in
                                         let uu____18677 =
                                           let uu____18684 =
                                             let uu____18685 =
                                               let uu____18700 =
                                                 let uu____18709 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18709]  in
                                               (uu____18700, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18685
                                              in
                                           FStar_Syntax_Syntax.mk uu____18684
                                            in
                                         uu____18677
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18740 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18740
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18749 =
                                           let uu____18754 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18754
                                            in
                                         uu____18749
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18655, g))
                          | uu____18763 -> fail signature)
                     | uu____18764 -> fail signature)
  
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
            let uu____18795 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18795
              (fun ed  ->
                 let uu____18803 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18803 u a_tm)
  
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
              let uu____18839 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18839 with
              | (uu____18844,sig_tm) ->
                  let fail t =
                    let uu____18852 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18852 r  in
                  let uu____18858 =
                    let uu____18859 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18859.FStar_Syntax_Syntax.n  in
                  (match uu____18858 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18863) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18886)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18908 -> fail sig_tm)
                   | uu____18909 -> fail sig_tm)
  
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
          (let uu____18940 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18940
           then
             let uu____18945 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18947 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18945 uu____18947
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18954 =
             let uu____18965 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18966 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18965, (ct.FStar_Syntax_Syntax.result_typ), uu____18966)
              in
           match uu____18954 with
           | (u,a,c_is) ->
               let uu____19014 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19014 with
                | (uu____19023,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19034 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19036 = FStar_Ident.string_of_lid tgt  in
                      let uu____19038 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19034 uu____19036 s uu____19038
                       in
                    let uu____19041 =
                      let uu____19074 =
                        let uu____19075 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19075.FStar_Syntax_Syntax.n  in
                      match uu____19074 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19139 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19139 with
                           | (a_b::bs1,c2) ->
                               let uu____19199 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19199, c2))
                      | uu____19287 ->
                          let uu____19288 =
                            let uu____19294 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19294)
                             in
                          FStar_Errors.raise_error uu____19288 r
                       in
                    (match uu____19041 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19412 =
                           let uu____19419 =
                             let uu____19420 =
                               let uu____19421 =
                                 let uu____19428 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19428, a)  in
                               FStar_Syntax_Syntax.NT uu____19421  in
                             [uu____19420]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19419
                             (fun b  ->
                                let uu____19445 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19447 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19449 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19451 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19445 uu____19447 uu____19449
                                  uu____19451) r
                            in
                         (match uu____19412 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19465 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19465
                                then
                                  let uu____19470 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19479 =
                                             let uu____19481 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19481
                                              in
                                           Prims.op_Hat s uu____19479) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19470
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19512 =
                                           let uu____19519 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19519, t)  in
                                         FStar_Syntax_Syntax.NT uu____19512)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19538 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19538
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19544 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19544
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19553 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19553)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19555 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19555
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19559 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19559 r
                                   in
                                let fml =
                                  let uu____19564 =
                                    let uu____19569 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19570 =
                                      let uu____19571 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19571
                                       in
                                    (uu____19569, uu____19570)  in
                                  match uu____19564 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19597 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19597
                                 then
                                   let uu____19603 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19603
                                 else ());
                                (let c1 =
                                   let uu____19609 =
                                     let uu____19610 =
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
                                         uu____19610;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19609
                                    in
                                 (let uu____19634 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19634
                                  then
                                    let uu____19639 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19639
                                  else ());
                                 (let uu____19644 =
                                    let uu____19645 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19646 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19645 uu____19646
                                     in
                                  (c1, uu____19644)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu19660 .
    'uuuuuu19660 ->
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
              let uu____19689 =
                let uu____19694 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19694
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19689 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19737 =
                let uu____19738 =
                  let uu____19741 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19741
                    FStar_Syntax_Subst.compress
                   in
                uu____19738.FStar_Syntax_Syntax.n  in
              match uu____19737 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19764::bs,uu____19766)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19806 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19806
                    FStar_Pervasives_Native.fst
              | uu____19912 ->
                  let uu____19913 =
                    let uu____19919 =
                      let uu____19921 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19921
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19919)  in
                  FStar_Errors.raise_error uu____19913
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19948 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19957 =
                let uu____19968 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20004  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20011 =
                  let uu____20022 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20022]  in
                FStar_List.append uu____19968 uu____20011  in
              uu____19948 :: uu____19957  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____20093 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20093 with
        | (uu____20098,t) ->
            let err n =
              let uu____20108 =
                let uu____20114 =
                  let uu____20116 = FStar_Ident.string_of_lid datacon  in
                  let uu____20118 = FStar_Util.string_of_int n  in
                  let uu____20120 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20116 uu____20118 uu____20120
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20114)
                 in
              let uu____20124 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20108 uu____20124  in
            let uu____20125 =
              let uu____20126 = FStar_Syntax_Subst.compress t  in
              uu____20126.FStar_Syntax_Syntax.n  in
            (match uu____20125 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20130) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20185  ->
                           match uu____20185 with
                           | (uu____20193,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20202 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20236 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20249 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20249
      then
        let uu____20252 =
          let uu____20265 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20265
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20252;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20300 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20300 with
           | (uu____20309,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20328 =
                 let uu____20329 =
                   let uu___2464_20330 = ct  in
                   let uu____20331 =
                     let uu____20342 =
                       let uu____20351 =
                         let uu____20352 =
                           let uu____20359 =
                             let uu____20360 =
                               let uu____20377 =
                                 let uu____20388 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20388; wp]  in
                               (lift_t, uu____20377)  in
                             FStar_Syntax_Syntax.Tm_app uu____20360  in
                           FStar_Syntax_Syntax.mk uu____20359  in
                         uu____20352 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20351
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20342]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2464_20330.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2464_20330.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20331;
                     FStar_Syntax_Syntax.flags =
                       (uu___2464_20330.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20329  in
               (uu____20328, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20488 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20488 with
           | (uu____20495,lift_t) ->
               let uu____20497 =
                 let uu____20504 =
                   let uu____20505 =
                     let uu____20522 =
                       let uu____20533 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20542 =
                         let uu____20553 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20562 =
                           let uu____20573 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20573]  in
                         uu____20553 :: uu____20562  in
                       uu____20533 :: uu____20542  in
                     (lift_t, uu____20522)  in
                   FStar_Syntax_Syntax.Tm_app uu____20505  in
                 FStar_Syntax_Syntax.mk uu____20504  in
               uu____20497 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20626 =
           let uu____20639 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20639 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20626;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20675  ->
                        fun uu____20676  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____20699 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____20699
  
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
  