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
            let uu____8967 =
              let uu____8968 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8968]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8967  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9015  ->
                   match uu____9015 with
                   | (uu____9029,eff_label,uu____9031,uu____9032) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9045 =
            let uu____9053 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9091  ->
                      match uu____9091 with
                      | (uu____9106,uu____9107,flags,uu____9109) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9126  ->
                                  match uu___5_9126 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9129 -> false))))
               in
            if uu____9053
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9045 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9166 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9168 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9168
                then
                  let uu____9175 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9175, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9182 =
                         let uu____9191 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9191]  in
                       let uu____9210 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9182 uu____9210  in
                     let kwp =
                       let uu____9216 =
                         let uu____9225 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9225]  in
                       let uu____9244 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9216 uu____9244  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9251 =
                         let uu____9252 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9252]  in
                       let uu____9271 =
                         let uu____9274 =
                           let uu____9281 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9281
                            in
                         let uu____9282 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9274 uu____9282  in
                       FStar_Syntax_Util.abs uu____9251 uu____9271
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
                     let uu____9306 =
                       should_not_inline_whole_match ||
                         (let uu____9309 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9309)
                        in
                     if uu____9306 then cthen true else cthen false  in
                   let branch_conditions =
                     let uu____9321 =
                       let uu____9334 =
                         let uu____9339 =
                           let uu____9350 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9394  ->
                                     match uu____9394 with
                                     | (g,uu____9409,uu____9410,uu____9411)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9350
                             (FStar_List.fold_left
                                (fun uu____9455  ->
                                   fun g  ->
                                     match uu____9455 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9496 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9496
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9339
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9334
                         (FStar_List.splitAt (FStar_List.length lcases))
                        in
                     FStar_All.pipe_right uu____9321
                       FStar_Pervasives_Native.fst
                      in
                   let uu____9597 =
                     FStar_List.fold_right2
                       (fun uu____9660  ->
                          fun bcond  ->
                            fun uu____9662  ->
                              match (uu____9660, uu____9662) with
                              | ((g,eff_label,uu____9722,cthen),(uu____9724,celse,g_comp))
                                  ->
                                  let uu____9771 =
                                    let uu____9776 =
                                      maybe_return eff_label cthen  in
                                    FStar_TypeChecker_Common.lcomp_comp
                                      uu____9776
                                     in
                                  (match uu____9771 with
                                   | (cthen1,gthen) ->
                                       let gthen1 =
                                         let uu____9788 =
                                           FStar_Syntax_Util.mk_conj bcond g
                                            in
                                         FStar_TypeChecker_Common.weaken_guard_formula
                                           gthen uu____9788
                                          in
                                       let uu____9789 =
                                         let uu____9800 =
                                           lift_comps_sep_guards env cthen1
                                             celse
                                             FStar_Pervasives_Native.None
                                             false
                                            in
                                         match uu____9800 with
                                         | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                             ->
                                             let md =
                                               FStar_TypeChecker_Env.get_effect_decl
                                                 env m
                                                in
                                             let uu____9828 =
                                               FStar_All.pipe_right cthen2
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             let uu____9829 =
                                               FStar_All.pipe_right celse1
                                                 FStar_Syntax_Util.comp_to_comp_typ
                                                in
                                             (md, uu____9828, uu____9829,
                                               g_lift_then, g_lift_else)
                                          in
                                       (match uu____9789 with
                                        | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                            ->
                                            let fn =
                                              let uu____9880 =
                                                FStar_All.pipe_right md
                                                  FStar_Syntax_Util.is_layered
                                                 in
                                              if uu____9880
                                              then mk_layered_conjunction
                                              else mk_non_layered_conjunction
                                               in
                                            let g_lift_then1 =
                                              let uu____9915 =
                                                FStar_Syntax_Util.mk_conj
                                                  bcond g
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_then uu____9915
                                               in
                                            let g_lift_else1 =
                                              let uu____9917 =
                                                let uu____9918 =
                                                  FStar_Syntax_Util.mk_neg g
                                                   in
                                                FStar_Syntax_Util.mk_conj
                                                  bcond uu____9918
                                                 in
                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                g_lift_else uu____9917
                                               in
                                            let g_lift =
                                              FStar_TypeChecker_Env.conj_guard
                                                g_lift_then1 g_lift_else1
                                               in
                                            let uu____9922 =
                                              let uu____9927 =
                                                FStar_TypeChecker_Env.get_range
                                                  env
                                                 in
                                              fn env md u_res_t res_t g
                                                ct_then ct_else uu____9927
                                               in
                                            (match uu____9922 with
                                             | (c,g_conjunction) ->
                                                 let uu____9938 =
                                                   FStar_TypeChecker_Env.conj_guards
                                                     [g_comp;
                                                     gthen1;
                                                     g_lift;
                                                     g_conjunction]
                                                    in
                                                 ((FStar_Pervasives_Native.Some
                                                     md), c, uu____9938)))))
                       lcases branch_conditions
                       (FStar_Pervasives_Native.None, default_case,
                         FStar_TypeChecker_Env.trivial_guard)
                      in
                   match uu____9597 with
                   | (md,comp,g_comp) ->
                       let g_comp1 =
                         let uu____9955 =
                           let uu____9956 =
                             FStar_All.pipe_right scrutinee
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____9956]  in
                         FStar_TypeChecker_Env.close_guard env0 uu____9955
                           g_comp
                          in
                       (match lcases with
                        | [] -> (comp, g_comp1)
                        | uu____9999::[] -> (comp, g_comp1)
                        | uu____10042 ->
                            let uu____10059 =
                              let uu____10061 =
                                FStar_All.pipe_right md FStar_Util.must  in
                              FStar_All.pipe_right uu____10061
                                FStar_Syntax_Util.is_layered
                               in
                            if uu____10059
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
                               let uu____10074 = destruct_wp_comp comp1  in
                               match uu____10074 with
                               | (uu____10085,uu____10086,wp) ->
                                   let ite_wp =
                                     let uu____10089 =
                                       FStar_All.pipe_right md1
                                         FStar_Syntax_Util.get_wp_ite_combinator
                                        in
                                     FStar_All.pipe_right uu____10089
                                       FStar_Util.must
                                      in
                                   let wp1 =
                                     let uu____10099 =
                                       let uu____10104 =
                                         FStar_TypeChecker_Env.inst_effect_fun_with
                                           [u_res_t] env md1 ite_wp
                                          in
                                       let uu____10105 =
                                         let uu____10106 =
                                           FStar_Syntax_Syntax.as_arg res_t
                                            in
                                         let uu____10115 =
                                           let uu____10126 =
                                             FStar_Syntax_Syntax.as_arg wp
                                              in
                                           [uu____10126]  in
                                         uu____10106 :: uu____10115  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____10104 uu____10105
                                        in
                                     uu____10099 FStar_Pervasives_Native.None
                                       wp.FStar_Syntax_Syntax.pos
                                      in
                                   let uu____10159 =
                                     mk_comp md1 u_res_t res_t wp1
                                       bind_cases_flags
                                      in
                                   (uu____10159, g_comp1))))
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
          let uu____10194 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10194 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10210 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10216 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10210 uu____10216
              else
                (let uu____10225 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10231 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10225 uu____10231)
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
          let uu____10256 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10256
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10259 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10259
        then u_res
        else
          (let is_total =
             let uu____10266 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10266
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10277 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10277 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10280 =
                    let uu____10286 =
                      let uu____10288 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10288
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10286)
                     in
                  FStar_Errors.raise_error uu____10280
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
      let uu____10312 = destruct_wp_comp ct  in
      match uu____10312 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10331 = FStar_TypeChecker_Env.get_range env  in
            let uu____10332 =
              let uu____10337 =
                let uu____10338 =
                  let uu____10339 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10339 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10338
                 in
              let uu____10346 =
                let uu____10347 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10356 =
                  let uu____10367 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10367]  in
                uu____10347 :: uu____10356  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10337 uu____10346  in
            uu____10332 FStar_Pervasives_Native.None uu____10331  in
          let uu____10400 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10400)
  
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
                  let uu____10455 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10455 with
                  | FStar_Pervasives_Native.Some uu____10470 ->
                      ((let uu____10488 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10488
                        then
                          let uu____10492 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10492
                        else ());
                       (let coercion =
                          let uu____10498 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10498
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10505 =
                            let uu____10506 =
                              let uu____10507 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10507
                               in
                            (FStar_Pervasives_Native.None, uu____10506)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10505
                           in
                        let e1 =
                          let uu____10513 =
                            let uu____10518 =
                              let uu____10519 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10519]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10518
                             in
                          uu____10513 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10553 =
                          let uu____10559 =
                            let uu____10561 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10561
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10559)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10553);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10580 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10598 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10609 -> false 
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
      let uu____10633 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10633 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10678 =
              let uu____10693 =
                let uu____10694 = FStar_Syntax_Subst.compress h1  in
                uu____10694.FStar_Syntax_Syntax.n  in
              (uu____10693, args)  in
            match uu____10678 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10741,uu____10742) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10775) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10796,branches),uu____10798) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10862 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10863 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10863 with
                               | (uu____10864,uu____10865,br_body) ->
                                   let uu____10883 =
                                     let uu____10884 =
                                       let uu____10889 =
                                         let uu____10890 =
                                           let uu____10893 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10893
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10890
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10889  in
                                     FStar_All.pipe_right br_body uu____10884
                                      in
                                   (match uu____10883 with
                                    | No  -> No
                                    | uu____10904 -> Maybe))) No)
            | uu____10905 -> No  in
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
            (((let uu____10957 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10957) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10976 =
                 let uu____10977 = FStar_Syntax_Subst.compress t1  in
                 uu____10977.FStar_Syntax_Syntax.n  in
               match uu____10976 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10982 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10992 =
                 let uu____10993 = FStar_Syntax_Subst.compress t1  in
                 uu____10993.FStar_Syntax_Syntax.n  in
               match uu____10992 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10998 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11009 =
                 let uu____11010 = FStar_Syntax_Subst.compress t2  in
                 uu____11010.FStar_Syntax_Syntax.n  in
               match uu____11009 with
               | FStar_Syntax_Syntax.Tm_type uu____11014 -> true
               | uu____11016 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11019 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11019 with
             | (head,args) ->
                 ((let uu____11069 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11069
                   then
                     let uu____11073 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11075 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11077 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11079 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11073 uu____11075 uu____11077 uu____11079
                   else ());
                  (let mk_erased u t =
                     let uu____11097 =
                       let uu____11100 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11100 [u]  in
                     let uu____11101 =
                       let uu____11112 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11112]  in
                     FStar_Syntax_Util.mk_app uu____11097 uu____11101  in
                   let uu____11137 =
                     let uu____11152 =
                       let uu____11153 = FStar_Syntax_Util.un_uinst head  in
                       uu____11153.FStar_Syntax_Syntax.n  in
                     (uu____11152, args)  in
                   match uu____11137 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____11191 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11191 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11231 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11231 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11271 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11271 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11311 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11311 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11332 ->
                       let uu____11347 =
                         let uu____11352 = check_erased env res_typ  in
                         let uu____11353 = check_erased env exp_t  in
                         (uu____11352, uu____11353)  in
                       (match uu____11347 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11362 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11362 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11373 =
                                   let uu____11378 =
                                     let uu____11379 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11379]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11378
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11373 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11414 =
                              let uu____11419 =
                                let uu____11420 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11420]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11419
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11414 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11453 ->
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
        let uu____11488 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11488 with
        | (hd,args) ->
            let uu____11537 =
              let uu____11552 =
                let uu____11553 = FStar_Syntax_Subst.compress hd  in
                uu____11553.FStar_Syntax_Syntax.n  in
              (uu____11552, args)  in
            (match uu____11537 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11591 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____11618  ->
                      FStar_Pervasives_Native.Some uu____11618) uu____11591
             | uu____11619 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11672 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11672
           then
             let uu____11675 = FStar_Syntax_Print.term_to_string e  in
             let uu____11677 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11679 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11675 uu____11677 uu____11679
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11689 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11689 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11714 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11740 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11740, false)
             else
               (let uu____11750 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11750, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11763) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11775 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11775
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1377_11791 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1377_11791.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1377_11791.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1377_11791.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____11798 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11798 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11814 =
                      let uu____11815 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11815 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11835 =
                            let uu____11837 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11837 = FStar_Syntax_Util.Equal  in
                          if uu____11835
                          then
                            ((let uu____11844 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11844
                              then
                                let uu____11848 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11850 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11848 uu____11850
                              else ());
                             (let uu____11855 = set_result_typ c  in
                              (uu____11855, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11862 ->
                                   true
                               | uu____11870 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11879 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11879
                                  in
                               let lc1 =
                                 let uu____11881 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11882 =
                                   let uu____11883 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11883)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11881 uu____11882
                                  in
                               ((let uu____11887 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11887
                                 then
                                   let uu____11891 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11893 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11895 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11897 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11891 uu____11893 uu____11895
                                     uu____11897
                                 else ());
                                (let uu____11902 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11902 with
                                 | (c1,g_lc) ->
                                     let uu____11913 = set_result_typ c1  in
                                     let uu____11914 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11913, uu____11914)))
                             else
                               ((let uu____11918 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11918
                                 then
                                   let uu____11922 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11924 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11922 uu____11924
                                 else ());
                                (let uu____11929 = set_result_typ c  in
                                 (uu____11929, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1414_11933 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1414_11933.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1414_11933.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1414_11933.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11943 =
                      let uu____11944 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11944
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11954 =
                           let uu____11955 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11955.FStar_Syntax_Syntax.n  in
                         match uu____11954 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11962,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11964;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11965;_},uu____11966)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1430_11992 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1430_11992.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1430_11992.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1430_11992.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11993 ->
                             let uu____11994 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11994 with
                              | (c,g_c) ->
                                  ((let uu____12006 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12006
                                    then
                                      let uu____12010 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12012 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12014 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12016 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12010 uu____12012 uu____12014
                                        uu____12016
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
                                        let uu____12029 =
                                          let uu____12034 =
                                            let uu____12035 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12035]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12034
                                           in
                                        uu____12029
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12062 =
                                      let uu____12067 =
                                        FStar_All.pipe_left
                                          (fun uu____12088  ->
                                             FStar_Pervasives_Native.Some
                                               uu____12088)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12089 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12090 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12091 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12067
                                        uu____12089 e uu____12090 uu____12091
                                       in
                                    match uu____12062 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1448_12099 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1448_12099.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1448_12099.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12101 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12101
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12104 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12104 with
                                         | (c2,g_lc) ->
                                             ((let uu____12116 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12116
                                               then
                                                 let uu____12120 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12120
                                               else ());
                                              (let uu____12125 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12125))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12134  ->
                              match uu___6_12134 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12137 -> []))
                       in
                    let lc1 =
                      let uu____12139 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12139 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1464_12141 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1464_12141.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1464_12141.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1464_12141.FStar_TypeChecker_Common.implicits)
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
        let uu____12177 =
          let uu____12180 =
            let uu____12185 =
              let uu____12186 =
                let uu____12195 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12195  in
              [uu____12186]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12185  in
          uu____12180 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12177  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12218 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12218
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12237 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12253 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12270 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12270
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12286)::(ens,uu____12288)::uu____12289 ->
                    let uu____12332 =
                      let uu____12335 = norm req  in
                      FStar_Pervasives_Native.Some uu____12335  in
                    let uu____12336 =
                      let uu____12337 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____12337  in
                    (uu____12332, uu____12336)
                | uu____12340 ->
                    let uu____12351 =
                      let uu____12357 =
                        let uu____12359 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12359
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12357)
                       in
                    FStar_Errors.raise_error uu____12351
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12379)::uu____12380 ->
                    let uu____12407 =
                      let uu____12412 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12412
                       in
                    (match uu____12407 with
                     | (us_r,uu____12444) ->
                         let uu____12445 =
                           let uu____12450 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12450
                            in
                         (match uu____12445 with
                          | (us_e,uu____12482) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12485 =
                                  let uu____12486 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12486
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12485
                                  us_r
                                 in
                              let as_ens =
                                let uu____12488 =
                                  let uu____12489 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12489
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12488
                                  us_e
                                 in
                              let req =
                                let uu____12493 =
                                  let uu____12498 =
                                    let uu____12499 =
                                      let uu____12510 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12510]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12499
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12498
                                   in
                                uu____12493 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12550 =
                                  let uu____12555 =
                                    let uu____12556 =
                                      let uu____12567 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12567]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12556
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12555
                                   in
                                uu____12550 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12604 =
                                let uu____12607 = norm req  in
                                FStar_Pervasives_Native.Some uu____12607  in
                              let uu____12608 =
                                let uu____12609 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____12609  in
                              (uu____12604, uu____12608)))
                | uu____12612 -> failwith "Impossible"))
  
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
        (let uu____12651 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12651
         then
           let uu____12656 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12658 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12656
             uu____12658
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
          (let uu____12717 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12717
           then
             let uu____12722 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12724 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12722
               uu____12724
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12735 =
      let uu____12737 =
        let uu____12738 = FStar_Syntax_Subst.compress t  in
        uu____12738.FStar_Syntax_Syntax.n  in
      match uu____12737 with
      | FStar_Syntax_Syntax.Tm_app uu____12742 -> false
      | uu____12760 -> true  in
    if uu____12735
    then t
    else
      (let uu____12765 = FStar_Syntax_Util.head_and_args t  in
       match uu____12765 with
       | (head,args) ->
           let uu____12808 =
             let uu____12810 =
               let uu____12811 = FStar_Syntax_Subst.compress head  in
               uu____12811.FStar_Syntax_Syntax.n  in
             match uu____12810 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12816 -> false  in
           if uu____12808
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12848 ->
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
          ((let uu____12895 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12895
            then
              let uu____12898 = FStar_Syntax_Print.term_to_string e  in
              let uu____12900 = FStar_Syntax_Print.term_to_string t  in
              let uu____12902 =
                let uu____12904 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12904
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12898 uu____12900 uu____12902
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____12940 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____12940 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____12974 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____13052  ->
                          match uu____13052 with
                          | (uu____13060,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____13067 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____13067 = FStar_Syntax_Util.Equal)))
                   in
                match uu____12974 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____13186 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13186 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13200 =
                      let uu____13206 =
                        let uu____13208 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13210 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13212 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13208 uu____13210 uu____13212
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13206)
                       in
                    let uu____13216 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13200 uu____13216
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13234 =
              match uu___7_13234 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13277 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13277 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____13408,uu____13395) when
                           uu____13408 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13441,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13443))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13477 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13477 with
                            | (v,uu____13518,g) ->
                                ((let uu____13533 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13533
                                  then
                                    let uu____13536 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13536
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13546 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13546 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13639 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13639))))
                       | (uu____13666,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13703 =
                             let uu____13716 =
                               let uu____13723 =
                                 let uu____13728 = FStar_Dyn.mkdyn env  in
                                 (uu____13728, tau)  in
                               FStar_Pervasives_Native.Some uu____13723  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13716
                              in
                           (match uu____13703 with
                            | (v,uu____13761,g) ->
                                ((let uu____13776 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13776
                                  then
                                    let uu____13779 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13779
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____13789 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____13789 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____13882 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____13882))))
                       | (uu____13909,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13957 =
                       let uu____13984 = inst_n_binders t1  in
                       aux [] uu____13984 bs1  in
                     (match uu____13957 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14056) -> (e, torig, guard)
                           | (uu____14087,[]) when
                               let uu____14118 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14118 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14120 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14148 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   FStar_Pervasives_Native.None
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____14161 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____14173 =
      let uu____14177 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____14177
        (FStar_List.map
           (fun u  ->
              let uu____14189 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14189 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14173 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14217 = FStar_Util.set_is_empty x  in
      if uu____14217
      then []
      else
        (let s =
           let uu____14237 =
             let uu____14240 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14240  in
           FStar_All.pipe_right uu____14237 FStar_Util.set_elements  in
         (let uu____14258 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14258
          then
            let uu____14263 =
              let uu____14265 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14265  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14263
          else ());
         (let r =
            let uu____14274 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14274  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14319 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14319
                     then
                       let uu____14324 =
                         let uu____14326 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14326
                          in
                       let uu____14330 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14332 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14324 uu____14330 uu____14332
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
        let uu____14362 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14362 FStar_Util.set_elements  in
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
        | ([],uu____14401) -> generalized_univ_names
        | (uu____14408,[]) -> explicit_univ_names
        | uu____14415 ->
            let uu____14424 =
              let uu____14430 =
                let uu____14432 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14432
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14430)
               in
            FStar_Errors.raise_error uu____14424 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14454 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14454
       then
         let uu____14459 = FStar_Syntax_Print.term_to_string t  in
         let uu____14461 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14459 uu____14461
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____14470 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14470
        then
          let uu____14475 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14475
        else ());
       (let gen = gen_univs env univs  in
        (let uu____14484 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14484
         then
           let uu____14489 = FStar_Syntax_Print.term_to_string t  in
           let uu____14491 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14489 uu____14491
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
        let uu____14575 =
          let uu____14577 =
            FStar_Util.for_all
              (fun uu____14591  ->
                 match uu____14591 with
                 | (uu____14601,uu____14602,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14577  in
        if uu____14575
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____14654 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14654
              then
                let uu____14657 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14657
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14664 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14664
               then
                 let uu____14667 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14667
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14685 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14685 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14719 =
             match uu____14719 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14756 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14756
                   then
                     let uu____14761 =
                       let uu____14763 =
                         let uu____14767 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____14767
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14763
                         (FStar_String.concat ", ")
                        in
                     let uu____14823 =
                       let uu____14825 =
                         let uu____14829 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14829
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14842 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14844 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14842
                                   uu____14844))
                          in
                       FStar_All.pipe_right uu____14825
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14761
                       uu____14823
                   else ());
                  (let univs1 =
                     let uu____14858 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____14870 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____14870) univs
                       uu____14858
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14877 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14877
                    then
                      let uu____14882 =
                        let uu____14884 =
                          let uu____14888 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____14888
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14884
                          (FStar_String.concat ", ")
                         in
                      let uu____14944 =
                        let uu____14946 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14960 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14962 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14960
                                    uu____14962))
                           in
                        FStar_All.pipe_right uu____14946
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14882 uu____14944
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____14983 =
             let uu____15000 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15000  in
           match uu____14983 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15090 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15090
                 then ()
                 else
                   (let uu____15095 = lec_hd  in
                    match uu____15095 with
                    | (lb1,uu____15103,uu____15104) ->
                        let uu____15105 = lec2  in
                        (match uu____15105 with
                         | (lb2,uu____15113,uu____15114) ->
                             let msg =
                               let uu____15117 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15119 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15117 uu____15119
                                in
                             let uu____15122 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15122))
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
                 let uu____15190 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15190
                 then ()
                 else
                   (let uu____15195 = lec_hd  in
                    match uu____15195 with
                    | (lb1,uu____15203,uu____15204) ->
                        let uu____15205 = lec2  in
                        (match uu____15205 with
                         | (lb2,uu____15213,uu____15214) ->
                             let msg =
                               let uu____15217 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15219 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15217 uu____15219
                                in
                             let uu____15222 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15222))
                  in
               let lecs1 =
                 let uu____15233 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15286 = univs_and_uvars_of_lec this_lec  in
                        match uu____15286 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15233 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____15396 = lec_hd  in
                   match uu____15396 with
                   | (lbname,e,c) ->
                       let uu____15406 =
                         let uu____15412 =
                           let uu____15414 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15416 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15418 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15414 uu____15416 uu____15418
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15412)
                          in
                       FStar_Errors.raise_error uu____15406 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15440 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15440 with
                         | FStar_Pervasives_Native.Some uu____15449 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15457 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15461 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15461 with
                              | (bs,kres) ->
                                  ((let uu____15481 =
                                      let uu____15482 =
                                        let uu____15485 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15485
                                         in
                                      uu____15482.FStar_Syntax_Syntax.n  in
                                    match uu____15481 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15486
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15490 =
                                          let uu____15492 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15492  in
                                        if uu____15490
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____15497 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____15499 =
                                        let uu____15502 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____15505  ->
                                             FStar_Pervasives_Native.Some
                                               uu____15505) uu____15502
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15499
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15513 ->
                                          let uu____15514 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15514
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
                      (fun uu____15617  ->
                         match uu____15617 with
                         | (lbname,e,c) ->
                             let uu____15663 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15724 ->
                                   let uu____15737 = (e, c)  in
                                   (match uu____15737 with
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
                                                (fun uu____15777  ->
                                                   match uu____15777 with
                                                   | (x,uu____15783) ->
                                                       let uu____15784 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15784)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15802 =
                                                let uu____15804 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15804
                                                 in
                                              if uu____15802
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
                                          let uu____15813 =
                                            let uu____15814 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15814.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15813 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15839 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15839 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15850 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15854 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15854, gen_tvars))
                                in
                             (match uu____15663 with
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
        (let uu____16001 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16001
         then
           let uu____16004 =
             let uu____16006 =
               FStar_List.map
                 (fun uu____16021  ->
                    match uu____16021 with
                    | (lb,uu____16030,uu____16031) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16006 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16004
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16057  ->
                match uu____16057 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16086 = gen env is_rec lecs  in
           match uu____16086 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16185  ->
                       match uu____16185 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16247 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16247
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16295  ->
                           match uu____16295 with
                           | (l,us,e,c,gvs) ->
                               let uu____16329 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16331 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16333 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16335 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16337 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16329 uu____16331 uu____16333
                                 uu____16335 uu____16337))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____16382  ->
                match uu____16382 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16426 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____16426, t, c, gvs)) univnames_lecs
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
        let uu____16481 =
          let uu____16485 =
            let uu____16487 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16487  in
          FStar_Pervasives_Native.Some uu____16485  in
        FStar_Profiling.profile
          (fun uu____16504  -> generalize' env is_rec lecs) uu____16481
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
              let uu____16561 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16561 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16567 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16567
                    (fun uu____16570  ->
                       FStar_Pervasives_Native.Some uu____16570)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16579 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16579 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16585 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____16588  ->
                          FStar_Pervasives_Native.Some uu____16588)
                       uu____16585)
             in
          let uu____16589 = maybe_coerce_lc env1 e lc t2  in
          match uu____16589 with
          | (e1,lc1,g_c) ->
              let uu____16605 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16605 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16614 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16620 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16614 uu____16620
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16629 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16629
                     then
                       let uu____16634 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16634
                     else ());
                    (let uu____16640 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16640))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16668 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16668
         then
           let uu____16671 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16671
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16685 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16685 with
         | (c,g_c) ->
             let uu____16697 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16697
             then
               let uu____16705 =
                 let uu____16707 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16707  in
               (uu____16705, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16715 =
                    let uu____16716 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16716
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16715
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16717 = check_trivial_precondition env c1  in
                match uu____16717 with
                | (ct,vc,g_pre) ->
                    ((let uu____16733 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16733
                      then
                        let uu____16738 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16738
                      else ());
                     (let uu____16743 =
                        let uu____16745 =
                          let uu____16746 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16746  in
                        discharge uu____16745  in
                      let uu____16747 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16743, uu____16747)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16781 =
        match uu___8_16781 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____16791)::[] -> f fst
        | uu____16816 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16828 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16828
          (fun uu____16829  ->
             FStar_TypeChecker_Common.NonTrivial uu____16829)
         in
      let op_or_e e =
        let uu____16840 =
          let uu____16841 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16841  in
        FStar_All.pipe_right uu____16840
          (fun uu____16844  ->
             FStar_TypeChecker_Common.NonTrivial uu____16844)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____16851  ->
             FStar_TypeChecker_Common.NonTrivial uu____16851)
         in
      let op_or_t t =
        let uu____16862 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16862
          (fun uu____16865  ->
             FStar_TypeChecker_Common.NonTrivial uu____16865)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____16872  ->
             FStar_TypeChecker_Common.NonTrivial uu____16872)
         in
      let short_op_ite uu___9_16878 =
        match uu___9_16878 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16888)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16915)::[] ->
            let uu____16956 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16956
              (fun uu____16957  ->
                 FStar_TypeChecker_Common.NonTrivial uu____16957)
        | uu____16958 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16970 =
          let uu____16978 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16978)  in
        let uu____16986 =
          let uu____16996 =
            let uu____17004 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17004)  in
          let uu____17012 =
            let uu____17022 =
              let uu____17030 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17030)  in
            let uu____17038 =
              let uu____17048 =
                let uu____17056 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17056)  in
              let uu____17064 =
                let uu____17074 =
                  let uu____17082 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17082)  in
                [uu____17074; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17048 :: uu____17064  in
            uu____17022 :: uu____17038  in
          uu____16996 :: uu____17012  in
        uu____16970 :: uu____16986  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17144 =
            FStar_Util.find_map table
              (fun uu____17159  ->
                 match uu____17159 with
                 | (x,mk) ->
                     let uu____17176 = FStar_Ident.lid_equals x lid  in
                     if uu____17176
                     then
                       let uu____17181 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____17181
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17144 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17185 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17193 =
      let uu____17194 = FStar_Syntax_Util.un_uinst l  in
      uu____17194.FStar_Syntax_Syntax.n  in
    match uu____17193 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17199 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____17235)::uu____17236 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____17255 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17264,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17265))::uu____17266 -> bs
      | uu____17284 ->
          let uu____17285 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17285 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17289 =
                 let uu____17290 = FStar_Syntax_Subst.compress t  in
                 uu____17290.FStar_Syntax_Syntax.n  in
               (match uu____17289 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17294) ->
                    let uu____17315 =
                      FStar_Util.prefix_until
                        (fun uu___10_17355  ->
                           match uu___10_17355 with
                           | (uu____17363,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17364)) ->
                               false
                           | uu____17369 -> true) bs'
                       in
                    (match uu____17315 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17405,uu____17406) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17478,uu____17479) ->
                         let uu____17552 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17573  ->
                                   match uu____17573 with
                                   | (x,uu____17582) ->
                                       let uu____17587 =
                                         FStar_Ident.text_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____17587 "'"))
                            in
                         if uu____17552
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17633  ->
                                     match uu____17633 with
                                     | (x,i) ->
                                         let uu____17652 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17652, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17663 -> bs))
  
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
            let uu____17692 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17692
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
          let uu____17723 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17723
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
        (let uu____17766 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17766
         then
           ((let uu____17771 = FStar_Ident.string_of_lid lident  in
             d uu____17771);
            (let uu____17773 = FStar_Ident.string_of_lid lident  in
             let uu____17775 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17773 uu____17775))
         else ());
        (let fv =
           let uu____17781 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17781
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
         let uu____17793 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2086_17795 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2086_17795.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2086_17795.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2086_17795.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2086_17795.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2086_17795.FStar_Syntax_Syntax.sigopts)
           }), uu____17793))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17813 =
        match uu___11_17813 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17816 -> false  in
      let reducibility uu___12_17824 =
        match uu___12_17824 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17831 -> false  in
      let assumption uu___13_17839 =
        match uu___13_17839 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17843 -> false  in
      let reification uu___14_17851 =
        match uu___14_17851 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17854 -> true
        | uu____17856 -> false  in
      let inferred uu___15_17864 =
        match uu___15_17864 with
        | FStar_Syntax_Syntax.Discriminator uu____17866 -> true
        | FStar_Syntax_Syntax.Projector uu____17868 -> true
        | FStar_Syntax_Syntax.RecordType uu____17874 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17884 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17897 -> false  in
      let has_eq uu___16_17905 =
        match uu___16_17905 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17909 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17988 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17995 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18028 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18028))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18059 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18059
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18079 ->
               let uu____18088 =
                 let uu____18090 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18096  ->
                           match uu___17_18096 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18099 -> false))
                    in
                 Prims.op_Negation uu____18090  in
               if uu____18088
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18106 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____18113 -> ()
           | uu____18126 ->
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
      let uu____18140 =
        let uu____18142 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18148  ->
                  match uu___18_18148 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18151 -> false))
           in
        FStar_All.pipe_right uu____18142 Prims.op_Negation  in
      if uu____18140
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18172 =
            let uu____18178 =
              let uu____18180 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18180 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18178)  in
          FStar_Errors.raise_error uu____18172 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18198 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18206 =
            let uu____18208 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18208  in
          if uu____18206 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18219),uu____18220) ->
              ((let uu____18232 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18232
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18241 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18241
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18252 ->
              ((let uu____18262 =
                  let uu____18264 =
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
                  Prims.op_Negation uu____18264  in
                if uu____18262 then err'1 () else ());
               (let uu____18274 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18280  ->
                           match uu___19_18280 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18283 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18274
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18289 ->
              let uu____18296 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18296 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18304 ->
              let uu____18311 =
                let uu____18313 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18313  in
              if uu____18311 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18323 ->
              let uu____18324 =
                let uu____18326 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18326  in
              if uu____18324 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18336 ->
              let uu____18349 =
                let uu____18351 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18351  in
              if uu____18349 then err'1 () else ()
          | uu____18361 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18400 =
          let uu____18401 = FStar_Syntax_Subst.compress t1  in
          uu____18401.FStar_Syntax_Syntax.n  in
        match uu____18400 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18405 ->
            let uu____18420 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18420 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18429;
               FStar_Syntax_Syntax.index = uu____18430;
               FStar_Syntax_Syntax.sort = t2;_},uu____18432)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____18441) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____18467) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18473 -> false
      
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
        (let uu____18483 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18483
         then
           let uu____18488 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18488
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
                  let uu____18553 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18553 r  in
                let uu____18563 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18563 with
                | (uu____18572,signature) ->
                    let uu____18574 =
                      let uu____18575 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18575.FStar_Syntax_Syntax.n  in
                    (match uu____18574 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18583) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18631 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18647 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18649 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____18651 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18647 uu____18649 uu____18651) r
                                 in
                              (match uu____18631 with
                               | (is,g) ->
                                   let uu____18664 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18666 =
                                             let uu____18667 =
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
                                                 = uu____18667;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18666
                                            in
                                         let uu____18686 =
                                           let uu____18693 =
                                             let uu____18694 =
                                               let uu____18709 =
                                                 let uu____18718 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18718]  in
                                               (uu____18709, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18694
                                              in
                                           FStar_Syntax_Syntax.mk uu____18693
                                            in
                                         uu____18686
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18749 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18749
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18758 =
                                           let uu____18763 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18763
                                            in
                                         uu____18758
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18664, g))
                          | uu____18772 -> fail signature)
                     | uu____18773 -> fail signature)
  
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
            let uu____18804 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18804
              (fun ed  ->
                 let uu____18812 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18812 u a_tm)
  
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
              let uu____18848 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18848 with
              | (uu____18853,sig_tm) ->
                  let fail t =
                    let uu____18861 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18861 r  in
                  let uu____18867 =
                    let uu____18868 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18868.FStar_Syntax_Syntax.n  in
                  (match uu____18867 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18872) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18895)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18917 -> fail sig_tm)
                   | uu____18918 -> fail sig_tm)
  
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
          (let uu____18949 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18949
           then
             let uu____18954 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18956 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18954 uu____18956
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18963 =
             let uu____18974 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18975 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18974, (ct.FStar_Syntax_Syntax.result_typ), uu____18975)
              in
           match uu____18963 with
           | (u,a,c_is) ->
               let uu____19023 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19023 with
                | (uu____19032,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19043 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19045 = FStar_Ident.string_of_lid tgt  in
                      let uu____19047 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19043 uu____19045 s uu____19047
                       in
                    let uu____19050 =
                      let uu____19083 =
                        let uu____19084 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19084.FStar_Syntax_Syntax.n  in
                      match uu____19083 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19148 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19148 with
                           | (a_b::bs1,c2) ->
                               let uu____19208 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19208, c2))
                      | uu____19296 ->
                          let uu____19297 =
                            let uu____19303 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19303)
                             in
                          FStar_Errors.raise_error uu____19297 r
                       in
                    (match uu____19050 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19421 =
                           let uu____19428 =
                             let uu____19429 =
                               let uu____19430 =
                                 let uu____19437 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19437, a)  in
                               FStar_Syntax_Syntax.NT uu____19430  in
                             [uu____19429]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19428
                             (fun b  ->
                                let uu____19454 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19456 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19458 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19460 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19454 uu____19456 uu____19458
                                  uu____19460) r
                            in
                         (match uu____19421 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19474 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19474
                                then
                                  let uu____19479 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19488 =
                                             let uu____19490 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19490
                                              in
                                           Prims.op_Hat s uu____19488) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19479
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19521 =
                                           let uu____19528 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19528, t)  in
                                         FStar_Syntax_Syntax.NT uu____19521)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19547 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19547
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19553 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19553
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19562 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19562)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19564 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19564
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19568 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19568 r
                                   in
                                let fml =
                                  let uu____19573 =
                                    let uu____19578 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19579 =
                                      let uu____19580 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19580
                                       in
                                    (uu____19578, uu____19579)  in
                                  match uu____19573 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19606 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19606
                                 then
                                   let uu____19612 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19612
                                 else ());
                                (let c1 =
                                   let uu____19618 =
                                     let uu____19619 =
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
                                         uu____19619;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19618
                                    in
                                 (let uu____19643 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19643
                                  then
                                    let uu____19648 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19648
                                  else ());
                                 (let uu____19653 =
                                    let uu____19654 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19655 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19654 uu____19655
                                     in
                                  (c1, uu____19653)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu19669 .
    'uuuuuu19669 ->
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
              let uu____19698 =
                let uu____19703 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19703
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19698 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19746 =
                let uu____19747 =
                  let uu____19750 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19750
                    FStar_Syntax_Subst.compress
                   in
                uu____19747.FStar_Syntax_Syntax.n  in
              match uu____19746 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19773::bs,uu____19775)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19815 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19815
                    FStar_Pervasives_Native.fst
              | uu____19921 ->
                  let uu____19922 =
                    let uu____19928 =
                      let uu____19930 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19930
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19928)  in
                  FStar_Errors.raise_error uu____19922
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19957 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19966 =
                let uu____19977 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20013  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20020 =
                  let uu____20031 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20031]  in
                FStar_List.append uu____19977 uu____20020  in
              uu____19957 :: uu____19966  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____20102 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20102 with
        | (uu____20107,t) ->
            let err n =
              let uu____20117 =
                let uu____20123 =
                  let uu____20125 = FStar_Ident.string_of_lid datacon  in
                  let uu____20127 = FStar_Util.string_of_int n  in
                  let uu____20129 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20125 uu____20127 uu____20129
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20123)
                 in
              let uu____20133 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20117 uu____20133  in
            let uu____20134 =
              let uu____20135 = FStar_Syntax_Subst.compress t  in
              uu____20135.FStar_Syntax_Syntax.n  in
            (match uu____20134 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20139) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20194  ->
                           match uu____20194 with
                           | (uu____20202,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20211 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____20245 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____20258 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____20258
      then
        let uu____20261 =
          let uu____20274 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____20274
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20261;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20309 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20309 with
           | (uu____20318,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20337 =
                 let uu____20338 =
                   let uu___2462_20339 = ct  in
                   let uu____20340 =
                     let uu____20351 =
                       let uu____20360 =
                         let uu____20361 =
                           let uu____20368 =
                             let uu____20369 =
                               let uu____20386 =
                                 let uu____20397 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20397; wp]  in
                               (lift_t, uu____20386)  in
                             FStar_Syntax_Syntax.Tm_app uu____20369  in
                           FStar_Syntax_Syntax.mk uu____20368  in
                         uu____20361 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20360
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20351]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2462_20339.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2462_20339.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20340;
                     FStar_Syntax_Syntax.flags =
                       (uu___2462_20339.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20338  in
               (uu____20337, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20497 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20497 with
           | (uu____20504,lift_t) ->
               let uu____20506 =
                 let uu____20513 =
                   let uu____20514 =
                     let uu____20531 =
                       let uu____20542 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20551 =
                         let uu____20562 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20571 =
                           let uu____20582 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20582]  in
                         uu____20562 :: uu____20571  in
                       uu____20542 :: uu____20551  in
                     (lift_t, uu____20531)  in
                   FStar_Syntax_Syntax.Tm_app uu____20514  in
                 FStar_Syntax_Syntax.mk uu____20513  in
               uu____20506 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20635 =
           let uu____20648 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20648 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20635;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20684  ->
                        fun uu____20685  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____20708 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____20708
  
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
  