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
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____339;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____341;
          FStar_Syntax_Syntax.lbpos = uu____342;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____377 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____377 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
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
                    (univ_vars2, t2, true))
           | uu____575 ->
               let uu____576 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____576 with
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
        let uu____702 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____702)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____706 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____706)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____710 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
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
               mk1 uu____891  in
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
         | hd1::uu____972 -> FStar_Pervasives_Native.Some hd1)
  
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
    fun is_layered1  ->
      fun r  ->
        let err uu____1184 =
          let uu____1185 =
            let uu____1191 =
              let uu____1193 = FStar_Syntax_Print.term_to_string repr  in
              let uu____1195 = FStar_Util.string_of_bool is_layered1  in
              FStar_Util.format2
                "Could not get effect args from repr %s with is_layered %s"
                uu____1193 uu____1195
               in
            (FStar_Errors.Fatal_UnexpectedEffect, uu____1191)  in
          FStar_Errors.raise_error uu____1185 r  in
        let repr1 = FStar_Syntax_Subst.compress repr  in
        if is_layered1
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
                             let subst1 =
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
                                    (FStar_Syntax_Subst.subst subst1))
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
                let close1 =
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
                             md close1
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
               (let uu____3502 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3502) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3506 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3506)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3517 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3517 with
                | (head1,uu____3534) ->
                    let uu____3555 =
                      let uu____3556 = FStar_Syntax_Util.un_uinst head1  in
                      uu____3556.FStar_Syntax_Syntax.n  in
                    (match uu____3555 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3561 =
                           let uu____3563 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3563
                            in
                         Prims.op_Negation uu____3561
                     | uu____3564 -> true)))
              &&
              (let uu____3567 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3567)
  
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
            let uu____3595 =
              let uu____3597 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3597  in
            if uu____3595
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3604 = FStar_Syntax_Util.is_unit t  in
               if uu____3604
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
                    let uu____3613 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3613
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3619 =
                         let uu____3620 =
                           let uu____3625 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3626 =
                             let uu____3627 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3636 =
                               let uu____3647 = FStar_Syntax_Syntax.as_arg v1
                                  in
                               [uu____3647]  in
                             uu____3627 :: uu____3636  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3625
                             uu____3626
                            in
                         uu____3620 FStar_Pervasives_Native.None
                           v1.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3619)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3681 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3681
           then
             let uu____3686 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3688 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3690 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3686 uu____3688 uu____3690
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
                      (let uu____3763 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3763
                       then
                         let uu____3768 =
                           let uu____3770 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3770  in
                         let uu____3771 =
                           let uu____3773 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3773  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3768 uu____3771
                       else ());
                      (let uu____3777 =
                         let uu____3784 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3785 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3786 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3784, uu____3785, uu____3786)  in
                       match uu____3777 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3794 =
                             let uu____3805 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3806 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3805,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3806)
                              in
                           (match uu____3794 with
                            | (u1,t1,is1) ->
                                let uu____3840 =
                                  let uu____3851 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3852 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3851,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3852)
                                   in
                                (match uu____3840 with
                                 | (u2,t2,is2) ->
                                     let uu____3886 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3886 with
                                      | (uu____3895,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3910 =
                                              let uu____3912 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3912 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3910)
                                             in
                                          let uu____3916 =
                                            let uu____3961 =
                                              let uu____3962 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3962.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3961 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4038 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4038 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4123 =
                                                       let uu____4150 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4150
                                                         (fun uu____4235  ->
                                                            match uu____4235
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4316
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4329
                                                                  =
                                                                  let uu____4336
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4336
                                                                   in
                                                                (l1,
                                                                  uu____4316,
                                                                  uu____4329))
                                                        in
                                                     (match uu____4123 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          let uu____4464 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c1
                                                             in
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b,
                                                            uu____4464)))
                                            | uu____4497 ->
                                                let uu____4498 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4498 r1
                                             in
                                          (match uu____3916 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                               ->
                                               let uu____4623 =
                                                 let uu____4630 =
                                                   let uu____4631 =
                                                     let uu____4632 =
                                                       let uu____4639 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4639, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4632
                                                      in
                                                   let uu____4650 =
                                                     let uu____4653 =
                                                       let uu____4654 =
                                                         let uu____4661 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4661, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4654
                                                        in
                                                     [uu____4653]  in
                                                   uu____4631 :: uu____4650
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4630
                                                   (fun b1  ->
                                                      let uu____4677 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4679 =
                                                        let uu____4681 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4683 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4685 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4681
                                                          uu____4683
                                                          uu____4685
                                                         in
                                                      let uu____4688 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4677 uu____4679
                                                        uu____4688) r1
                                                  in
                                               (match uu____4623 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4725 =
                                                               let uu____4732
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4732,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4725)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4759 =
                                                          let uu____4762 =
                                                            let uu____4763 =
                                                              let uu____4764
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4764.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4763
                                                             in
                                                          let uu____4773 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4762
                                                            uu____4773 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4759
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4786
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4786)
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
                                                        let uu____4805 =
                                                          let uu____4806 =
                                                            let uu____4809 =
                                                              let uu____4810
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4810.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4809
                                                             in
                                                          uu____4806.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4805 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4843 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4843
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4853
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    let uu____4861
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4861
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4882
                                                                    =
                                                                    let uu____4885
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4885
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4860,
                                                                    uu____4882)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4853
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4899
                                                                   =
                                                                   let uu____4902
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4903
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4902
                                                                    uu____4903
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4899
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4922 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4930
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4930)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4922
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let is =
                                                      let uu____4946 =
                                                        let uu____4949 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____4950 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____4949
                                                          uu____4950 r1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4946
                                                        (FStar_List.map
                                                           (FStar_Syntax_Subst.subst
                                                              subst1))
                                                       in
                                                    let c =
                                                      let uu____4957 =
                                                        let uu____4958 =
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
                                                            = uu____4958;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4957
                                                       in
                                                    ((let uu____4978 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4978
                                                      then
                                                        let uu____4983 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4983
                                                      else ());
                                                     (let uu____4988 =
                                                        FStar_TypeChecker_Env.conj_guards
                                                          [g_uvars;
                                                          f_guard;
                                                          g_guard]
                                                         in
                                                      (c, uu____4988)))))))))
  
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
                let uu____5033 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5059 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5059 with
                  | (a,kwp) ->
                      let uu____5090 = destruct_wp_comp ct1  in
                      let uu____5097 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5090, uu____5097)
                   in
                match uu____5033 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5150 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5150]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5170 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5170]
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
                      let uu____5217 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5226 =
                        let uu____5237 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5246 =
                          let uu____5257 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5266 =
                            let uu____5277 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5286 =
                              let uu____5297 =
                                let uu____5306 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5306  in
                              [uu____5297]  in
                            uu____5277 :: uu____5286  in
                          uu____5257 :: uu____5266  in
                        uu____5237 :: uu____5246  in
                      uu____5217 :: uu____5226  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5359 =
                        let uu____5364 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5364 wp_args  in
                      uu____5359 FStar_Pervasives_Native.None
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
              let uu____5412 =
                let uu____5417 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5418 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5417, uu____5418)  in
              match uu____5412 with
              | (ct1,ct2) ->
                  let uu____5425 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5425 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5476 = lift_comps env c1 c2 b true  in
                       (match uu____5476 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5494 =
                              let uu____5499 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5500 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5499, uu____5500)  in
                            (match uu____5494 with
                             | (ct11,ct21) ->
                                 let uu____5507 =
                                   let uu____5512 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5512
                                   then
                                     let bind_t =
                                       let uu____5520 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5520
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5523 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5523,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5507 with
                                  | (c,g_bind) ->
                                      let uu____5530 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5530)))))
  
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
            let uu____5566 =
              let uu____5567 =
                let uu____5578 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5578]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5567;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5566  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5623 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5629  ->
              match uu___1_5629 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5632 -> false))
       in
    if uu____5623
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5644  ->
              match uu___2_5644 with
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
        let uu____5672 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5672
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5683 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5683  in
           let pure_assume_wp1 =
             let uu____5688 = FStar_TypeChecker_Env.get_range env  in
             let uu____5689 =
               let uu____5694 =
                 let uu____5695 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5695]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5694  in
             uu____5689 FStar_Pervasives_Native.None uu____5688  in
           let uu____5728 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5728)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5756 =
          let uu____5757 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5757 with
          | (c,g_c) ->
              let uu____5768 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5768
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5782 = weaken_comp env c f1  in
                     (match uu____5782 with
                      | (c1,g_w) ->
                          let uu____5793 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5793)))
           in
        let uu____5794 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5794 weaken
  
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
                 let uu____5851 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5851  in
               let pure_assert_wp1 =
                 let uu____5856 =
                   let uu____5861 =
                     let uu____5862 =
                       let uu____5871 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5871
                        in
                     [uu____5862]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5861
                    in
                 uu____5856 FStar_Pervasives_Native.None r  in
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
       (let uu____5963 = FStar_Options.debug_any ()  in
        if uu____5963
        then
          let uu____5966 = FStar_Util.string_of_int n1  in
          let uu____5968 =
            let uu____5970 =
              let uu____5972 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____5972  in
            FStar_Util.string_of_int uu____5970  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____5966
            uu____5968
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
            let uu____6027 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6027
            then (lc, g0)
            else
              (let flags =
                 let uu____6039 =
                   let uu____6047 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6047
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6039 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6077 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6085  ->
                               match uu___3_6085 with
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
                               | uu____6088 -> []))
                        in
                     FStar_List.append flags uu____6077
                  in
               let strengthen uu____6098 =
                 let uu____6099 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6099 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6118 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6118 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6125 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6125
                              then
                                let uu____6129 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6131 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6129 uu____6131
                              else ());
                             (let uu____6136 =
                                strengthen_comp env reason c f flags  in
                              match uu____6136 with
                              | (c1,g_s) ->
                                  let uu____6147 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6147))))
                  in
               let uu____6148 =
                 let uu____6149 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6149
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6148,
                 (let uu___711_6151 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___711_6151.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___711_6151.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___711_6151.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6160  ->
            match uu___4_6160 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6164 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6193 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6193
          then e
          else
            (let uu____6200 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6203 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6203)
                in
             if uu____6200
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
                | uu____6273 -> false  in
              if is_unit1
              then
                let uu____6280 =
                  let uu____6282 =
                    let uu____6283 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6283
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6282
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6280
                 then
                   let uu____6292 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6292 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6336 =
                           let uu____6339 =
                             let uu____6340 =
                               let uu____6347 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6347, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6340  in
                           [uu____6339]  in
                         FStar_Syntax_Subst.subst uu____6336 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6360 = close_wp_comp env [x] c  in
                    (uu____6360, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6363 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6391  ->
            match uu____6391 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6411 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6411 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6424 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6424
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6434 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6434
                       then
                         let uu____6439 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6439
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6446 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6446
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6455 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6455
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6462 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6462
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6478 =
                  let uu____6479 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6479
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6487 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6487, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6490 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6490 with
                     | (c1,g_c1) ->
                         let uu____6501 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6501 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____6521  ->
                                    let uu____6522 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6524 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6529 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6522 uu____6524 uu____6529);
                               (let aux uu____6547 =
                                  let uu____6548 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6548
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6579
                                        ->
                                        let uu____6580 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6580
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6612 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6612
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6659 =
                                  let aux_with_trivial_guard uu____6689 =
                                    let uu____6690 = aux ()  in
                                    match uu____6690 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6748 =
                                    let uu____6750 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6750  in
                                  if uu____6748
                                  then
                                    let uu____6766 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6766
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6793 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6793))
                                  else
                                    (let uu____6810 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6810
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___810_6856 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___810_6856.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___810_6856.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____6857 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____6857 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6915 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____6915
                                             (close1 x "c1 Tot")
                                       | (uu____6931,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____6956,uu____6957) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6972 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6972
                                        then
                                          let uu____6987 =
                                            let uu____6995 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6995,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6987
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7008 = try_simplify ()  in
                                match uu____7008 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____7043  ->
                                          let uu____7044 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7044);
                                     (let uu____7047 =
                                        let uu____7048 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____7048
                                         in
                                      (c, uu____7047)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7062  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____7088 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7088 with
                                        | (c,g_bind) ->
                                            let uu____7099 =
                                              let uu____7100 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____7100 g_bind
                                               in
                                            (c, uu____7099)
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
                                        let uu____7127 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7127 with
                                        | (m,uu____7139,lift2) ->
                                            let uu____7141 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7141 with
                                             | (c23,g2) ->
                                                 let uu____7152 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7152 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7168 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7168
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7178 =
                                                          let uu____7183 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7184 =
                                                            let uu____7185 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7194 =
                                                              let uu____7205
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7205]
                                                               in
                                                            uu____7185 ::
                                                              uu____7194
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7183
                                                            uu____7184
                                                           in
                                                        uu____7178
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7238 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7238 with
                                                       | (c,g_s) ->
                                                           let uu____7253 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7253))))
                                         in
                                      let uu____7254 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7270 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7270, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7254 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7286 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7286
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7295 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7295
                                             then
                                               (debug1
                                                  (fun uu____7309  ->
                                                     let uu____7310 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7312 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7310 uu____7312);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____7320 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7323 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7323)
                                                   in
                                                if uu____7320
                                                then
                                                  let e1' =
                                                    let uu____7348 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7348
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7360  ->
                                                        let uu____7361 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7363 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7361
                                                          uu____7363);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7378  ->
                                                        let uu____7379 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7381 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7379
                                                          uu____7381);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7388 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7388
                                                       in
                                                    let uu____7389 =
                                                      let uu____7394 =
                                                        let uu____7395 =
                                                          let uu____7396 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7396]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7395
                                                         in
                                                      weaken_comp uu____7394
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7389 with
                                                    | (c22,g_w) ->
                                                        let uu____7421 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____7421
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7432 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7432))))))
                                          else mk_bind1 c1 b c2))))))
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
      | uu____7449 -> g2
  
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
            (let uu____7473 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7473)
           in
        let flags =
          if should_return1
          then
            let uu____7481 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7481
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7499 =
          let uu____7500 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7500 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7513 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7513
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7521 =
                  let uu____7523 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7523  in
                (if uu____7521
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___929_7532 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___929_7532.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___929_7532.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___929_7532.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7533 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7533, g_c)
                 else
                   (let uu____7536 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7536, g_c)))
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
                   let uu____7547 =
                     let uu____7548 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7548
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7547
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7551 =
                   let uu____7556 =
                     let uu____7557 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7557
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7556  in
                 match uu____7551 with
                 | (bind_c,g_bind) ->
                     let uu____7566 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7567 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7566, uu____7567))
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
            fun uu____7603  ->
              match uu____7603 with
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
                    let uu____7615 =
                      ((let uu____7619 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7619) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7615
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7637 =
        let uu____7638 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7638  in
      FStar_Syntax_Syntax.fvar uu____7637 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7688 =
                    let uu____7693 =
                      let uu____7694 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7694 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7693 [u_a]
                     in
                  match uu____7688 with
                  | (uu____7705,conjunction) ->
                      let uu____7707 =
                        let uu____7716 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7731 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7716, uu____7731)  in
                      (match uu____7707 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7777 =
                               let uu____7779 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7779 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7777)
                              in
                           let uu____7783 =
                             let uu____7828 =
                               let uu____7829 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7829.FStar_Syntax_Syntax.n  in
                             match uu____7828 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7878) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7910 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7910 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7982 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7982 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8130 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8130)))
                             | uu____8163 ->
                                 let uu____8164 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8164 r
                              in
                           (match uu____7783 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8289 =
                                  let uu____8296 =
                                    let uu____8297 =
                                      let uu____8298 =
                                        let uu____8305 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8305, a)  in
                                      FStar_Syntax_Syntax.NT uu____8298  in
                                    [uu____8297]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8296
                                    (fun b  ->
                                       let uu____8321 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8323 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8325 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8321 uu____8323 uu____8325) r
                                   in
                                (match uu____8289 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8363 =
                                                let uu____8370 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8370, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8363) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8409 =
                                           let uu____8410 =
                                             let uu____8413 =
                                               let uu____8414 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8414.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8413
                                              in
                                           uu____8410.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8409 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8425,uu____8426::is) ->
                                             let uu____8468 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8468
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8501 ->
                                             let uu____8502 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8502 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8518 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8518)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8523 =
                                           let uu____8524 =
                                             let uu____8527 =
                                               let uu____8528 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8528.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8527
                                              in
                                           uu____8524.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8523 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8539,uu____8540::is) ->
                                             let uu____8582 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8582
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8615 ->
                                             let uu____8616 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8616 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8632 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8632)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8637 =
                                         let uu____8638 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8638.FStar_Syntax_Syntax.n  in
                                       match uu____8637 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8643,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8698 ->
                                           let uu____8699 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8699 r
                                        in
                                     let uu____8708 =
                                       let uu____8709 =
                                         let uu____8710 =
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
                                             uu____8710;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8709
                                        in
                                     let uu____8733 =
                                       let uu____8734 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8734 g_guard
                                        in
                                     (uu____8708, uu____8733))))
  
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
                fun uu____8779  ->
                  let if_then_else1 =
                    let uu____8785 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8785 FStar_Util.must  in
                  let uu____8792 = destruct_wp_comp ct1  in
                  match uu____8792 with
                  | (uu____8803,uu____8804,wp_t) ->
                      let uu____8806 = destruct_wp_comp ct2  in
                      (match uu____8806 with
                       | (uu____8817,uu____8818,wp_e) ->
                           let wp =
                             let uu____8823 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8824 =
                               let uu____8829 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8830 =
                                 let uu____8831 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8840 =
                                   let uu____8851 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8860 =
                                     let uu____8871 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8880 =
                                       let uu____8891 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8891]  in
                                     uu____8871 :: uu____8880  in
                                   uu____8851 :: uu____8860  in
                                 uu____8831 :: uu____8840  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8829
                                 uu____8830
                                in
                             uu____8824 FStar_Pervasives_Native.None
                               uu____8823
                              in
                           let uu____8940 = mk_comp ed u_a a wp []  in
                           (uu____8940, FStar_TypeChecker_Env.trivial_guard))
  
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
        fun guard_x  ->
          let env =
            let uu____8994 =
              let uu____8995 =
                FStar_All.pipe_right guard_x FStar_Syntax_Syntax.mk_binder
                 in
              [uu____8995]  in
            FStar_TypeChecker_Env.push_binders env0 uu____8994  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9042  ->
                   match uu____9042 with
                   | (uu____9056,eff_label,uu____9058,uu____9059) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9072 =
            let uu____9080 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9118  ->
                      match uu____9118 with
                      | (uu____9133,uu____9134,flags,uu____9136) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9153  ->
                                  match uu___5_9153 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9156 -> false))))
               in
            if uu____9080
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9072 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9193 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9195 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9195
                then
                  let uu____9202 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9202, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9209 =
                         let uu____9218 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9218]  in
                       let uu____9237 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9209 uu____9237  in
                     let kwp =
                       let uu____9243 =
                         let uu____9252 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9252]  in
                       let uu____9271 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9243 uu____9271  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9278 =
                         let uu____9279 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9279]  in
                       let uu____9298 =
                         let uu____9301 =
                           let uu____9308 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9308
                            in
                         let uu____9309 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9301 uu____9309  in
                       FStar_Syntax_Util.abs uu____9278 uu____9298
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
                     let uu____9333 =
                       should_not_inline_whole_match ||
                         (let uu____9336 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9336)
                        in
                     if uu____9333 then cthen true else cthen false  in
                   let uu____9343 =
                     let uu____9354 =
                       FStar_All.pipe_right lcases
                         (FStar_List.map
                            (fun uu____9398  ->
                               match uu____9398 with
                               | (g,uu____9413,uu____9414,uu____9415) -> g))
                        in
                     FStar_All.pipe_right uu____9354
                       (FStar_List.fold_left
                          (fun uu____9459  ->
                             fun g  ->
                               match uu____9459 with
                               | (conds,acc) ->
                                   let cond =
                                     let uu____9500 =
                                       FStar_Syntax_Util.mk_neg g  in
                                     FStar_Syntax_Util.mk_conj acc uu____9500
                                      in
                                   ((FStar_List.append conds [cond]), cond))
                          ([], FStar_Syntax_Util.t_true))
                      in
                   match uu____9343 with
                   | (branch_conditions,uu____9528) ->
                       let uu____9541 =
                         FStar_List.fold_right2
                           (fun uu____9603  ->
                              fun bcond  ->
                                fun uu____9605  ->
                                  match (uu____9603, uu____9605) with
                                  | ((g,eff_label,uu____9665,cthen),(uu____9667,celse,g_comp))
                                      ->
                                      let uu____9714 =
                                        let uu____9719 =
                                          maybe_return eff_label cthen  in
                                        FStar_TypeChecker_Common.lcomp_comp
                                          uu____9719
                                         in
                                      (match uu____9714 with
                                       | (cthen1,gthen) ->
                                           let uu____9730 =
                                             let uu____9741 =
                                               lift_comps_sep_guards env
                                                 cthen1 celse
                                                 FStar_Pervasives_Native.None
                                                 false
                                                in
                                             match uu____9741 with
                                             | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                 ->
                                                 let md =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env m
                                                    in
                                                 let uu____9769 =
                                                   FStar_All.pipe_right
                                                     cthen2
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____9770 =
                                                   FStar_All.pipe_right
                                                     celse1
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 (md, uu____9769, uu____9770,
                                                   g_lift_then, g_lift_else)
                                              in
                                           (match uu____9730 with
                                            | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                                ->
                                                let fn =
                                                  let uu____9821 =
                                                    FStar_All.pipe_right md
                                                      FStar_Syntax_Util.is_layered
                                                     in
                                                  if uu____9821
                                                  then mk_layered_conjunction
                                                  else
                                                    mk_non_layered_conjunction
                                                   in
                                                let g_lift_then1 =
                                                  let uu____9856 =
                                                    FStar_Syntax_Util.mk_conj
                                                      bcond g
                                                     in
                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                    g_lift_then uu____9856
                                                   in
                                                let g_lift_else1 =
                                                  let uu____9858 =
                                                    let uu____9859 =
                                                      FStar_Syntax_Util.mk_neg
                                                        g
                                                       in
                                                    FStar_Syntax_Util.mk_conj
                                                      bcond uu____9859
                                                     in
                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                    g_lift_else uu____9858
                                                   in
                                                let g_lift =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g_lift_then1 g_lift_else1
                                                   in
                                                let uu____9863 =
                                                  let uu____9868 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env
                                                     in
                                                  fn env md u_res_t res_t g
                                                    ct_then ct_else
                                                    uu____9868
                                                   in
                                                (match uu____9863 with
                                                 | (c,g_conjunction) ->
                                                     let uu____9879 =
                                                       let uu____9880 =
                                                         let uu____9881 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             g_comp gthen
                                                            in
                                                         FStar_TypeChecker_Env.conj_guard
                                                           uu____9881 g_lift
                                                          in
                                                       FStar_TypeChecker_Env.conj_guard
                                                         uu____9880
                                                         g_conjunction
                                                        in
                                                     ((FStar_Pervasives_Native.Some
                                                         md), c, uu____9879)))))
                           lcases branch_conditions
                           (FStar_Pervasives_Native.None, default_case,
                             FStar_TypeChecker_Env.trivial_guard)
                          in
                       (match uu____9541 with
                        | (md,comp,g_comp) ->
                            let g_comp1 =
                              let uu____9898 =
                                let uu____9899 =
                                  FStar_All.pipe_right guard_x
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                [uu____9899]  in
                              FStar_TypeChecker_Env.close_guard env0
                                uu____9898 g_comp
                               in
                            (match lcases with
                             | [] -> (comp, g_comp1)
                             | uu____9942::[] -> (comp, g_comp1)
                             | uu____9985 ->
                                 let uu____10002 =
                                   let uu____10004 =
                                     FStar_All.pipe_right md FStar_Util.must
                                      in
                                   FStar_All.pipe_right uu____10004
                                     FStar_Syntax_Util.is_layered
                                    in
                                 if uu____10002
                                 then (comp, g_comp1)
                                 else
                                   (let comp1 =
                                      FStar_TypeChecker_Env.comp_to_comp_typ
                                        env comp
                                       in
                                    let md1 =
                                      FStar_TypeChecker_Env.get_effect_decl
                                        env
                                        comp1.FStar_Syntax_Syntax.effect_name
                                       in
                                    let uu____10017 = destruct_wp_comp comp1
                                       in
                                    match uu____10017 with
                                    | (uu____10028,uu____10029,wp) ->
                                        let ite_wp =
                                          let uu____10032 =
                                            FStar_All.pipe_right md1
                                              FStar_Syntax_Util.get_wp_ite_combinator
                                             in
                                          FStar_All.pipe_right uu____10032
                                            FStar_Util.must
                                           in
                                        let wp1 =
                                          let uu____10042 =
                                            let uu____10047 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [u_res_t] env md1 ite_wp
                                               in
                                            let uu____10048 =
                                              let uu____10049 =
                                                FStar_Syntax_Syntax.as_arg
                                                  res_t
                                                 in
                                              let uu____10058 =
                                                let uu____10069 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    wp
                                                   in
                                                [uu____10069]  in
                                              uu____10049 :: uu____10058  in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              uu____10047 uu____10048
                                             in
                                          uu____10042
                                            FStar_Pervasives_Native.None
                                            wp.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10102 =
                                          mk_comp md1 u_res_t res_t wp1
                                            bind_cases_flags
                                           in
                                        (uu____10102, g_comp1)))))
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
          let uu____10137 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10137 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10153 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10159 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10153 uu____10159
              else
                (let uu____10168 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10174 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10168 uu____10174)
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
          let uu____10199 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10199
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10202 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10202
        then u_res
        else
          (let is_total =
             let uu____10209 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10209
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10220 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10220 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10223 =
                    let uu____10229 =
                      let uu____10231 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10231
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10229)
                     in
                  FStar_Errors.raise_error uu____10223
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
      let uu____10255 = destruct_wp_comp ct  in
      match uu____10255 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10274 = FStar_TypeChecker_Env.get_range env  in
            let uu____10275 =
              let uu____10280 =
                let uu____10281 =
                  let uu____10282 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10282 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10281
                 in
              let uu____10289 =
                let uu____10290 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10299 =
                  let uu____10310 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10310]  in
                uu____10290 :: uu____10299  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10280 uu____10289  in
            uu____10275 FStar_Pervasives_Native.None uu____10274  in
          let uu____10343 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10343)
  
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
                  let uu____10398 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10398 with
                  | FStar_Pervasives_Native.Some uu____10413 ->
                      ((let uu____10431 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10431
                        then
                          let uu____10435 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10435
                        else ());
                       (let coercion =
                          let uu____10441 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10441
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10448 =
                            let uu____10449 =
                              let uu____10450 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10450
                               in
                            (FStar_Pervasives_Native.None, uu____10449)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10448
                           in
                        let e1 =
                          let uu____10456 =
                            let uu____10461 =
                              let uu____10462 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10462]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10461
                             in
                          uu____10456 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10496 =
                          let uu____10502 =
                            let uu____10504 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10504
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10502)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10496);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10523 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10541 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10552 -> false 
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
      let uu____10576 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10576 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10621 =
              let uu____10636 =
                let uu____10637 = FStar_Syntax_Subst.compress h1  in
                uu____10637.FStar_Syntax_Syntax.n  in
              (uu____10636, args)  in
            match uu____10621 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10684,uu____10685) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10718) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10739,branches),uu____10741) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10805 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10806 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10806 with
                               | (uu____10807,uu____10808,br_body) ->
                                   let uu____10826 =
                                     let uu____10827 =
                                       let uu____10832 =
                                         let uu____10833 =
                                           let uu____10836 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10836
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10833
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10832  in
                                     FStar_All.pipe_right br_body uu____10827
                                      in
                                   (match uu____10826 with
                                    | No  -> No
                                    | uu____10847 -> Maybe))) No)
            | uu____10848 -> No  in
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
            (((let uu____10900 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10900) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10919 =
                 let uu____10920 = FStar_Syntax_Subst.compress t1  in
                 uu____10920.FStar_Syntax_Syntax.n  in
               match uu____10919 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10925 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10935 =
                 let uu____10936 = FStar_Syntax_Subst.compress t1  in
                 uu____10936.FStar_Syntax_Syntax.n  in
               match uu____10935 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10941 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10951 =
                 let uu____10952 = FStar_Syntax_Subst.compress t1  in
                 uu____10952.FStar_Syntax_Syntax.n  in
               match uu____10951 with
               | FStar_Syntax_Syntax.Tm_type uu____10956 -> true
               | uu____10958 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10961 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10961 with
             | (head1,args) ->
                 ((let uu____11011 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11011
                   then
                     let uu____11015 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11017 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11019 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11021 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11015 uu____11017 uu____11019 uu____11021
                   else ());
                  (let mk_erased u t =
                     let uu____11039 =
                       let uu____11042 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11042 [u]  in
                     let uu____11043 =
                       let uu____11054 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11054]  in
                     FStar_Syntax_Util.mk_app uu____11039 uu____11043  in
                   let uu____11079 =
                     let uu____11094 =
                       let uu____11095 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11095.FStar_Syntax_Syntax.n  in
                     (uu____11094, args)  in
                   match uu____11079 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11133 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11133 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11173 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11173 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11213 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11213 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11253 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11253 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11274 ->
                       let uu____11289 =
                         let uu____11294 = check_erased env res_typ  in
                         let uu____11295 = check_erased env exp_t  in
                         (uu____11294, uu____11295)  in
                       (match uu____11289 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11304 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11304 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11315 =
                                   let uu____11320 =
                                     let uu____11321 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11321]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11320
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11315 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11356 =
                              let uu____11361 =
                                let uu____11362 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11362]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11361
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11356 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11395 ->
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
        let uu____11430 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11430 with
        | (hd1,args) ->
            let uu____11479 =
              let uu____11494 =
                let uu____11495 = FStar_Syntax_Subst.compress hd1  in
                uu____11495.FStar_Syntax_Syntax.n  in
              (uu____11494, args)  in
            (match uu____11479 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11533 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11560  -> FStar_Pervasives_Native.Some _11560)
                   uu____11533
             | uu____11561 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11614 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11614
           then
             let uu____11617 = FStar_Syntax_Print.term_to_string e  in
             let uu____11619 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11621 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11617 uu____11619 uu____11621
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____11631 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11631 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11656 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11682 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11682, false)
             else
               (let uu____11692 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11692, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11705) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11717 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11717
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1371_11733 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1371_11733.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1371_11733.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1371_11733.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11740 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11740 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11756 =
                      let uu____11757 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11757 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11777 =
                            let uu____11779 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11779 = FStar_Syntax_Util.Equal  in
                          if uu____11777
                          then
                            ((let uu____11786 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11786
                              then
                                let uu____11790 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11792 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11790 uu____11792
                              else ());
                             (let uu____11797 = set_result_typ1 c  in
                              (uu____11797, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11804 ->
                                   true
                               | uu____11812 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11821 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11821
                                  in
                               let lc1 =
                                 let uu____11823 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11824 =
                                   let uu____11825 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11825)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11823 uu____11824
                                  in
                               ((let uu____11829 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11829
                                 then
                                   let uu____11833 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11835 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11837 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11839 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11833 uu____11835 uu____11837
                                     uu____11839
                                 else ());
                                (let uu____11844 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11844 with
                                 | (c1,g_lc) ->
                                     let uu____11855 = set_result_typ1 c1  in
                                     let uu____11856 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11855, uu____11856)))
                             else
                               ((let uu____11860 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11860
                                 then
                                   let uu____11864 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11866 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11864 uu____11866
                                 else ());
                                (let uu____11871 = set_result_typ1 c  in
                                 (uu____11871, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1408_11875 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1408_11875.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1408_11875.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1408_11875.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11885 =
                      let uu____11886 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11886
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11896 =
                           let uu____11897 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11897.FStar_Syntax_Syntax.n  in
                         match uu____11896 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11904,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11906;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11907;_},uu____11908)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1424_11934 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1424_11934.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1424_11934.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1424_11934.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11935 ->
                             let uu____11936 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11936 with
                              | (c,g_c) ->
                                  ((let uu____11948 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11948
                                    then
                                      let uu____11952 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11954 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11956 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11958 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11952 uu____11954 uu____11956
                                        uu____11958
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
                                        let uu____11971 =
                                          let uu____11976 =
                                            let uu____11977 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11977]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11976
                                           in
                                        uu____11971
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12004 =
                                      let uu____12009 =
                                        FStar_All.pipe_left
                                          (fun _12030  ->
                                             FStar_Pervasives_Native.Some
                                               _12030)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12031 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12032 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12033 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12009
                                        uu____12031 e uu____12032 uu____12033
                                       in
                                    match uu____12004 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1442_12041 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1442_12041.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1442_12041.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12043 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12043
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12046 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12046 with
                                         | (c2,g_lc) ->
                                             ((let uu____12058 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12058
                                               then
                                                 let uu____12062 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12062
                                               else ());
                                              (let uu____12067 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12067))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12076  ->
                              match uu___6_12076 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12079 -> []))
                       in
                    let lc1 =
                      let uu____12081 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12081 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1458_12083 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1458_12083.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1458_12083.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1458_12083.FStar_TypeChecker_Common.implicits)
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
        let uu____12119 =
          let uu____12122 =
            let uu____12127 =
              let uu____12128 =
                let uu____12137 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12137  in
              [uu____12128]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12127  in
          uu____12122 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12119  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12160 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12160
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12179 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12195 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12212 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12212
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12228)::(ens,uu____12230)::uu____12231 ->
                    let uu____12274 =
                      let uu____12277 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12277  in
                    let uu____12278 =
                      let uu____12279 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12279  in
                    (uu____12274, uu____12278)
                | uu____12282 ->
                    let uu____12293 =
                      let uu____12299 =
                        let uu____12301 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12301
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12299)
                       in
                    FStar_Errors.raise_error uu____12293
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12321)::uu____12322 ->
                    let uu____12349 =
                      let uu____12354 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12354
                       in
                    (match uu____12349 with
                     | (us_r,uu____12386) ->
                         let uu____12387 =
                           let uu____12392 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12392
                            in
                         (match uu____12387 with
                          | (us_e,uu____12424) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12427 =
                                  let uu____12428 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12428
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12427
                                  us_r
                                 in
                              let as_ens =
                                let uu____12430 =
                                  let uu____12431 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12431
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12430
                                  us_e
                                 in
                              let req =
                                let uu____12435 =
                                  let uu____12440 =
                                    let uu____12441 =
                                      let uu____12452 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12452]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12441
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12440
                                   in
                                uu____12435 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12492 =
                                  let uu____12497 =
                                    let uu____12498 =
                                      let uu____12509 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12509]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12498
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12497
                                   in
                                uu____12492 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12546 =
                                let uu____12549 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12549  in
                              let uu____12550 =
                                let uu____12551 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12551  in
                              (uu____12546, uu____12550)))
                | uu____12554 -> failwith "Impossible"))
  
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
        (let uu____12593 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12593
         then
           let uu____12598 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12600 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12598
             uu____12600
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
          (let uu____12659 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12659
           then
             let uu____12664 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12666 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12664
               uu____12666
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12677 =
      let uu____12679 =
        let uu____12680 = FStar_Syntax_Subst.compress t  in
        uu____12680.FStar_Syntax_Syntax.n  in
      match uu____12679 with
      | FStar_Syntax_Syntax.Tm_app uu____12684 -> false
      | uu____12702 -> true  in
    if uu____12677
    then t
    else
      (let uu____12707 = FStar_Syntax_Util.head_and_args t  in
       match uu____12707 with
       | (head1,args) ->
           let uu____12750 =
             let uu____12752 =
               let uu____12753 = FStar_Syntax_Subst.compress head1  in
               uu____12753.FStar_Syntax_Syntax.n  in
             match uu____12752 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12758 -> false  in
           if uu____12750
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12790 ->
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
          ((let uu____12837 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12837
            then
              let uu____12840 = FStar_Syntax_Print.term_to_string e  in
              let uu____12842 = FStar_Syntax_Print.term_to_string t  in
              let uu____12844 =
                let uu____12846 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12846
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12840 uu____12842 uu____12844
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____12859 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____12859 with
              | (formals,uu____12875) ->
                  let n_implicits =
                    let uu____12897 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____12975  ->
                              match uu____12975 with
                              | (uu____12983,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____12990 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____12990 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____12897 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____13115 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13115 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13129 =
                      let uu____13135 =
                        let uu____13137 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13139 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13141 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13137 uu____13139 uu____13141
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13135)
                       in
                    let uu____13145 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13129 uu____13145
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13163 =
              match uu___7_13163 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13206 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13206 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13337,uu____13324)
                           when _13337 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13370,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13372))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13406 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13406 with
                            | (v1,uu____13447,g) ->
                                ((let uu____13462 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13462
                                  then
                                    let uu____13465 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13465
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13475 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13475 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13568 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13568))))
                       | (uu____13595,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13632 =
                             let uu____13645 =
                               let uu____13652 =
                                 let uu____13657 = FStar_Dyn.mkdyn env  in
                                 (uu____13657, tau)  in
                               FStar_Pervasives_Native.Some uu____13652  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13645
                              in
                           (match uu____13632 with
                            | (v1,uu____13690,g) ->
                                ((let uu____13705 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13705
                                  then
                                    let uu____13708 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13708
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13718 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13718 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13811 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13811))))
                       | (uu____13838,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13886 =
                       let uu____13913 = inst_n_binders t1  in
                       aux [] uu____13913 bs1  in
                     (match uu____13886 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____13985) -> (e, torig, guard)
                           | (uu____14016,[]) when
                               let uu____14047 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14047 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14049 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14077 ->
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
            | uu____14090 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14102 =
      let uu____14106 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14106
        (FStar_List.map
           (fun u  ->
              let uu____14118 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14118 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14102 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14146 = FStar_Util.set_is_empty x  in
      if uu____14146
      then []
      else
        (let s =
           let uu____14164 =
             let uu____14167 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14167  in
           FStar_All.pipe_right uu____14164 FStar_Util.set_elements  in
         (let uu____14183 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14183
          then
            let uu____14188 =
              let uu____14190 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14190  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14188
          else ());
         (let r =
            let uu____14199 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14199  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14238 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14238
                     then
                       let uu____14243 =
                         let uu____14245 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14245
                          in
                       let uu____14249 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14251 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14243 uu____14249 uu____14251
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
        let uu____14281 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14281 FStar_Util.set_elements  in
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
        | ([],uu____14320) -> generalized_univ_names
        | (uu____14327,[]) -> explicit_univ_names
        | uu____14334 ->
            let uu____14343 =
              let uu____14349 =
                let uu____14351 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14351
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14349)
               in
            FStar_Errors.raise_error uu____14343 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14373 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14373
       then
         let uu____14378 = FStar_Syntax_Print.term_to_string t  in
         let uu____14380 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14378 uu____14380
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14389 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14389
        then
          let uu____14394 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14394
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14403 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14403
         then
           let uu____14408 = FStar_Syntax_Print.term_to_string t  in
           let uu____14410 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14408 uu____14410
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
        let uu____14494 =
          let uu____14496 =
            FStar_Util.for_all
              (fun uu____14510  ->
                 match uu____14510 with
                 | (uu____14520,uu____14521,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14496  in
        if uu____14494
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14573 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14573
              then
                let uu____14576 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14576
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14583 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14583
               then
                 let uu____14586 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14586
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14604 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14604 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14638 =
             match uu____14638 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14675 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14675
                   then
                     let uu____14680 =
                       let uu____14682 =
                         let uu____14686 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14686
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14682
                         (FStar_String.concat ", ")
                        in
                     let uu____14734 =
                       let uu____14736 =
                         let uu____14740 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14740
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14753 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14755 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14753
                                   uu____14755))
                          in
                       FStar_All.pipe_right uu____14736
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14680
                       uu____14734
                   else ());
                  (let univs2 =
                     let uu____14769 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14781 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14781) univs1
                       uu____14769
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14788 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14788
                    then
                      let uu____14793 =
                        let uu____14795 =
                          let uu____14799 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____14799
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14795
                          (FStar_String.concat ", ")
                         in
                      let uu____14847 =
                        let uu____14849 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14863 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14865 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14863
                                    uu____14865))
                           in
                        FStar_All.pipe_right uu____14849
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14793 uu____14847
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____14886 =
             let uu____14903 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14903  in
           match uu____14886 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____14993 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____14993
                 then ()
                 else
                   (let uu____14998 = lec_hd  in
                    match uu____14998 with
                    | (lb1,uu____15006,uu____15007) ->
                        let uu____15008 = lec2  in
                        (match uu____15008 with
                         | (lb2,uu____15016,uu____15017) ->
                             let msg =
                               let uu____15020 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15022 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15020 uu____15022
                                in
                             let uu____15025 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15025))
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
                 let uu____15093 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15093
                 then ()
                 else
                   (let uu____15098 = lec_hd  in
                    match uu____15098 with
                    | (lb1,uu____15106,uu____15107) ->
                        let uu____15108 = lec2  in
                        (match uu____15108 with
                         | (lb2,uu____15116,uu____15117) ->
                             let msg =
                               let uu____15120 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15122 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15120 uu____15122
                                in
                             let uu____15125 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15125))
                  in
               let lecs1 =
                 let uu____15136 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15189 = univs_and_uvars_of_lec this_lec  in
                        match uu____15189 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15136 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15294 = lec_hd  in
                   match uu____15294 with
                   | (lbname,e,c) ->
                       let uu____15304 =
                         let uu____15310 =
                           let uu____15312 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15314 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15316 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15312 uu____15314 uu____15316
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15310)
                          in
                       let uu____15320 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15304 uu____15320
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15339 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15339 with
                         | FStar_Pervasives_Native.Some uu____15348 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15356 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15360 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15360 with
                              | (bs,kres) ->
                                  ((let uu____15404 =
                                      let uu____15405 =
                                        let uu____15408 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15408
                                         in
                                      uu____15405.FStar_Syntax_Syntax.n  in
                                    match uu____15404 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15409
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15413 =
                                          let uu____15415 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15415  in
                                        if uu____15413
                                        then fail1 kres
                                        else ()
                                    | uu____15420 -> fail1 kres);
                                   (let a =
                                      let uu____15422 =
                                        let uu____15425 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15428  ->
                                             FStar_Pervasives_Native.Some
                                               _15428) uu____15425
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15422
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15436 ->
                                          let uu____15445 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15445
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
                      (fun uu____15548  ->
                         match uu____15548 with
                         | (lbname,e,c) ->
                             let uu____15594 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15655 ->
                                   let uu____15668 = (e, c)  in
                                   (match uu____15668 with
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
                                                (fun uu____15708  ->
                                                   match uu____15708 with
                                                   | (x,uu____15714) ->
                                                       let uu____15715 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15715)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15733 =
                                                let uu____15735 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15735
                                                 in
                                              if uu____15733
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
                                          let uu____15744 =
                                            let uu____15745 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15745.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15744 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15770 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15770 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15781 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15785 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15785, gen_tvars))
                                in
                             (match uu____15594 with
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
        (let uu____15932 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15932
         then
           let uu____15935 =
             let uu____15937 =
               FStar_List.map
                 (fun uu____15952  ->
                    match uu____15952 with
                    | (lb,uu____15961,uu____15962) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15937 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15935
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15988  ->
                match uu____15988 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16017 = gen env is_rec lecs  in
           match uu____16017 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16116  ->
                       match uu____16116 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16178 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16178
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16226  ->
                           match uu____16226 with
                           | (l,us,e,c,gvs) ->
                               let uu____16260 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16262 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16264 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16266 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16268 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16260 uu____16262 uu____16264
                                 uu____16266 uu____16268))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16313  ->
                match uu____16313 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16357 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16357, t, c, gvs)) univnames_lecs
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
        let uu____16412 =
          let uu____16416 =
            let uu____16418 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16418  in
          FStar_Pervasives_Native.Some uu____16416  in
        FStar_Profiling.profile
          (fun uu____16435  -> generalize' env is_rec lecs) uu____16412
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
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
            else
              (let uu____16495 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____16495 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____16501 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _16504  -> FStar_Pervasives_Native.Some _16504)
                     uu____16501)
             in
          let uu____16505 = maybe_coerce_lc env1 e lc t2  in
          match uu____16505 with
          | (e1,lc1,g_c) ->
              let uu____16521 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16521 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16530 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16536 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16530 uu____16536
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16545 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16545
                     then
                       let uu____16550 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16550
                     else ());
                    (let uu____16556 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16556))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16584 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16584
         then
           let uu____16587 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16587
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16601 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16601 with
         | (c,g_c) ->
             let uu____16613 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16613
             then
               let uu____16621 =
                 let uu____16623 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16623  in
               (uu____16621, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16631 =
                    let uu____16632 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16632
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16631
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16633 = check_trivial_precondition env c1  in
                match uu____16633 with
                | (ct,vc,g_pre) ->
                    ((let uu____16649 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16649
                      then
                        let uu____16654 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16654
                      else ());
                     (let uu____16659 =
                        let uu____16661 =
                          let uu____16662 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16662  in
                        discharge uu____16661  in
                      let uu____16663 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16659, uu____16663)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16697 =
        match uu___8_16697 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16707)::[] -> f fst1
        | uu____16732 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16744 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16744
          (fun _16745  -> FStar_TypeChecker_Common.NonTrivial _16745)
         in
      let op_or_e e =
        let uu____16756 =
          let uu____16757 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16757  in
        FStar_All.pipe_right uu____16756
          (fun _16760  -> FStar_TypeChecker_Common.NonTrivial _16760)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16767  -> FStar_TypeChecker_Common.NonTrivial _16767)
         in
      let op_or_t t =
        let uu____16778 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16778
          (fun _16781  -> FStar_TypeChecker_Common.NonTrivial _16781)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16788  -> FStar_TypeChecker_Common.NonTrivial _16788)
         in
      let short_op_ite uu___9_16794 =
        match uu___9_16794 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16804)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16831)::[] ->
            let uu____16872 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16872
              (fun _16873  -> FStar_TypeChecker_Common.NonTrivial _16873)
        | uu____16874 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16886 =
          let uu____16894 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16894)  in
        let uu____16902 =
          let uu____16912 =
            let uu____16920 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16920)  in
          let uu____16928 =
            let uu____16938 =
              let uu____16946 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16946)  in
            let uu____16954 =
              let uu____16964 =
                let uu____16972 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____16972)  in
              let uu____16980 =
                let uu____16990 =
                  let uu____16998 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____16998)  in
                [uu____16990; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____16964 :: uu____16980  in
            uu____16938 :: uu____16954  in
          uu____16912 :: uu____16928  in
        uu____16886 :: uu____16902  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17060 =
            FStar_Util.find_map table
              (fun uu____17075  ->
                 match uu____17075 with
                 | (x,mk1) ->
                     let uu____17092 = FStar_Ident.lid_equals x lid  in
                     if uu____17092
                     then
                       let uu____17097 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17097
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17060 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17101 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17109 =
      let uu____17110 = FStar_Syntax_Util.un_uinst l  in
      uu____17110.FStar_Syntax_Syntax.n  in
    match uu____17109 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17115 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17151)::uu____17152 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17171 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17180,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17181))::uu____17182 -> bs
      | uu____17200 ->
          let uu____17201 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17201 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17205 =
                 let uu____17206 = FStar_Syntax_Subst.compress t  in
                 uu____17206.FStar_Syntax_Syntax.n  in
               (match uu____17205 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17210) ->
                    let uu____17231 =
                      FStar_Util.prefix_until
                        (fun uu___10_17271  ->
                           match uu___10_17271 with
                           | (uu____17279,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17280)) ->
                               false
                           | uu____17285 -> true) bs'
                       in
                    (match uu____17231 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17321,uu____17322) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17394,uu____17395) ->
                         let uu____17468 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17488  ->
                                   match uu____17488 with
                                   | (x,uu____17497) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17468
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17546  ->
                                     match uu____17546 with
                                     | (x,i) ->
                                         let uu____17565 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17565, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17576 -> bs))
  
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
            let uu____17605 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17605
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
          let uu____17636 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17636
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
        (let uu____17679 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17679
         then
           ((let uu____17684 = FStar_Ident.text_of_lid lident  in
             d uu____17684);
            (let uu____17686 = FStar_Ident.text_of_lid lident  in
             let uu____17688 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17686 uu____17688))
         else ());
        (let fv =
           let uu____17694 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17694
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
         let uu____17706 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2067_17708 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2067_17708.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2067_17708.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2067_17708.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2067_17708.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2067_17708.FStar_Syntax_Syntax.sigopts)
           }), uu____17706))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17726 =
        match uu___11_17726 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17729 -> false  in
      let reducibility uu___12_17737 =
        match uu___12_17737 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17744 -> false  in
      let assumption uu___13_17752 =
        match uu___13_17752 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17756 -> false  in
      let reification uu___14_17764 =
        match uu___14_17764 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17767 -> true
        | uu____17769 -> false  in
      let inferred uu___15_17777 =
        match uu___15_17777 with
        | FStar_Syntax_Syntax.Discriminator uu____17779 -> true
        | FStar_Syntax_Syntax.Projector uu____17781 -> true
        | FStar_Syntax_Syntax.RecordType uu____17787 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17797 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17810 -> false  in
      let has_eq uu___16_17818 =
        match uu___16_17818 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17822 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17901 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17908 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17941 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17941))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17972 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____17972
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
           | FStar_Syntax_Syntax.Sig_bundle uu____17992 ->
               let uu____18001 =
                 let uu____18003 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18009  ->
                           match uu___17_18009 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18012 -> false))
                    in
                 Prims.op_Negation uu____18003  in
               if uu____18001
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18019 -> ()
           | uu____18026 ->
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
      let uu____18040 =
        let uu____18042 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18048  ->
                  match uu___18_18048 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18051 -> false))
           in
        FStar_All.pipe_right uu____18042 Prims.op_Negation  in
      if uu____18040
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18072 =
            let uu____18078 =
              let uu____18080 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18080 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18078)  in
          FStar_Errors.raise_error uu____18072 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18098 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18106 =
            let uu____18108 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18108  in
          if uu____18106 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18119),uu____18120) ->
              ((let uu____18132 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18132
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18141 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18141
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18152 ->
              ((let uu____18162 =
                  let uu____18164 =
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
                  Prims.op_Negation uu____18164  in
                if uu____18162 then err'1 () else ());
               (let uu____18174 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18180  ->
                           match uu___19_18180 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18183 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18174
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18189 ->
              let uu____18196 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18196 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18204 ->
              let uu____18211 =
                let uu____18213 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18213  in
              if uu____18211 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18223 ->
              let uu____18224 =
                let uu____18226 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18226  in
              if uu____18224 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18236 ->
              let uu____18249 =
                let uu____18251 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18251  in
              if uu____18249 then err'1 () else ()
          | uu____18261 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18300 =
          let uu____18301 = FStar_Syntax_Subst.compress t1  in
          uu____18301.FStar_Syntax_Syntax.n  in
        match uu____18300 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18305 ->
            let uu____18320 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18320 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18353;
               FStar_Syntax_Syntax.index = uu____18354;
               FStar_Syntax_Syntax.sort = t2;_},uu____18356)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18365) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18391) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18397 -> false
      
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
        (let uu____18407 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18407
         then
           let uu____18412 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18412
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
                  let uu____18477 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18477 r  in
                let uu____18487 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18487 with
                | (uu____18496,signature) ->
                    let uu____18498 =
                      let uu____18499 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18499.FStar_Syntax_Syntax.n  in
                    (match uu____18498 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18507) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18555 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18570 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18572 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18570 eff_name.FStar_Ident.str
                                       uu____18572) r
                                 in
                              (match uu____18555 with
                               | (is,g) ->
                                   let uu____18585 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18587 =
                                             let uu____18588 =
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
                                                 = uu____18588;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18587
                                            in
                                         let uu____18607 =
                                           let uu____18614 =
                                             let uu____18615 =
                                               let uu____18630 =
                                                 let uu____18639 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18639]  in
                                               (uu____18630, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18615
                                              in
                                           FStar_Syntax_Syntax.mk uu____18614
                                            in
                                         uu____18607
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18670 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18670
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18679 =
                                           let uu____18684 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18684
                                            in
                                         uu____18679
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18585, g))
                          | uu____18693 -> fail1 signature)
                     | uu____18694 -> fail1 signature)
  
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
            let uu____18725 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18725
              (fun ed  ->
                 let uu____18733 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18733 u a_tm)
  
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
              let uu____18769 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18769 with
              | (uu____18774,sig_tm) ->
                  let fail1 t =
                    let uu____18782 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18782 r  in
                  let uu____18788 =
                    let uu____18789 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18789.FStar_Syntax_Syntax.n  in
                  (match uu____18788 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18793) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18816)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18838 -> fail1 sig_tm)
                   | uu____18839 -> fail1 sig_tm)
  
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
          (let uu____18870 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18870
           then
             let uu____18875 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18877 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18875 uu____18877
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18884 =
             let uu____18895 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18896 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18895, (ct.FStar_Syntax_Syntax.result_typ), uu____18896)
              in
           match uu____18884 with
           | (u,a,c_is) ->
               let uu____18944 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18944 with
                | (uu____18953,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18964 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18966 = FStar_Ident.string_of_lid tgt  in
                      let uu____18968 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18964 uu____18966 s uu____18968
                       in
                    let uu____18971 =
                      let uu____19004 =
                        let uu____19005 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19005.FStar_Syntax_Syntax.n  in
                      match uu____19004 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19069 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19069 with
                           | (a_b::bs1,c2) ->
                               let uu____19129 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19129, c2))
                      | uu____19217 ->
                          let uu____19218 =
                            let uu____19224 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19224)
                             in
                          FStar_Errors.raise_error uu____19218 r
                       in
                    (match uu____18971 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19342 =
                           let uu____19349 =
                             let uu____19350 =
                               let uu____19351 =
                                 let uu____19358 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19358, a)  in
                               FStar_Syntax_Syntax.NT uu____19351  in
                             [uu____19350]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19349
                             (fun b  ->
                                let uu____19375 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19377 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19379 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19381 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19375 uu____19377 uu____19379
                                  uu____19381) r
                            in
                         (match uu____19342 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19395 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19395
                                then
                                  let uu____19400 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19409 =
                                             let uu____19411 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19411
                                              in
                                           Prims.op_Hat s uu____19409) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19400
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19442 =
                                           let uu____19449 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19449, t)  in
                                         FStar_Syntax_Syntax.NT uu____19442)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19468 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19468
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19474 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19474
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19483 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19483)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19485 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19485
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19489 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19489 r
                                   in
                                let fml =
                                  let uu____19494 =
                                    let uu____19499 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19500 =
                                      let uu____19501 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19501
                                       in
                                    (uu____19499, uu____19500)  in
                                  match uu____19494 with
                                  | (u1,wp) ->
                                      let trivial_post =
                                        let ts =
                                          let uu____19528 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.trivial_pure_post_lid
                                             in
                                          FStar_All.pipe_right uu____19528
                                            FStar_Util.must
                                           in
                                        let uu____19533 =
                                          FStar_TypeChecker_Env.inst_tscheme_with
                                            ts [u1]
                                           in
                                        match uu____19533 with
                                        | (uu____19538,t) ->
                                            let uu____19540 =
                                              let uu____19545 =
                                                let uu____19546 =
                                                  FStar_All.pipe_right
                                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____19546]  in
                                              FStar_Syntax_Syntax.mk_Tm_app t
                                                uu____19545
                                               in
                                            uu____19540
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                         in
                                      let uu____19579 =
                                        let uu____19584 =
                                          let uu____19585 =
                                            FStar_All.pipe_right trivial_post
                                              FStar_Syntax_Syntax.as_arg
                                             in
                                          [uu____19585]  in
                                        FStar_Syntax_Syntax.mk_Tm_app wp
                                          uu____19584
                                         in
                                      uu____19579
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                   in
                                (let uu____19619 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19619
                                 then
                                   let uu____19625 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19625
                                 else ());
                                (let c1 =
                                   let uu____19631 =
                                     let uu____19632 =
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
                                         uu____19632;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19631
                                    in
                                 (let uu____19656 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19656
                                  then
                                    let uu____19661 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19661
                                  else ());
                                 (let uu____19666 =
                                    let uu____19667 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19668 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19667 uu____19668
                                     in
                                  (c1, uu____19666)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19682 .
    'Auu____19682 ->
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
              let uu____19711 =
                let uu____19716 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19716
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19711 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19759 =
                let uu____19760 =
                  let uu____19763 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19763
                    FStar_Syntax_Subst.compress
                   in
                uu____19760.FStar_Syntax_Syntax.n  in
              match uu____19759 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19786::bs,uu____19788)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19828 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19828
                    FStar_Pervasives_Native.fst
              | uu____19934 ->
                  let uu____19935 =
                    let uu____19941 =
                      let uu____19943 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19943
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19941)  in
                  FStar_Errors.raise_error uu____19935
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19970 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19979 =
                let uu____19990 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20026  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20033 =
                  let uu____20044 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20044]  in
                FStar_List.append uu____19990 uu____20033  in
              uu____19970 :: uu____19979  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20115 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20115 with
        | (uu____20120,t) ->
            let err n1 =
              let uu____20130 =
                let uu____20136 =
                  let uu____20138 = FStar_Ident.string_of_lid datacon  in
                  let uu____20140 = FStar_Util.string_of_int n1  in
                  let uu____20142 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20138 uu____20140 uu____20142
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20136)
                 in
              let uu____20146 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20130 uu____20146  in
            let uu____20147 =
              let uu____20148 = FStar_Syntax_Subst.compress t  in
              uu____20148.FStar_Syntax_Syntax.n  in
            (match uu____20147 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20152) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20207  ->
                           match uu____20207 with
                           | (uu____20215,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20224 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____20256 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____20256
                      FStar_Pervasives_Native.fst)
             | uu____20267 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20280 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20280
      then
        let uu____20283 =
          let uu____20296 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20296
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20283;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20331 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20331 with
           | (uu____20340,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20359 =
                 let uu____20360 =
                   let uu___2446_20361 = ct  in
                   let uu____20362 =
                     let uu____20373 =
                       let uu____20382 =
                         let uu____20383 =
                           let uu____20390 =
                             let uu____20391 =
                               let uu____20408 =
                                 let uu____20419 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20419; wp]  in
                               (lift_t, uu____20408)  in
                             FStar_Syntax_Syntax.Tm_app uu____20391  in
                           FStar_Syntax_Syntax.mk uu____20390  in
                         uu____20383 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20382
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20373]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2446_20361.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2446_20361.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20362;
                     FStar_Syntax_Syntax.flags =
                       (uu___2446_20361.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20360  in
               (uu____20359, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20519 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20519 with
           | (uu____20526,lift_t) ->
               let uu____20528 =
                 let uu____20535 =
                   let uu____20536 =
                     let uu____20553 =
                       let uu____20564 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20573 =
                         let uu____20584 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20593 =
                           let uu____20604 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20604]  in
                         uu____20584 :: uu____20593  in
                       uu____20564 :: uu____20573  in
                     (lift_t, uu____20553)  in
                   FStar_Syntax_Syntax.Tm_app uu____20536  in
                 FStar_Syntax_Syntax.mk uu____20535  in
               uu____20528 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20657 =
           let uu____20670 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20670 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20657;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20706  ->
                        fun uu____20707  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20730 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20730
  
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
  