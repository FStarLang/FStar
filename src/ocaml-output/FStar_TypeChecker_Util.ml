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
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4496 ->
                                                let uu____4497 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4497 r1
                                             in
                                          (match uu____3916 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4622 =
                                                 let uu____4629 =
                                                   let uu____4630 =
                                                     let uu____4631 =
                                                       let uu____4638 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4638, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4631
                                                      in
                                                   let uu____4649 =
                                                     let uu____4652 =
                                                       let uu____4653 =
                                                         let uu____4660 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4660, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4653
                                                        in
                                                     [uu____4652]  in
                                                   uu____4630 :: uu____4649
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4629
                                                   (fun b1  ->
                                                      let uu____4676 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4678 =
                                                        let uu____4680 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4682 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4684 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4680
                                                          uu____4682
                                                          uu____4684
                                                         in
                                                      let uu____4687 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4676 uu____4678
                                                        uu____4687) r1
                                                  in
                                               (match uu____4622 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4724 =
                                                               let uu____4731
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4731,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4724)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4758 =
                                                          let uu____4761 =
                                                            let uu____4762 =
                                                              let uu____4763
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4763.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4762
                                                             in
                                                          let uu____4772 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4761
                                                            uu____4772 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4758
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4785
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4785)
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
                                                        let uu____4804 =
                                                          let uu____4805 =
                                                            let uu____4808 =
                                                              let uu____4809
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4809.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4808
                                                             in
                                                          uu____4805.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4804 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4842 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4842
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4852
                                                                    =
                                                                    let uu____4859
                                                                    =
                                                                    let uu____4860
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4860
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4881
                                                                    =
                                                                    let uu____4884
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4884
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4859,
                                                                    uu____4881)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4852
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4898
                                                                   =
                                                                   let uu____4901
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4902
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4901
                                                                    uu____4902
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4898
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4921 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4929
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4929)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4921
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4943 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst1)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4943
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4945 =
                                                        let uu____4950 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4951 =
                                                          let uu____4952 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4952
                                                           in
                                                        (uu____4950,
                                                          uu____4951)
                                                         in
                                                      match uu____4945 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4978 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4979 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4978 uu____4979
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4982 =
                                                        let uu____4983 =
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
                                                            = uu____4983;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4982
                                                       in
                                                    ((let uu____5003 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____5003
                                                      then
                                                        let uu____5008 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____5008
                                                      else ());
                                                     (let uu____5013 =
                                                        let uu____5014 =
                                                          let uu____5017 =
                                                            let uu____5020 =
                                                              let uu____5023
                                                                =
                                                                let uu____5026
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____5026]
                                                                 in
                                                              g_guard ::
                                                                uu____5023
                                                               in
                                                            f_guard ::
                                                              uu____5020
                                                             in
                                                          g_uvars ::
                                                            uu____5017
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____5014
                                                         in
                                                      (c, uu____5013)))))))))
  
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
                let uu____5071 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5097 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5097 with
                  | (a,kwp) ->
                      let uu____5128 = destruct_wp_comp ct1  in
                      let uu____5135 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5128, uu____5135)
                   in
                match uu____5071 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5188 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5188]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5208 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5208]
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
                      let uu____5255 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5264 =
                        let uu____5275 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5284 =
                          let uu____5295 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5304 =
                            let uu____5315 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5324 =
                              let uu____5335 =
                                let uu____5344 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5344  in
                              [uu____5335]  in
                            uu____5315 :: uu____5324  in
                          uu____5295 :: uu____5304  in
                        uu____5275 :: uu____5284  in
                      uu____5255 :: uu____5264  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5397 =
                        let uu____5402 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5402 wp_args  in
                      uu____5397 FStar_Pervasives_Native.None
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
              let uu____5450 =
                let uu____5455 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5456 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5455, uu____5456)  in
              match uu____5450 with
              | (ct1,ct2) ->
                  let uu____5463 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5463 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5514 = lift_comps env c1 c2 b true  in
                       (match uu____5514 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5532 =
                              let uu____5537 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5538 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5537, uu____5538)  in
                            (match uu____5532 with
                             | (ct11,ct21) ->
                                 let uu____5545 =
                                   let uu____5550 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5550
                                   then
                                     let bind_t =
                                       let uu____5558 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5558
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5561 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5561,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5545 with
                                  | (c,g_bind) ->
                                      let uu____5568 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5568)))))
  
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
            let uu____5604 =
              let uu____5605 =
                let uu____5616 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5616]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5605;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5604  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5661 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5667  ->
              match uu___1_5667 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5670 -> false))
       in
    if uu____5661
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5682  ->
              match uu___2_5682 with
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
        let uu____5710 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5710
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5721 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5721  in
           let pure_assume_wp1 =
             let uu____5726 = FStar_TypeChecker_Env.get_range env  in
             let uu____5727 =
               let uu____5732 =
                 let uu____5733 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5733]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5732  in
             uu____5727 FStar_Pervasives_Native.None uu____5726  in
           let uu____5766 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5766)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5794 =
          let uu____5795 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5795 with
          | (c,g_c) ->
              let uu____5806 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5806
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5820 = weaken_comp env c f1  in
                     (match uu____5820 with
                      | (c1,g_w) ->
                          let uu____5831 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5831)))
           in
        let uu____5832 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5832 weaken
  
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
                 let uu____5889 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5889  in
               let pure_assert_wp1 =
                 let uu____5894 =
                   let uu____5899 =
                     let uu____5900 =
                       let uu____5909 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5909
                        in
                     [uu____5900]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5899
                    in
                 uu____5894 FStar_Pervasives_Native.None r  in
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
       (let uu____6001 = FStar_Options.debug_any ()  in
        if uu____6001
        then
          let uu____6004 = FStar_Util.string_of_int n1  in
          let uu____6006 =
            let uu____6008 =
              let uu____6010 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____6010  in
            FStar_Util.string_of_int uu____6008  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____6004
            uu____6006
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
            let uu____6065 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____6065
            then (lc, g0)
            else
              (let flags =
                 let uu____6077 =
                   let uu____6085 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____6085
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____6077 with
                 | (maybe_trivial_post,flags) ->
                     let uu____6115 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_6123  ->
                               match uu___3_6123 with
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
                               | uu____6126 -> []))
                        in
                     FStar_List.append flags uu____6115
                  in
               let strengthen uu____6136 =
                 let uu____6137 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6137 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6156 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6156 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6163 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6163
                              then
                                let uu____6167 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6169 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6167 uu____6169
                              else ());
                             (let uu____6174 =
                                strengthen_comp env reason c f flags  in
                              match uu____6174 with
                              | (c1,g_s) ->
                                  let uu____6185 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6185))))
                  in
               let uu____6186 =
                 let uu____6187 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6187
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6186,
                 (let uu___716_6189 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___716_6189.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___716_6189.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___716_6189.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6198  ->
            match uu___4_6198 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6202 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6231 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6231
          then e
          else
            (let uu____6238 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6241 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6241)
                in
             if uu____6238
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
                | uu____6311 -> false  in
              if is_unit1
              then
                let uu____6318 =
                  let uu____6320 =
                    let uu____6321 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6321
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6320
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6318
                 then
                   let uu____6330 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6330 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6374 =
                           let uu____6377 =
                             let uu____6378 =
                               let uu____6385 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6385, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6378  in
                           [uu____6377]  in
                         FStar_Syntax_Subst.subst uu____6374 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6398 = close_wp_comp env [x] c  in
                    (uu____6398, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6401 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6429  ->
            match uu____6429 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6449 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6449 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6462 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6462
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6472 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6472
                       then
                         let uu____6477 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6477
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6484 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6484
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6493 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6493
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6500 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6500
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6516 =
                  let uu____6517 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6517
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6525 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6525, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6528 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6528 with
                     | (c1,g_c1) ->
                         let uu____6539 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6539 with
                          | (c2,g_c2) ->
                              let trivial_guard1 =
                                let uu____6551 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6554 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6554
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6551
                                 in
                              (debug1
                                 (fun uu____6580  ->
                                    let uu____6581 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6583 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6588 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6581 uu____6583 uu____6588);
                               (let aux uu____6606 =
                                  let uu____6607 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6607
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6638
                                        ->
                                        let uu____6639 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6639
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6671 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6671
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6718 =
                                  let aux_with_trivial_guard uu____6748 =
                                    let uu____6749 = aux ()  in
                                    match uu____6749 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard1, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6807 =
                                    let uu____6809 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6809  in
                                  if uu____6807
                                  then
                                    let uu____6825 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6825
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard1,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6852 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6852))
                                  else
                                    (let uu____6869 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6869
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___820_6900 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___820_6900.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___820_6900.FStar_Syntax_Syntax.index);
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
                                           let uu____6931 =
                                             let uu____6936 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6936
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6931 with
                                            | (c21,g_close) ->
                                                let uu____6957 =
                                                  let uu____6965 =
                                                    let uu____6966 =
                                                      let uu____6969 =
                                                        let uu____6972 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6972; g_close]
                                                         in
                                                      g_c1 :: uu____6969  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6966
                                                     in
                                                  (c21, uu____6965, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6957)
                                       | (uu____6985,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6997 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6997 with
                                            | (c21,g_close) ->
                                                let uu____7020 =
                                                  let uu____7028 =
                                                    let uu____7029 =
                                                      let uu____7032 =
                                                        let uu____7035 =
                                                          let uu____7036 =
                                                            let uu____7037 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____7037]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____7036
                                                            g_c2
                                                           in
                                                        [uu____7035; g_close]
                                                         in
                                                      g_c1 :: uu____7032  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____7029
                                                     in
                                                  (c21, uu____7028,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____7020)
                                       | (uu____7066,uu____7067) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____7082 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____7082
                                        then
                                          let uu____7097 =
                                            let uu____7105 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____7105, trivial_guard1,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____7097
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____7118 = try_simplify ()  in
                                match uu____7118 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug1
                                       (fun uu____7153  ->
                                          let uu____7154 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____7154);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____7170  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7201 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7201 with
                                        | (c,g_bind) ->
                                            let uu____7212 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7212)
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
                                        let uu____7239 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7239 with
                                        | (m,uu____7251,lift2) ->
                                            let uu____7253 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7253 with
                                             | (c23,g2) ->
                                                 let uu____7264 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7264 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7280 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7280
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7290 =
                                                          let uu____7295 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7296 =
                                                            let uu____7297 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7306 =
                                                              let uu____7317
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7317]
                                                               in
                                                            uu____7297 ::
                                                              uu____7306
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7295
                                                            uu____7296
                                                           in
                                                        uu____7290
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7350 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7350 with
                                                       | (c,g_s) ->
                                                           let uu____7365 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7365))))
                                         in
                                      let uu____7366 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7382 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7382, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7366 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7398 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7398
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7407 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7407
                                             then
                                               (debug1
                                                  (fun uu____7421  ->
                                                     let uu____7422 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7424 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7422 uu____7424);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7431 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7431
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7436 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7439 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7439)
                                                   in
                                                if uu____7436
                                                then
                                                  let e1' =
                                                    let uu____7464 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7464
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7476  ->
                                                        let uu____7477 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7479 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7477
                                                          uu____7479);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7494  ->
                                                        let uu____7495 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7497 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7495
                                                          uu____7497);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7504 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7504
                                                       in
                                                    let uu____7505 =
                                                      let uu____7510 =
                                                        let uu____7511 =
                                                          let uu____7512 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7512]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7511
                                                         in
                                                      weaken_comp uu____7510
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7505 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7538 =
                                                            let uu____7539 =
                                                              let uu____7540
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7540]
                                                               in
                                                            let uu____7559 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7539
                                                              uu____7559
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7538
                                                           in
                                                        let uu____7560 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7560
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7571 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7571))))))
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
      | uu____7588 -> g2
  
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
            (let uu____7612 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7612)
           in
        let flags =
          if should_return1
          then
            let uu____7620 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7620
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7638 =
          let uu____7639 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7639 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7652 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7652
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7660 =
                  let uu____7662 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7662  in
                (if uu____7660
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___945_7671 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___945_7671.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___945_7671.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___945_7671.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7672 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7672, g_c)
                 else
                   (let uu____7675 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7675, g_c)))
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
                   let uu____7686 =
                     let uu____7687 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7687
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7686
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7690 =
                   let uu____7695 =
                     let uu____7696 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7696
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7695  in
                 match uu____7690 with
                 | (bind_c,g_bind) ->
                     let uu____7705 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7706 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7705, uu____7706))
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
            fun uu____7742  ->
              match uu____7742 with
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
                    let uu____7754 =
                      ((let uu____7758 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7758) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7754
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7776 =
        let uu____7777 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7777  in
      FStar_Syntax_Syntax.fvar uu____7776 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7827 =
                    let uu____7832 =
                      let uu____7833 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7833 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7832 [u_a]
                     in
                  match uu____7827 with
                  | (uu____7844,conjunction) ->
                      let uu____7846 =
                        let uu____7855 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7870 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7855, uu____7870)  in
                      (match uu____7846 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7916 =
                               let uu____7918 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7918 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7916)
                              in
                           let uu____7922 =
                             let uu____7967 =
                               let uu____7968 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7968.FStar_Syntax_Syntax.n  in
                             match uu____7967 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____8017) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____8049 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____8049 with
                                  | (a_b::bs1,body1) ->
                                      let uu____8121 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____8121 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8269 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8269)))
                             | uu____8302 ->
                                 let uu____8303 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8303 r
                              in
                           (match uu____7922 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8428 =
                                  let uu____8435 =
                                    let uu____8436 =
                                      let uu____8437 =
                                        let uu____8444 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8444, a)  in
                                      FStar_Syntax_Syntax.NT uu____8437  in
                                    [uu____8436]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8435
                                    (fun b  ->
                                       let uu____8460 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8462 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8464 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8460 uu____8462 uu____8464) r
                                   in
                                (match uu____8428 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8502 =
                                                let uu____8509 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8509, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8502) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8548 =
                                           let uu____8549 =
                                             let uu____8552 =
                                               let uu____8553 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8553.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8552
                                              in
                                           uu____8549.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8548 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8564,uu____8565::is) ->
                                             let uu____8607 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8607
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8640 ->
                                             let uu____8641 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8641 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8657 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8657)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8662 =
                                           let uu____8663 =
                                             let uu____8666 =
                                               let uu____8667 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8667.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8666
                                              in
                                           uu____8663.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8662 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8678,uu____8679::is) ->
                                             let uu____8721 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8721
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8754 ->
                                             let uu____8755 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8755 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8771 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8771)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8776 =
                                         let uu____8777 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8777.FStar_Syntax_Syntax.n  in
                                       match uu____8776 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8782,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8837 ->
                                           let uu____8838 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8838 r
                                        in
                                     let uu____8847 =
                                       let uu____8848 =
                                         let uu____8849 =
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
                                             uu____8849;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8848
                                        in
                                     let uu____8872 =
                                       let uu____8873 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8873 g_guard
                                        in
                                     (uu____8847, uu____8872))))
  
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
                fun uu____8918  ->
                  let if_then_else1 =
                    let uu____8924 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8924 FStar_Util.must  in
                  let uu____8931 = destruct_wp_comp ct1  in
                  match uu____8931 with
                  | (uu____8942,uu____8943,wp_t) ->
                      let uu____8945 = destruct_wp_comp ct2  in
                      (match uu____8945 with
                       | (uu____8956,uu____8957,wp_e) ->
                           let wp =
                             let uu____8962 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8963 =
                               let uu____8968 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8969 =
                                 let uu____8970 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8979 =
                                   let uu____8990 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8999 =
                                     let uu____9010 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____9019 =
                                       let uu____9030 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____9030]  in
                                     uu____9010 :: uu____9019  in
                                   uu____8990 :: uu____8999  in
                                 uu____8970 :: uu____8979  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8968
                                 uu____8969
                                in
                             uu____8963 FStar_Pervasives_Native.None
                               uu____8962
                              in
                           let uu____9079 = mk_comp ed u_a a wp []  in
                           (uu____9079, FStar_TypeChecker_Env.trivial_guard))
  
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
            let uu____9133 =
              let uu____9134 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9134]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9133  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9181  ->
                   match uu____9181 with
                   | (uu____9195,eff_label,uu____9197,uu____9198) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9211 =
            let uu____9219 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9257  ->
                      match uu____9257 with
                      | (uu____9272,uu____9273,flags,uu____9275) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9292  ->
                                  match uu___5_9292 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9295 -> false))))
               in
            if uu____9219
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9211 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9332 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9334 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9334
                then
                  let uu____9341 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9341, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let default_case =
                     let post_k =
                       let uu____9348 =
                         let uu____9357 =
                           FStar_Syntax_Syntax.null_binder res_t  in
                         [uu____9357]  in
                       let uu____9376 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9348 uu____9376  in
                     let kwp =
                       let uu____9382 =
                         let uu____9391 =
                           FStar_Syntax_Syntax.null_binder post_k  in
                         [uu____9391]  in
                       let uu____9410 =
                         FStar_Syntax_Syntax.mk_Total
                           FStar_Syntax_Util.ktype0
                          in
                       FStar_Syntax_Util.arrow uu____9382 uu____9410  in
                     let post =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None post_k
                        in
                     let wp =
                       let uu____9417 =
                         let uu____9418 = FStar_Syntax_Syntax.mk_binder post
                            in
                         [uu____9418]  in
                       let uu____9437 =
                         let uu____9440 =
                           let uu____9447 =
                             FStar_TypeChecker_Env.get_range env  in
                           label FStar_TypeChecker_Err.exhaustiveness_check
                             uu____9447
                            in
                         let uu____9448 =
                           fvar_const env FStar_Parser_Const.false_lid  in
                         FStar_All.pipe_left uu____9440 uu____9448  in
                       FStar_Syntax_Util.abs uu____9417 uu____9437
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
                     let uu____9472 =
                       should_not_inline_whole_match ||
                         (let uu____9475 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9475)
                        in
                     if uu____9472 then cthen true else cthen false  in
                   let uu____9482 =
                     let uu____9493 =
                       FStar_All.pipe_right lcases
                         (FStar_List.map
                            (fun uu____9537  ->
                               match uu____9537 with
                               | (g,uu____9552,uu____9553,uu____9554) -> g))
                        in
                     FStar_All.pipe_right uu____9493
                       (FStar_List.fold_left
                          (fun uu____9598  ->
                             fun g  ->
                               match uu____9598 with
                               | (conds,acc) ->
                                   let cond =
                                     let uu____9639 =
                                       FStar_Syntax_Util.mk_neg g  in
                                     FStar_Syntax_Util.mk_conj acc uu____9639
                                      in
                                   ((FStar_List.append conds [cond]), cond))
                          ([], FStar_Syntax_Util.t_true))
                      in
                   match uu____9482 with
                   | (branch_conditions,uu____9667) ->
                       let uu____9680 =
                         FStar_List.fold_right2
                           (fun uu____9742  ->
                              fun bcond  ->
                                fun uu____9744  ->
                                  match (uu____9742, uu____9744) with
                                  | ((g,eff_label,uu____9804,cthen),(uu____9806,celse,g_comp))
                                      ->
                                      let uu____9853 =
                                        let uu____9858 =
                                          maybe_return eff_label cthen  in
                                        FStar_TypeChecker_Common.lcomp_comp
                                          uu____9858
                                         in
                                      (match uu____9853 with
                                       | (cthen1,gthen) ->
                                           let uu____9869 =
                                             let uu____9880 =
                                               lift_comps_sep_guards env
                                                 cthen1 celse
                                                 FStar_Pervasives_Native.None
                                                 false
                                                in
                                             match uu____9880 with
                                             | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                 ->
                                                 let md =
                                                   FStar_TypeChecker_Env.get_effect_decl
                                                     env m
                                                    in
                                                 let uu____9908 =
                                                   FStar_All.pipe_right
                                                     cthen2
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____9909 =
                                                   FStar_All.pipe_right
                                                     celse1
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 (md, uu____9908, uu____9909,
                                                   g_lift_then, g_lift_else)
                                              in
                                           (match uu____9869 with
                                            | (md,ct_then,ct_else,g_lift_then,g_lift_else)
                                                ->
                                                let fn =
                                                  let uu____9960 =
                                                    FStar_All.pipe_right md
                                                      FStar_Syntax_Util.is_layered
                                                     in
                                                  if uu____9960
                                                  then mk_layered_conjunction
                                                  else
                                                    mk_non_layered_conjunction
                                                   in
                                                let g_lift_then1 =
                                                  let uu____9995 =
                                                    FStar_Syntax_Util.mk_conj
                                                      bcond g
                                                     in
                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                    g_lift_then uu____9995
                                                   in
                                                let g_lift_else1 =
                                                  let uu____9997 =
                                                    let uu____9998 =
                                                      FStar_Syntax_Util.mk_neg
                                                        g
                                                       in
                                                    FStar_Syntax_Util.mk_conj
                                                      bcond uu____9998
                                                     in
                                                  FStar_TypeChecker_Common.weaken_guard_formula
                                                    g_lift_else uu____9997
                                                   in
                                                let g_lift =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g_lift_then1 g_lift_else1
                                                   in
                                                let uu____10002 =
                                                  let uu____10007 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env
                                                     in
                                                  fn env md u_res_t res_t g
                                                    ct_then ct_else
                                                    uu____10007
                                                   in
                                                (match uu____10002 with
                                                 | (c,g_conjunction) ->
                                                     let uu____10018 =
                                                       FStar_TypeChecker_Env.conj_guards
                                                         [g_comp;
                                                         gthen;
                                                         g_lift;
                                                         g_conjunction]
                                                        in
                                                     ((FStar_Pervasives_Native.Some
                                                         md), c, uu____10018)))))
                           lcases branch_conditions
                           (FStar_Pervasives_Native.None, default_case,
                             FStar_TypeChecker_Env.trivial_guard)
                          in
                       (match uu____9680 with
                        | (md,comp,g_comp) ->
                            let g_comp1 =
                              let uu____10035 =
                                let uu____10036 =
                                  FStar_All.pipe_right scrutinee
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                [uu____10036]  in
                              FStar_TypeChecker_Env.close_guard env0
                                uu____10035 g_comp
                               in
                            (match lcases with
                             | [] -> (comp, g_comp1)
                             | uu____10079::[] -> (comp, g_comp1)
                             | uu____10122 ->
                                 let uu____10139 =
                                   let uu____10141 =
                                     FStar_All.pipe_right md FStar_Util.must
                                      in
                                   FStar_All.pipe_right uu____10141
                                     FStar_Syntax_Util.is_layered
                                    in
                                 if uu____10139
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
                                    let uu____10154 = destruct_wp_comp comp1
                                       in
                                    match uu____10154 with
                                    | (uu____10165,uu____10166,wp) ->
                                        let ite_wp =
                                          let uu____10169 =
                                            FStar_All.pipe_right md1
                                              FStar_Syntax_Util.get_wp_ite_combinator
                                             in
                                          FStar_All.pipe_right uu____10169
                                            FStar_Util.must
                                           in
                                        let wp1 =
                                          let uu____10179 =
                                            let uu____10184 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [u_res_t] env md1 ite_wp
                                               in
                                            let uu____10185 =
                                              let uu____10186 =
                                                FStar_Syntax_Syntax.as_arg
                                                  res_t
                                                 in
                                              let uu____10195 =
                                                let uu____10206 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    wp
                                                   in
                                                [uu____10206]  in
                                              uu____10186 :: uu____10195  in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              uu____10184 uu____10185
                                             in
                                          uu____10179
                                            FStar_Pervasives_Native.None
                                            wp.FStar_Syntax_Syntax.pos
                                           in
                                        let uu____10239 =
                                          mk_comp md1 u_res_t res_t wp1
                                            bind_cases_flags
                                           in
                                        (uu____10239, g_comp1)))))
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
          let uu____10274 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____10274 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____10290 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____10296 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____10290 uu____10296
              else
                (let uu____10305 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____10311 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____10305 uu____10311)
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
          let uu____10336 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____10336
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____10339 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____10339
        then u_res
        else
          (let is_total =
             let uu____10346 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____10346
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____10357 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____10357 with
              | FStar_Pervasives_Native.None  ->
                  let uu____10360 =
                    let uu____10366 =
                      let uu____10368 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____10368
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____10366)
                     in
                  FStar_Errors.raise_error uu____10360
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
      let uu____10392 = destruct_wp_comp ct  in
      match uu____10392 with
      | (u_t,t,wp) ->
          let vc =
            let uu____10411 = FStar_TypeChecker_Env.get_range env  in
            let uu____10412 =
              let uu____10417 =
                let uu____10418 =
                  let uu____10419 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____10419 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____10418
                 in
              let uu____10426 =
                let uu____10427 = FStar_Syntax_Syntax.as_arg t  in
                let uu____10436 =
                  let uu____10447 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____10447]  in
                uu____10427 :: uu____10436  in
              FStar_Syntax_Syntax.mk_Tm_app uu____10417 uu____10426  in
            uu____10412 FStar_Pervasives_Native.None uu____10411  in
          let uu____10480 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____10480)
  
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
                  let uu____10535 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10535 with
                  | FStar_Pervasives_Native.Some uu____10550 ->
                      ((let uu____10568 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10568
                        then
                          let uu____10572 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10572
                        else ());
                       (let coercion =
                          let uu____10578 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10578
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10585 =
                            let uu____10586 =
                              let uu____10587 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10587
                               in
                            (FStar_Pervasives_Native.None, uu____10586)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10585
                           in
                        let e1 =
                          let uu____10593 =
                            let uu____10598 =
                              let uu____10599 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10599]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10598
                             in
                          uu____10593 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10633 =
                          let uu____10639 =
                            let uu____10641 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10641
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10639)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10633);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10660 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10678 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10689 -> false 
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
      let uu____10713 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10713 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10758 =
              let uu____10773 =
                let uu____10774 = FStar_Syntax_Subst.compress h1  in
                uu____10774.FStar_Syntax_Syntax.n  in
              (uu____10773, args)  in
            match uu____10758 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10821,uu____10822) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10855) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10876,branches),uu____10878) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10942 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10943 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10943 with
                               | (uu____10944,uu____10945,br_body) ->
                                   let uu____10963 =
                                     let uu____10964 =
                                       let uu____10969 =
                                         let uu____10970 =
                                           let uu____10973 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10973
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10970
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10969  in
                                     FStar_All.pipe_right br_body uu____10964
                                      in
                                   (match uu____10963 with
                                    | No  -> No
                                    | uu____10984 -> Maybe))) No)
            | uu____10985 -> No  in
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
            (((let uu____11037 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11037) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11056 =
                 let uu____11057 = FStar_Syntax_Subst.compress t1  in
                 uu____11057.FStar_Syntax_Syntax.n  in
               match uu____11056 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____11062 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11072 =
                 let uu____11073 = FStar_Syntax_Subst.compress t1  in
                 uu____11073.FStar_Syntax_Syntax.n  in
               match uu____11072 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____11078 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____11089 =
                 let uu____11090 = FStar_Syntax_Subst.compress t2  in
                 uu____11090.FStar_Syntax_Syntax.n  in
               match uu____11089 with
               | FStar_Syntax_Syntax.Tm_type uu____11094 -> true
               | uu____11096 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____11099 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____11099 with
             | (head1,args) ->
                 ((let uu____11149 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____11149
                   then
                     let uu____11153 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____11155 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____11157 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____11159 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____11153 uu____11155 uu____11157 uu____11159
                   else ());
                  (let mk_erased u t =
                     let uu____11177 =
                       let uu____11180 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____11180 [u]  in
                     let uu____11181 =
                       let uu____11192 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____11192]  in
                     FStar_Syntax_Util.mk_app uu____11177 uu____11181  in
                   let uu____11217 =
                     let uu____11232 =
                       let uu____11233 = FStar_Syntax_Util.un_uinst head1  in
                       uu____11233.FStar_Syntax_Syntax.n  in
                     (uu____11232, args)  in
                   match uu____11217 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____11271 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____11271 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____11311 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11311 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11351 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11351 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____11391 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____11391 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____11412 ->
                       let uu____11427 =
                         let uu____11432 = check_erased env res_typ  in
                         let uu____11433 = check_erased env exp_t  in
                         (uu____11432, uu____11433)  in
                       (match uu____11427 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11442 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____11442 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____11453 =
                                   let uu____11458 =
                                     let uu____11459 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____11459]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____11458
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____11453 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____11494 =
                              let uu____11499 =
                                let uu____11500 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____11500]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____11499
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____11494 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11533 ->
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
        let uu____11568 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11568 with
        | (hd1,args) ->
            let uu____11617 =
              let uu____11632 =
                let uu____11633 = FStar_Syntax_Subst.compress hd1  in
                uu____11633.FStar_Syntax_Syntax.n  in
              (uu____11632, args)  in
            (match uu____11617 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11671 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11698  -> FStar_Pervasives_Native.Some _11698)
                   uu____11671
             | uu____11699 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11752 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11752
           then
             let uu____11755 = FStar_Syntax_Print.term_to_string e  in
             let uu____11757 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11759 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11755 uu____11757 uu____11759
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____11769 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11769 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11794 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11820 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11820, false)
             else
               (let uu____11830 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11830, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11843) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11855 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11855
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1388_11871 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1388_11871.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1388_11871.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1388_11871.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11878 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11878 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11894 =
                      let uu____11895 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11895 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11915 =
                            let uu____11917 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11917 = FStar_Syntax_Util.Equal  in
                          if uu____11915
                          then
                            ((let uu____11924 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11924
                              then
                                let uu____11928 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11930 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11928 uu____11930
                              else ());
                             (let uu____11935 = set_result_typ1 c  in
                              (uu____11935, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11942 ->
                                   true
                               | uu____11950 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11959 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11959
                                  in
                               let lc1 =
                                 let uu____11961 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11962 =
                                   let uu____11963 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11963)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11961 uu____11962
                                  in
                               ((let uu____11967 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11967
                                 then
                                   let uu____11971 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11973 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11975 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11977 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11971 uu____11973 uu____11975
                                     uu____11977
                                 else ());
                                (let uu____11982 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11982 with
                                 | (c1,g_lc) ->
                                     let uu____11993 = set_result_typ1 c1  in
                                     let uu____11994 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11993, uu____11994)))
                             else
                               ((let uu____11998 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11998
                                 then
                                   let uu____12002 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12004 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12002 uu____12004
                                 else ());
                                (let uu____12009 = set_result_typ1 c  in
                                 (uu____12009, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1425_12013 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1425_12013.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1425_12013.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1425_12013.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12023 =
                      let uu____12024 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12024
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12034 =
                           let uu____12035 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12035.FStar_Syntax_Syntax.n  in
                         match uu____12034 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12042,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12044;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12045;_},uu____12046)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1441_12072 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1441_12072.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1441_12072.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1441_12072.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____12073 ->
                             let uu____12074 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____12074 with
                              | (c,g_c) ->
                                  ((let uu____12086 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____12086
                                    then
                                      let uu____12090 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____12092 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____12094 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____12096 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____12090 uu____12092 uu____12094
                                        uu____12096
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
                                        let uu____12109 =
                                          let uu____12114 =
                                            let uu____12115 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____12115]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____12114
                                           in
                                        uu____12109
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____12142 =
                                      let uu____12147 =
                                        FStar_All.pipe_left
                                          (fun _12168  ->
                                             FStar_Pervasives_Native.Some
                                               _12168)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____12169 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____12170 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____12171 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____12147
                                        uu____12169 e uu____12170 uu____12171
                                       in
                                    match uu____12142 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1459_12179 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1459_12179.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1459_12179.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____12181 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____12181
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____12184 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____12184 with
                                         | (c2,g_lc) ->
                                             ((let uu____12196 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____12196
                                               then
                                                 let uu____12200 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____12200
                                               else ());
                                              (let uu____12205 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____12205))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_12214  ->
                              match uu___6_12214 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____12217 -> []))
                       in
                    let lc1 =
                      let uu____12219 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____12219 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1475_12221 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1475_12221.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1475_12221.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1475_12221.FStar_TypeChecker_Common.implicits)
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
        let uu____12257 =
          let uu____12260 =
            let uu____12265 =
              let uu____12266 =
                let uu____12275 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____12275  in
              [uu____12266]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____12265  in
          uu____12260 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____12257  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____12298 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____12298
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____12317 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____12333 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____12350 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____12350
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____12366)::(ens,uu____12368)::uu____12369 ->
                    let uu____12412 =
                      let uu____12415 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____12415  in
                    let uu____12416 =
                      let uu____12417 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____12417  in
                    (uu____12412, uu____12416)
                | uu____12420 ->
                    let uu____12431 =
                      let uu____12437 =
                        let uu____12439 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____12439
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____12437)
                       in
                    FStar_Errors.raise_error uu____12431
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____12459)::uu____12460 ->
                    let uu____12487 =
                      let uu____12492 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____12492
                       in
                    (match uu____12487 with
                     | (us_r,uu____12524) ->
                         let uu____12525 =
                           let uu____12530 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12530
                            in
                         (match uu____12525 with
                          | (us_e,uu____12562) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12565 =
                                  let uu____12566 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12566
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12565
                                  us_r
                                 in
                              let as_ens =
                                let uu____12568 =
                                  let uu____12569 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12569
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12568
                                  us_e
                                 in
                              let req =
                                let uu____12573 =
                                  let uu____12578 =
                                    let uu____12579 =
                                      let uu____12590 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12590]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12579
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12578
                                   in
                                uu____12573 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12630 =
                                  let uu____12635 =
                                    let uu____12636 =
                                      let uu____12647 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12647]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12636
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12635
                                   in
                                uu____12630 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12684 =
                                let uu____12687 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12687  in
                              let uu____12688 =
                                let uu____12689 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12689  in
                              (uu____12684, uu____12688)))
                | uu____12692 -> failwith "Impossible"))
  
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
        (let uu____12731 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12731
         then
           let uu____12736 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12738 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12736
             uu____12738
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
          (let uu____12797 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12797
           then
             let uu____12802 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12804 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12802
               uu____12804
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12815 =
      let uu____12817 =
        let uu____12818 = FStar_Syntax_Subst.compress t  in
        uu____12818.FStar_Syntax_Syntax.n  in
      match uu____12817 with
      | FStar_Syntax_Syntax.Tm_app uu____12822 -> false
      | uu____12840 -> true  in
    if uu____12815
    then t
    else
      (let uu____12845 = FStar_Syntax_Util.head_and_args t  in
       match uu____12845 with
       | (head1,args) ->
           let uu____12888 =
             let uu____12890 =
               let uu____12891 = FStar_Syntax_Subst.compress head1  in
               uu____12891.FStar_Syntax_Syntax.n  in
             match uu____12890 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12896 -> false  in
           if uu____12888
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12928 ->
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
          ((let uu____12975 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12975
            then
              let uu____12978 = FStar_Syntax_Print.term_to_string e  in
              let uu____12980 = FStar_Syntax_Print.term_to_string t  in
              let uu____12982 =
                let uu____12984 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12984
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12978 uu____12980 uu____12982
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____12997 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____12997 with
              | (formals,uu____13013) ->
                  let n_implicits =
                    let uu____13035 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____13113  ->
                              match uu____13113 with
                              | (uu____13121,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____13128 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____13128 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____13035 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____13253 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____13253 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____13267 =
                      let uu____13273 =
                        let uu____13275 = FStar_Util.string_of_int n_expected
                           in
                        let uu____13277 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____13279 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____13275 uu____13277 uu____13279
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____13273)
                       in
                    let uu____13283 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____13267 uu____13283
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_13301 =
              match uu___7_13301 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____13344 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____13344 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _13475,uu____13462)
                           when _13475 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____13508,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____13510))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13544 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13544 with
                            | (v1,uu____13585,g) ->
                                ((let uu____13600 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13600
                                  then
                                    let uu____13603 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13603
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13613 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13613 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13706 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13706))))
                       | (uu____13733,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13770 =
                             let uu____13783 =
                               let uu____13790 =
                                 let uu____13795 = FStar_Dyn.mkdyn env  in
                                 (uu____13795, tau)  in
                               FStar_Pervasives_Native.Some uu____13790  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13783
                              in
                           (match uu____13770 with
                            | (v1,uu____13828,g) ->
                                ((let uu____13843 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13843
                                  then
                                    let uu____13846 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13846
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13856 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13856 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13949 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13949))))
                       | (uu____13976,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14024 =
                       let uu____14051 = inst_n_binders t1  in
                       aux [] uu____14051 bs1  in
                     (match uu____14024 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____14123) -> (e, torig, guard)
                           | (uu____14154,[]) when
                               let uu____14185 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____14185 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____14187 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____14215 ->
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
            | uu____14228 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____14240 =
      let uu____14244 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____14244
        (FStar_List.map
           (fun u  ->
              let uu____14256 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____14256 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____14240 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____14284 = FStar_Util.set_is_empty x  in
      if uu____14284
      then []
      else
        (let s =
           let uu____14302 =
             let uu____14305 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____14305  in
           FStar_All.pipe_right uu____14302 FStar_Util.set_elements  in
         (let uu____14321 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____14321
          then
            let uu____14326 =
              let uu____14328 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____14328  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____14326
          else ());
         (let r =
            let uu____14337 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____14337  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____14376 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____14376
                     then
                       let uu____14381 =
                         let uu____14383 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____14383
                          in
                       let uu____14387 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____14389 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____14381 uu____14387 uu____14389
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
        let uu____14419 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____14419 FStar_Util.set_elements  in
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
        | ([],uu____14458) -> generalized_univ_names
        | (uu____14465,[]) -> explicit_univ_names
        | uu____14472 ->
            let uu____14481 =
              let uu____14487 =
                let uu____14489 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____14489
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____14487)
               in
            FStar_Errors.raise_error uu____14481 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____14511 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____14511
       then
         let uu____14516 = FStar_Syntax_Print.term_to_string t  in
         let uu____14518 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____14516 uu____14518
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____14527 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____14527
        then
          let uu____14532 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14532
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14541 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14541
         then
           let uu____14546 = FStar_Syntax_Print.term_to_string t  in
           let uu____14548 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14546 uu____14548
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
        let uu____14632 =
          let uu____14634 =
            FStar_Util.for_all
              (fun uu____14648  ->
                 match uu____14648 with
                 | (uu____14658,uu____14659,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14634  in
        if uu____14632
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14711 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14711
              then
                let uu____14714 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14714
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14721 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14721
               then
                 let uu____14724 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14724
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14742 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14742 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14776 =
             match uu____14776 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14813 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14813
                   then
                     let uu____14818 =
                       let uu____14820 =
                         let uu____14824 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14824
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14820
                         (FStar_String.concat ", ")
                        in
                     let uu____14872 =
                       let uu____14874 =
                         let uu____14878 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14878
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14891 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14893 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14891
                                   uu____14893))
                          in
                       FStar_All.pipe_right uu____14874
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14818
                       uu____14872
                   else ());
                  (let univs2 =
                     let uu____14907 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14919 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14919) univs1
                       uu____14907
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14926 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14926
                    then
                      let uu____14931 =
                        let uu____14933 =
                          let uu____14937 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____14937
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14933
                          (FStar_String.concat ", ")
                         in
                      let uu____14985 =
                        let uu____14987 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15001 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15003 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15001
                                    uu____15003))
                           in
                        FStar_All.pipe_right uu____14987
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14931 uu____14985
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____15024 =
             let uu____15041 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15041  in
           match uu____15024 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____15131 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____15131
                 then ()
                 else
                   (let uu____15136 = lec_hd  in
                    match uu____15136 with
                    | (lb1,uu____15144,uu____15145) ->
                        let uu____15146 = lec2  in
                        (match uu____15146 with
                         | (lb2,uu____15154,uu____15155) ->
                             let msg =
                               let uu____15158 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15160 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____15158 uu____15160
                                in
                             let uu____15163 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____15163))
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
                 let uu____15231 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____15231
                 then ()
                 else
                   (let uu____15236 = lec_hd  in
                    match uu____15236 with
                    | (lb1,uu____15244,uu____15245) ->
                        let uu____15246 = lec2  in
                        (match uu____15246 with
                         | (lb2,uu____15254,uu____15255) ->
                             let msg =
                               let uu____15258 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____15260 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____15258 uu____15260
                                in
                             let uu____15263 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____15263))
                  in
               let lecs1 =
                 let uu____15274 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____15327 = univs_and_uvars_of_lec this_lec  in
                        match uu____15327 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____15274 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____15432 = lec_hd  in
                   match uu____15432 with
                   | (lbname,e,c) ->
                       let uu____15442 =
                         let uu____15448 =
                           let uu____15450 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____15452 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____15454 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____15450 uu____15452 uu____15454
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____15448)
                          in
                       let uu____15458 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____15442 uu____15458
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____15477 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____15477 with
                         | FStar_Pervasives_Native.Some uu____15486 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____15494 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____15498 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____15498 with
                              | (bs,kres) ->
                                  ((let uu____15542 =
                                      let uu____15543 =
                                        let uu____15546 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15546
                                         in
                                      uu____15543.FStar_Syntax_Syntax.n  in
                                    match uu____15542 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15547
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15551 =
                                          let uu____15553 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15553  in
                                        if uu____15551
                                        then fail1 kres
                                        else ()
                                    | uu____15558 -> fail1 kres);
                                   (let a =
                                      let uu____15560 =
                                        let uu____15563 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15566  ->
                                             FStar_Pervasives_Native.Some
                                               _15566) uu____15563
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15560
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15574 ->
                                          let uu____15583 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15583
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
                      (fun uu____15686  ->
                         match uu____15686 with
                         | (lbname,e,c) ->
                             let uu____15732 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15793 ->
                                   let uu____15806 = (e, c)  in
                                   (match uu____15806 with
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
                                                (fun uu____15846  ->
                                                   match uu____15846 with
                                                   | (x,uu____15852) ->
                                                       let uu____15853 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15853)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15871 =
                                                let uu____15873 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15873
                                                 in
                                              if uu____15871
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
                                          let uu____15882 =
                                            let uu____15883 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15883.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15882 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15908 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15908 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15919 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15923 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15923, gen_tvars))
                                in
                             (match uu____15732 with
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
        (let uu____16070 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16070
         then
           let uu____16073 =
             let uu____16075 =
               FStar_List.map
                 (fun uu____16090  ->
                    match uu____16090 with
                    | (lb,uu____16099,uu____16100) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____16075 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____16073
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____16126  ->
                match uu____16126 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____16155 = gen env is_rec lecs  in
           match uu____16155 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____16254  ->
                       match uu____16254 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____16316 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____16316
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____16364  ->
                           match uu____16364 with
                           | (l,us,e,c,gvs) ->
                               let uu____16398 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____16400 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____16402 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____16404 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16406 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____16398 uu____16400 uu____16402
                                 uu____16404 uu____16406))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____16451  ->
                match uu____16451 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____16495 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____16495, t, c, gvs)) univnames_lecs
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
        let uu____16550 =
          let uu____16554 =
            let uu____16556 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16556  in
          FStar_Pervasives_Native.Some uu____16554  in
        FStar_Profiling.profile
          (fun uu____16573  -> generalize' env is_rec lecs) uu____16550
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
              let uu____16630 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____16630 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____16636 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____16636
                    (fun _16639  -> FStar_Pervasives_Native.Some _16639)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____16648 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____16648 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____16654 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun _16657  -> FStar_Pervasives_Native.Some _16657)
                       uu____16654)
             in
          let uu____16658 = maybe_coerce_lc env1 e lc t2  in
          match uu____16658 with
          | (e1,lc1,g_c) ->
              let uu____16674 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16674 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16683 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16689 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16683 uu____16689
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16698 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16698
                     then
                       let uu____16703 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16703
                     else ());
                    (let uu____16709 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____16709))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16737 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16737
         then
           let uu____16740 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16740
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16754 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16754 with
         | (c,g_c) ->
             let uu____16766 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16766
             then
               let uu____16774 =
                 let uu____16776 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16776  in
               (uu____16774, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16784 =
                    let uu____16785 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16785
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16784
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16786 = check_trivial_precondition env c1  in
                match uu____16786 with
                | (ct,vc,g_pre) ->
                    ((let uu____16802 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16802
                      then
                        let uu____16807 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16807
                      else ());
                     (let uu____16812 =
                        let uu____16814 =
                          let uu____16815 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16815  in
                        discharge uu____16814  in
                      let uu____16816 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16812, uu____16816)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16850 =
        match uu___8_16850 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16860)::[] -> f fst1
        | uu____16885 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16897 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16897
          (fun _16898  -> FStar_TypeChecker_Common.NonTrivial _16898)
         in
      let op_or_e e =
        let uu____16909 =
          let uu____16910 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16910  in
        FStar_All.pipe_right uu____16909
          (fun _16913  -> FStar_TypeChecker_Common.NonTrivial _16913)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16920  -> FStar_TypeChecker_Common.NonTrivial _16920)
         in
      let op_or_t t =
        let uu____16931 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16931
          (fun _16934  -> FStar_TypeChecker_Common.NonTrivial _16934)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16941  -> FStar_TypeChecker_Common.NonTrivial _16941)
         in
      let short_op_ite uu___9_16947 =
        match uu___9_16947 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16957)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16984)::[] ->
            let uu____17025 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17025
              (fun _17026  -> FStar_TypeChecker_Common.NonTrivial _17026)
        | uu____17027 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17039 =
          let uu____17047 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17047)  in
        let uu____17055 =
          let uu____17065 =
            let uu____17073 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____17073)  in
          let uu____17081 =
            let uu____17091 =
              let uu____17099 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____17099)  in
            let uu____17107 =
              let uu____17117 =
                let uu____17125 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____17125)  in
              let uu____17133 =
                let uu____17143 =
                  let uu____17151 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____17151)  in
                [uu____17143; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____17117 :: uu____17133  in
            uu____17091 :: uu____17107  in
          uu____17065 :: uu____17081  in
        uu____17039 :: uu____17055  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____17213 =
            FStar_Util.find_map table
              (fun uu____17228  ->
                 match uu____17228 with
                 | (x,mk1) ->
                     let uu____17245 = FStar_Ident.lid_equals x lid  in
                     if uu____17245
                     then
                       let uu____17250 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____17250
                     else FStar_Pervasives_Native.None)
             in
          (match uu____17213 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____17254 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____17262 =
      let uu____17263 = FStar_Syntax_Util.un_uinst l  in
      uu____17263.FStar_Syntax_Syntax.n  in
    match uu____17262 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____17268 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____17304)::uu____17305 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____17324 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____17333,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____17334))::uu____17335 -> bs
      | uu____17353 ->
          let uu____17354 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____17354 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____17358 =
                 let uu____17359 = FStar_Syntax_Subst.compress t  in
                 uu____17359.FStar_Syntax_Syntax.n  in
               (match uu____17358 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____17363) ->
                    let uu____17384 =
                      FStar_Util.prefix_until
                        (fun uu___10_17424  ->
                           match uu___10_17424 with
                           | (uu____17432,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____17433)) ->
                               false
                           | uu____17438 -> true) bs'
                       in
                    (match uu____17384 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____17474,uu____17475) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17547,uu____17548) ->
                         let uu____17621 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17641  ->
                                   match uu____17641 with
                                   | (x,uu____17650) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17621
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17699  ->
                                     match uu____17699 with
                                     | (x,i) ->
                                         let uu____17718 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17718, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17729 -> bs))
  
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
            let uu____17758 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17758
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
          let uu____17789 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17789
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
        (let uu____17832 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17832
         then
           ((let uu____17837 = FStar_Ident.text_of_lid lident  in
             d uu____17837);
            (let uu____17839 = FStar_Ident.text_of_lid lident  in
             let uu____17841 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17839 uu____17841))
         else ());
        (let fv =
           let uu____17847 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17847
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
         let uu____17859 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2088_17861 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2088_17861.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2088_17861.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2088_17861.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2088_17861.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2088_17861.FStar_Syntax_Syntax.sigopts)
           }), uu____17859))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17879 =
        match uu___11_17879 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17882 -> false  in
      let reducibility uu___12_17890 =
        match uu___12_17890 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17897 -> false  in
      let assumption uu___13_17905 =
        match uu___13_17905 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17909 -> false  in
      let reification uu___14_17917 =
        match uu___14_17917 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17920 -> true
        | uu____17922 -> false  in
      let inferred uu___15_17930 =
        match uu___15_17930 with
        | FStar_Syntax_Syntax.Discriminator uu____17932 -> true
        | FStar_Syntax_Syntax.Projector uu____17934 -> true
        | FStar_Syntax_Syntax.RecordType uu____17940 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17950 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17963 -> false  in
      let has_eq uu___16_17971 =
        match uu___16_17971 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17975 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18054 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18061 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____18094 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____18094))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____18125 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____18125
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
           | FStar_Syntax_Syntax.Sig_bundle uu____18145 ->
               let uu____18154 =
                 let uu____18156 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_18162  ->
                           match uu___17_18162 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____18165 -> false))
                    in
                 Prims.op_Negation uu____18156  in
               if uu____18154
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____18172 -> ()
           | uu____18179 ->
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
      let uu____18193 =
        let uu____18195 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_18201  ->
                  match uu___18_18201 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____18204 -> false))
           in
        FStar_All.pipe_right uu____18195 Prims.op_Negation  in
      if uu____18193
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____18225 =
            let uu____18231 =
              let uu____18233 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____18233 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____18231)  in
          FStar_Errors.raise_error uu____18225 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____18251 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____18259 =
            let uu____18261 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____18261  in
          if uu____18259 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____18272),uu____18273) ->
              ((let uu____18285 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____18285
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____18294 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____18294
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____18305 ->
              ((let uu____18315 =
                  let uu____18317 =
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
                  Prims.op_Negation uu____18317  in
                if uu____18315 then err'1 () else ());
               (let uu____18327 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_18333  ->
                           match uu___19_18333 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____18336 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____18327
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____18342 ->
              let uu____18349 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____18349 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____18357 ->
              let uu____18364 =
                let uu____18366 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____18366  in
              if uu____18364 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____18376 ->
              let uu____18377 =
                let uu____18379 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____18379  in
              if uu____18377 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18389 ->
              let uu____18402 =
                let uu____18404 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____18404  in
              if uu____18402 then err'1 () else ()
          | uu____18414 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____18453 =
          let uu____18454 = FStar_Syntax_Subst.compress t1  in
          uu____18454.FStar_Syntax_Syntax.n  in
        match uu____18453 with
        | FStar_Syntax_Syntax.Tm_arrow uu____18458 ->
            let uu____18473 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____18473 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____18506;
               FStar_Syntax_Syntax.index = uu____18507;
               FStar_Syntax_Syntax.sort = t2;_},uu____18509)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____18518) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18544) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18550 -> false
      
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
        (let uu____18560 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18560
         then
           let uu____18565 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18565
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
                  let uu____18630 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18630 r  in
                let uu____18640 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18640 with
                | (uu____18649,signature) ->
                    let uu____18651 =
                      let uu____18652 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18652.FStar_Syntax_Syntax.n  in
                    (match uu____18651 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18660) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18708 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18723 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18725 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18723 eff_name.FStar_Ident.str
                                       uu____18725) r
                                 in
                              (match uu____18708 with
                               | (is,g) ->
                                   let uu____18738 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18740 =
                                             let uu____18741 =
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
                                                 = uu____18741;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18740
                                            in
                                         let uu____18760 =
                                           let uu____18767 =
                                             let uu____18768 =
                                               let uu____18783 =
                                                 let uu____18792 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18792]  in
                                               (uu____18783, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18768
                                              in
                                           FStar_Syntax_Syntax.mk uu____18767
                                            in
                                         uu____18760
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18823 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18823
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18832 =
                                           let uu____18837 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18837
                                            in
                                         uu____18832
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18738, g))
                          | uu____18846 -> fail1 signature)
                     | uu____18847 -> fail1 signature)
  
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
            let uu____18878 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18878
              (fun ed  ->
                 let uu____18886 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18886 u a_tm)
  
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
              let uu____18922 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18922 with
              | (uu____18927,sig_tm) ->
                  let fail1 t =
                    let uu____18935 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18935 r  in
                  let uu____18941 =
                    let uu____18942 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18942.FStar_Syntax_Syntax.n  in
                  (match uu____18941 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18946) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18969)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18991 -> fail1 sig_tm)
                   | uu____18992 -> fail1 sig_tm)
  
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
          (let uu____19023 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19023
           then
             let uu____19028 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19030 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19028 uu____19030
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19037 =
             let uu____19048 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19049 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19048, (ct.FStar_Syntax_Syntax.result_typ), uu____19049)
              in
           match uu____19037 with
           | (u,a,c_is) ->
               let uu____19097 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____19097 with
                | (uu____19106,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____19117 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____19119 = FStar_Ident.string_of_lid tgt  in
                      let uu____19121 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____19117 uu____19119 s uu____19121
                       in
                    let uu____19124 =
                      let uu____19157 =
                        let uu____19158 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____19158.FStar_Syntax_Syntax.n  in
                      match uu____19157 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____19222 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____19222 with
                           | (a_b::bs1,c2) ->
                               let uu____19282 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____19282, c2))
                      | uu____19370 ->
                          let uu____19371 =
                            let uu____19377 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____19377)
                             in
                          FStar_Errors.raise_error uu____19371 r
                       in
                    (match uu____19124 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____19495 =
                           let uu____19502 =
                             let uu____19503 =
                               let uu____19504 =
                                 let uu____19511 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____19511, a)  in
                               FStar_Syntax_Syntax.NT uu____19504  in
                             [uu____19503]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____19502
                             (fun b  ->
                                let uu____19528 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19530 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19532 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19534 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19528 uu____19530 uu____19532
                                  uu____19534) r
                            in
                         (match uu____19495 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19548 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19548
                                then
                                  let uu____19553 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19562 =
                                             let uu____19564 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19564
                                              in
                                           Prims.op_Hat s uu____19562) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19553
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19595 =
                                           let uu____19602 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19602, t)  in
                                         FStar_Syntax_Syntax.NT uu____19595)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19621 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19621
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19627 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19627
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19636 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19636)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____19638 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____19638
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____19642 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19642 r
                                   in
                                let fml =
                                  let uu____19647 =
                                    let uu____19652 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____19653 =
                                      let uu____19654 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____19654
                                       in
                                    (uu____19652, uu____19653)  in
                                  match uu____19647 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____19680 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____19680
                                 then
                                   let uu____19686 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____19686
                                 else ());
                                (let c1 =
                                   let uu____19692 =
                                     let uu____19693 =
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
                                         uu____19693;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____19692
                                    in
                                 (let uu____19717 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____19717
                                  then
                                    let uu____19722 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____19722
                                  else ());
                                 (let uu____19727 =
                                    let uu____19728 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____19729 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____19728 uu____19729
                                     in
                                  (c1, uu____19727)))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19743 .
    'Auu____19743 ->
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
              let uu____19772 =
                let uu____19777 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19777
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19772 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19820 =
                let uu____19821 =
                  let uu____19824 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19824
                    FStar_Syntax_Subst.compress
                   in
                uu____19821.FStar_Syntax_Syntax.n  in
              match uu____19820 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19847::bs,uu____19849)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19889 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19889
                    FStar_Pervasives_Native.fst
              | uu____19995 ->
                  let uu____19996 =
                    let uu____20002 =
                      let uu____20004 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20004
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20002)  in
                  FStar_Errors.raise_error uu____19996
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20031 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20040 =
                let uu____20051 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____20087  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____20094 =
                  let uu____20105 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____20105]  in
                FStar_List.append uu____20051 uu____20094  in
              uu____20031 :: uu____20040  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____20176 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____20176 with
        | (uu____20181,t) ->
            let err n1 =
              let uu____20191 =
                let uu____20197 =
                  let uu____20199 = FStar_Ident.string_of_lid datacon  in
                  let uu____20201 = FStar_Util.string_of_int n1  in
                  let uu____20203 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____20199 uu____20201 uu____20203
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____20197)
                 in
              let uu____20207 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____20191 uu____20207  in
            let uu____20208 =
              let uu____20209 = FStar_Syntax_Subst.compress t  in
              uu____20209.FStar_Syntax_Syntax.n  in
            (match uu____20208 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____20213) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____20268  ->
                           match uu____20268 with
                           | (uu____20276,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____20285 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____20317 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____20317
                      FStar_Pervasives_Native.fst)
             | uu____20328 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____20341 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____20341
      then
        let uu____20344 =
          let uu____20357 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____20357
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____20344;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____20392 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____20392 with
           | (uu____20401,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____20420 =
                 let uu____20421 =
                   let uu___2462_20422 = ct  in
                   let uu____20423 =
                     let uu____20434 =
                       let uu____20443 =
                         let uu____20444 =
                           let uu____20451 =
                             let uu____20452 =
                               let uu____20469 =
                                 let uu____20480 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____20480; wp]  in
                               (lift_t, uu____20469)  in
                             FStar_Syntax_Syntax.Tm_app uu____20452  in
                           FStar_Syntax_Syntax.mk uu____20451  in
                         uu____20444 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____20443
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____20434]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2462_20422.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2462_20422.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____20423;
                     FStar_Syntax_Syntax.flags =
                       (uu___2462_20422.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____20421  in
               (uu____20420, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20580 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20580 with
           | (uu____20587,lift_t) ->
               let uu____20589 =
                 let uu____20596 =
                   let uu____20597 =
                     let uu____20614 =
                       let uu____20625 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20634 =
                         let uu____20645 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20654 =
                           let uu____20665 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20665]  in
                         uu____20645 :: uu____20654  in
                       uu____20625 :: uu____20634  in
                     (lift_t, uu____20614)  in
                   FStar_Syntax_Syntax.Tm_app uu____20597  in
                 FStar_Syntax_Syntax.mk uu____20596  in
               uu____20589 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20718 =
           let uu____20731 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20731 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20718;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20767  ->
                        fun uu____20768  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20791 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20791
  
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
  