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
            let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
            let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
            let uu____2226 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2226 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2252 = lift_comp env c11 lift1  in
                (match uu____2252 with
                 | (c12,g1) ->
                     let uu____2267 =
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
                          let uu____2306 = lift_comp env_x c21 lift2  in
                          match uu____2306 with
                          | (c22,g2) ->
                              let uu____2317 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2317))
                        in
                     (match uu____2267 with
                      | (c22,g2) ->
                          let uu____2340 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (m, c12, c22, uu____2340)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2361 =
                  let uu____2362 =
                    let uu____2368 =
                      let uu____2370 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2372 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2370
                        uu____2372
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2368)
                     in
                  FStar_Errors.raise_error uu____2362 rng  in
                ((let uu____2385 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2385
                  then
                    let uu____2390 =
                      let uu____2392 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2392
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2394 =
                      let uu____2396 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2396
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2398 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2390 uu____2394 uu____2398
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
                      let uu____2452 =
                        let uu____2457 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2458 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2459 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2460 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2457 uu____2458 uu____2459
                          ct.FStar_Syntax_Syntax.result_typ uu____2460 rng
                         in
                      match uu____2452 with
                      | (c_ret,g_ret) ->
                          let uu____2467 =
                            let uu____2472 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2472 [] rng
                             in
                          (match uu____2467 with
                           | (c,g_bind) ->
                               let uu____2479 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2479))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2524 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2524
                      then
                        let uu____2560 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2560 with
                        | (p,f_bind) ->
                            let uu____2627 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2627
                             then
                               let uu____2640 = bind_with_return c12 p f_bind
                                  in
                               match uu____2640 with
                               | (c13,g) ->
                                   let uu____2657 =
                                     let uu____2666 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2666, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2657
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2695 =
                      let uu____2704 = try_lift c11 c21  in
                      match uu____2704 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2743 = try_lift c21 c11  in
                          (match uu____2743 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2695 with
                    | (p,c12,c22,g) ->
                        ((let uu____2795 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2795
                          then
                            let uu____2800 = FStar_Ident.string_of_lid p  in
                            let uu____2802 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2804 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2800 uu____2802 uu____2804
                          else ());
                         (p, c12, c22, g))))
  
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
          let uu____2864 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2864
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2876 =
      let uu____2877 = FStar_Syntax_Subst.compress t  in
      uu____2877.FStar_Syntax_Syntax.n  in
    match uu____2876 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2881 -> true
    | uu____2897 -> false
  
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
              let uu____2967 =
                let uu____2969 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2969  in
              if uu____2967
              then f
              else (let uu____2976 = reason1 ()  in label uu____2976 r f)
  
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
            let uu___384_2997 = g  in
            let uu____2998 =
              let uu____2999 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2999  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2998;
              FStar_TypeChecker_Common.deferred =
                (uu___384_2997.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___384_2997.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___384_2997.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3020 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3020
        then c
        else
          (let uu____3025 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3025
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____3067 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3067 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3095 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3095]  in
                       let us =
                         let uu____3117 =
                           let uu____3120 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3120]  in
                         u_res :: uu____3117  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3126 =
                         let uu____3131 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____3132 =
                           let uu____3133 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3142 =
                             let uu____3153 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3162 =
                               let uu____3173 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3173]  in
                             uu____3153 :: uu____3162  in
                           uu____3133 :: uu____3142  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3131 uu____3132
                          in
                       uu____3126 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3215 = destruct_wp_comp c1  in
              match uu____3215 with
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
                let uu____3255 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3255
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
                  let uu____3305 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3305
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3318  ->
            match uu___0_3318 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3321 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3346 =
            let uu____3349 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3349 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3346
            (fun c  ->
               (let uu____3405 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3405) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3409 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3409)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3420 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3420 with
                | (head1,uu____3437) ->
                    let uu____3458 =
                      let uu____3459 = FStar_Syntax_Util.un_uinst head1  in
                      uu____3459.FStar_Syntax_Syntax.n  in
                    (match uu____3458 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3464 =
                           let uu____3466 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3466
                            in
                         Prims.op_Negation uu____3464
                     | uu____3467 -> true)))
              &&
              (let uu____3470 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3470)
  
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
            let uu____3498 =
              let uu____3500 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3500  in
            if uu____3498
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3507 = FStar_Syntax_Util.is_unit t  in
               if uu____3507
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
                    let uu____3516 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3516
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3522 =
                         let uu____3523 =
                           let uu____3528 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3529 =
                             let uu____3530 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3539 =
                               let uu____3550 = FStar_Syntax_Syntax.as_arg v1
                                  in
                               [uu____3550]  in
                             uu____3530 :: uu____3539  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3528
                             uu____3529
                            in
                         uu____3523 FStar_Pervasives_Native.None
                           v1.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3522)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3584 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3584
           then
             let uu____3589 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3591 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3593 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3589 uu____3591 uu____3593
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
                      (let uu____3666 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3666
                       then
                         let uu____3671 =
                           let uu____3673 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3673  in
                         let uu____3674 =
                           let uu____3676 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3676  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3671 uu____3674
                       else ());
                      (let uu____3680 =
                         let uu____3687 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3688 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3689 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3687, uu____3688, uu____3689)  in
                       match uu____3680 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3697 =
                             let uu____3708 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3709 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3708,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3709)
                              in
                           (match uu____3697 with
                            | (u1,t1,is1) ->
                                let uu____3743 =
                                  let uu____3754 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3755 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3754,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3755)
                                   in
                                (match uu____3743 with
                                 | (u2,t2,is2) ->
                                     let uu____3789 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3789 with
                                      | (uu____3798,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3813 =
                                              let uu____3815 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3815 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3813)
                                             in
                                          let uu____3819 =
                                            let uu____3864 =
                                              let uu____3865 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3865.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3864 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3941 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3941 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4026 =
                                                       let uu____4053 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4053
                                                         (fun uu____4138  ->
                                                            match uu____4138
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4219
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4232
                                                                  =
                                                                  let uu____4239
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4239
                                                                   in
                                                                (l1,
                                                                  uu____4219,
                                                                  uu____4232))
                                                        in
                                                     (match uu____4026 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          let uu____4367 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c1
                                                             in
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b,
                                                            uu____4367)))
                                            | uu____4400 ->
                                                let uu____4401 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4401 r1
                                             in
                                          (match uu____3819 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                               ->
                                               let uu____4526 =
                                                 let uu____4533 =
                                                   let uu____4534 =
                                                     let uu____4535 =
                                                       let uu____4542 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4542, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4535
                                                      in
                                                   let uu____4553 =
                                                     let uu____4556 =
                                                       let uu____4557 =
                                                         let uu____4564 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4564, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4557
                                                        in
                                                     [uu____4556]  in
                                                   uu____4534 :: uu____4553
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4533
                                                   (fun b1  ->
                                                      let uu____4580 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4582 =
                                                        let uu____4584 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4586 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4588 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4584
                                                          uu____4586
                                                          uu____4588
                                                         in
                                                      let uu____4591 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4580 uu____4582
                                                        uu____4591) r1
                                                  in
                                               (match uu____4526 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4628 =
                                                               let uu____4635
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4635,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4628)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4662 =
                                                          let uu____4665 =
                                                            let uu____4666 =
                                                              let uu____4667
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4667.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4666
                                                             in
                                                          let uu____4676 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4665
                                                            uu____4676 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4662
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4689
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4689)
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
                                                        let uu____4708 =
                                                          let uu____4709 =
                                                            let uu____4712 =
                                                              let uu____4713
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4713.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4712
                                                             in
                                                          uu____4709.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4708 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4746 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4746
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4756
                                                                    =
                                                                    let uu____4763
                                                                    =
                                                                    let uu____4764
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4764
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4785
                                                                    =
                                                                    let uu____4788
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4788
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4763,
                                                                    uu____4785)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4756
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4802
                                                                   =
                                                                   let uu____4805
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4806
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4805
                                                                    uu____4806
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4802
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4825 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4833
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4833)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4825
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let is =
                                                      let uu____4849 =
                                                        let uu____4852 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____4853 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____4852
                                                          uu____4853 r1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4849
                                                        (FStar_List.map
                                                           (FStar_Syntax_Subst.subst
                                                              subst1))
                                                       in
                                                    let c =
                                                      let uu____4860 =
                                                        let uu____4861 =
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
                                                            = uu____4861;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4860
                                                       in
                                                    ((let uu____4881 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4881
                                                      then
                                                        let uu____4886 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4886
                                                      else ());
                                                     (let uu____4891 =
                                                        FStar_TypeChecker_Env.conj_guards
                                                          [g_uvars;
                                                          f_guard;
                                                          g_guard]
                                                         in
                                                      (c, uu____4891)))))))))
  
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
                let uu____4936 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4962 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4962 with
                  | (a,kwp) ->
                      let uu____4993 = destruct_wp_comp ct1  in
                      let uu____5000 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4993, uu____5000)
                   in
                match uu____4936 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5053 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5053]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5073 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5073]
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
                      let uu____5120 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5129 =
                        let uu____5140 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5149 =
                          let uu____5160 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5169 =
                            let uu____5180 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5189 =
                              let uu____5200 =
                                let uu____5209 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5209  in
                              [uu____5200]  in
                            uu____5180 :: uu____5189  in
                          uu____5160 :: uu____5169  in
                        uu____5140 :: uu____5149  in
                      uu____5120 :: uu____5129  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5262 =
                        let uu____5267 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5267 wp_args  in
                      uu____5262 FStar_Pervasives_Native.None
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
              let uu____5315 =
                let uu____5320 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5321 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5320, uu____5321)  in
              match uu____5315 with
              | (ct1,ct2) ->
                  let uu____5328 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5328 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5379 = lift_comps env c1 c2 b true  in
                       (match uu____5379 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5397 =
                              let uu____5402 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5403 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5402, uu____5403)  in
                            (match uu____5397 with
                             | (ct11,ct21) ->
                                 let uu____5410 =
                                   let uu____5415 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5415
                                   then
                                     let bind_t =
                                       let uu____5423 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5423
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5426 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5426,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5410 with
                                  | (c,g_bind) ->
                                      let uu____5433 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5433)))))
  
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
            let uu____5469 =
              let uu____5470 =
                let uu____5481 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5481]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5470;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5469  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5526 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5532  ->
              match uu___1_5532 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5535 -> false))
       in
    if uu____5526
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5547  ->
              match uu___2_5547 with
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
        let uu____5575 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5575
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5586 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5586  in
           let pure_assume_wp1 =
             let uu____5591 = FStar_TypeChecker_Env.get_range env  in
             let uu____5592 =
               let uu____5597 =
                 let uu____5598 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5598]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5597  in
             uu____5592 FStar_Pervasives_Native.None uu____5591  in
           let uu____5631 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5631)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5659 =
          let uu____5660 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5660 with
          | (c,g_c) ->
              let uu____5671 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5671
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5685 = weaken_comp env c f1  in
                     (match uu____5685 with
                      | (c1,g_w) ->
                          let uu____5696 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5696)))
           in
        let uu____5697 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5697 weaken
  
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
                 let uu____5754 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5754  in
               let pure_assert_wp1 =
                 let uu____5759 =
                   let uu____5764 =
                     let uu____5765 =
                       let uu____5774 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5774
                        in
                     [uu____5765]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5764
                    in
                 uu____5759 FStar_Pervasives_Native.None r  in
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
       (let uu____5866 = FStar_Options.debug_any ()  in
        if uu____5866
        then
          let uu____5869 = FStar_Util.string_of_int n1  in
          let uu____5871 =
            let uu____5873 =
              let uu____5875 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____5875  in
            FStar_Util.string_of_int uu____5873  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____5869
            uu____5871
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
            let uu____5930 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5930
            then (lc, g0)
            else
              (let flags =
                 let uu____5942 =
                   let uu____5950 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5950
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5942 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5980 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5988  ->
                               match uu___3_5988 with
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
                               | uu____5991 -> []))
                        in
                     FStar_List.append flags uu____5980
                  in
               let strengthen uu____6001 =
                 let uu____6002 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____6002 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6021 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6021 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6028 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6028
                              then
                                let uu____6032 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6034 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6032 uu____6034
                              else ());
                             (let uu____6039 =
                                strengthen_comp env reason c f flags  in
                              match uu____6039 with
                              | (c1,g_s) ->
                                  let uu____6050 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6050))))
                  in
               let uu____6051 =
                 let uu____6052 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6052
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6051,
                 (let uu___699_6054 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___699_6054.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___699_6054.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___699_6054.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6063  ->
            match uu___4_6063 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6067 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6096 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6096
          then e
          else
            (let uu____6103 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6106 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6106)
                in
             if uu____6103
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
                | uu____6176 -> false  in
              if is_unit1
              then
                let uu____6183 =
                  let uu____6185 =
                    let uu____6186 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6186
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6185
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6183
                 then
                   let uu____6195 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6195 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6239 =
                           let uu____6242 =
                             let uu____6243 =
                               let uu____6250 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6250, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6243  in
                           [uu____6242]  in
                         FStar_Syntax_Subst.subst uu____6239 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6263 = close_wp_comp env [x] c  in
                    (uu____6263, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6266 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6294  ->
            match uu____6294 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6314 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6314 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6327 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6327
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6337 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6337
                       then
                         let uu____6342 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6342
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6349 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6349
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6358 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6358
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6365 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6365
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6381 =
                  let uu____6382 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6382
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6390 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6390, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6393 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6393 with
                     | (c1,g_c1) ->
                         let uu____6404 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6404 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____6424  ->
                                    let uu____6425 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6427 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6432 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6425 uu____6427 uu____6432);
                               (let aux uu____6450 =
                                  let uu____6451 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6451
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6482
                                        ->
                                        let uu____6483 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6483
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6515 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6515
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6562 =
                                  let aux_with_trivial_guard uu____6592 =
                                    let uu____6593 = aux ()  in
                                    match uu____6593 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6651 =
                                    let uu____6653 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6653  in
                                  if uu____6651
                                  then
                                    let uu____6669 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6669
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6696 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6696))
                                  else
                                    (let uu____6713 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6713
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___798_6759 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___798_6759.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___798_6759.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____6760 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____6760 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6818 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____6818
                                             (close1 x "c1 Tot")
                                       | (uu____6834,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____6859,uu____6860) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6875 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6875
                                        then
                                          let uu____6890 =
                                            let uu____6898 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6898,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6890
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6911 = try_simplify ()  in
                                match uu____6911 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____6946  ->
                                          let uu____6947 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6947);
                                     (let uu____6950 =
                                        let uu____6951 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____6951
                                         in
                                      (c, uu____6950)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____6965  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____6991 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6991 with
                                        | (c,g_bind) ->
                                            let uu____7002 =
                                              let uu____7003 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____7003 g_bind
                                               in
                                            (c, uu____7002)
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
                                        let uu____7030 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7030 with
                                        | (m,uu____7042,lift2) ->
                                            let uu____7044 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7044 with
                                             | (c23,g2) ->
                                                 let uu____7055 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7055 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7071 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7071
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7081 =
                                                          let uu____7086 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7087 =
                                                            let uu____7088 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7097 =
                                                              let uu____7108
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7108]
                                                               in
                                                            uu____7088 ::
                                                              uu____7097
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7086
                                                            uu____7087
                                                           in
                                                        uu____7081
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7141 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7141 with
                                                       | (c,g_s) ->
                                                           let uu____7156 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7156))))
                                         in
                                      let uu____7157 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7173 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7173, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7157 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7189 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7189
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7198 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7198
                                             then
                                               (debug1
                                                  (fun uu____7212  ->
                                                     let uu____7213 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7215 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7213 uu____7215);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____7223 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7226 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7226)
                                                   in
                                                if uu____7223
                                                then
                                                  let e1' =
                                                    let uu____7251 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7251
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7263  ->
                                                        let uu____7264 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7266 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7264
                                                          uu____7266);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7281  ->
                                                        let uu____7282 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7284 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7282
                                                          uu____7284);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7291 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7291
                                                       in
                                                    let uu____7292 =
                                                      let uu____7297 =
                                                        let uu____7298 =
                                                          let uu____7299 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7299]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7298
                                                         in
                                                      weaken_comp uu____7297
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7292 with
                                                    | (c22,g_w) ->
                                                        let uu____7324 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____7324
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7335 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7335))))))
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
      | uu____7352 -> g2
  
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
            (let uu____7376 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7376)
           in
        let flags =
          if should_return1
          then
            let uu____7384 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7384
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7402 =
          let uu____7403 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7403 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7416 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7416
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7424 =
                  let uu____7426 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7426  in
                (if uu____7424
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___917_7435 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___917_7435.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___917_7435.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___917_7435.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7436 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7436, g_c)
                 else
                   (let uu____7439 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7439, g_c)))
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
                   let uu____7450 =
                     let uu____7451 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7451
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7450
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7454 =
                   let uu____7459 =
                     let uu____7460 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7460
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7459  in
                 match uu____7454 with
                 | (bind_c,g_bind) ->
                     let uu____7469 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7470 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7469, uu____7470))
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
            fun uu____7506  ->
              match uu____7506 with
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
                    let uu____7518 =
                      ((let uu____7522 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7522) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7518
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7540 =
        let uu____7541 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7541  in
      FStar_Syntax_Syntax.fvar uu____7540 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7591 =
                    let uu____7596 =
                      let uu____7597 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7597 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7596 [u_a]
                     in
                  match uu____7591 with
                  | (uu____7608,conjunction) ->
                      let uu____7610 =
                        let uu____7619 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7634 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7619, uu____7634)  in
                      (match uu____7610 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7680 =
                               let uu____7682 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7682 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7680)
                              in
                           let uu____7686 =
                             let uu____7731 =
                               let uu____7732 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7732.FStar_Syntax_Syntax.n  in
                             match uu____7731 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7781) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7813 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7813 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7885 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7885 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8033 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8033)))
                             | uu____8066 ->
                                 let uu____8067 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8067 r
                              in
                           (match uu____7686 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8192 =
                                  let uu____8199 =
                                    let uu____8200 =
                                      let uu____8201 =
                                        let uu____8208 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8208, a)  in
                                      FStar_Syntax_Syntax.NT uu____8201  in
                                    [uu____8200]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8199
                                    (fun b  ->
                                       let uu____8224 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8226 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8228 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8224 uu____8226 uu____8228) r
                                   in
                                (match uu____8192 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8266 =
                                                let uu____8273 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8273, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8266) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8312 =
                                           let uu____8313 =
                                             let uu____8316 =
                                               let uu____8317 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8317.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8316
                                              in
                                           uu____8313.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8312 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8328,uu____8329::is) ->
                                             let uu____8371 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8371
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8404 ->
                                             let uu____8405 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8405 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8421 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8421)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8426 =
                                           let uu____8427 =
                                             let uu____8430 =
                                               let uu____8431 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8431.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8430
                                              in
                                           uu____8427.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8426 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8442,uu____8443::is) ->
                                             let uu____8485 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8485
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8518 ->
                                             let uu____8519 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8519 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8535 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8535)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8540 =
                                         let uu____8541 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8541.FStar_Syntax_Syntax.n  in
                                       match uu____8540 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8546,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8601 ->
                                           let uu____8602 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8602 r
                                        in
                                     let uu____8611 =
                                       let uu____8612 =
                                         let uu____8613 =
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
                                             uu____8613;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8612
                                        in
                                     let uu____8636 =
                                       let uu____8637 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8637 g_guard
                                        in
                                     (uu____8611, uu____8636))))
  
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
                fun uu____8682  ->
                  let if_then_else1 =
                    let uu____8688 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8688 FStar_Util.must  in
                  let uu____8695 = destruct_wp_comp ct1  in
                  match uu____8695 with
                  | (uu____8706,uu____8707,wp_t) ->
                      let uu____8709 = destruct_wp_comp ct2  in
                      (match uu____8709 with
                       | (uu____8720,uu____8721,wp_e) ->
                           let wp =
                             let uu____8726 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8727 =
                               let uu____8732 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8733 =
                                 let uu____8734 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8743 =
                                   let uu____8754 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8763 =
                                     let uu____8774 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8783 =
                                       let uu____8794 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8794]  in
                                     uu____8774 :: uu____8783  in
                                   uu____8754 :: uu____8763  in
                                 uu____8734 :: uu____8743  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8732
                                 uu____8733
                                in
                             uu____8727 FStar_Pervasives_Native.None
                               uu____8726
                              in
                           let uu____8843 = mk_comp ed u_a a wp []  in
                           (uu____8843, FStar_TypeChecker_Env.trivial_guard))
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ * FStar_Ident.lident *
        FStar_Syntax_Syntax.cflag Prims.list *
        (Prims.bool -> FStar_TypeChecker_Common.lcomp)) Prims.list ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____8913  ->
                 match uu____8913 with
                 | (uu____8927,eff_label,uu____8929,uu____8930) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____8943 =
          let uu____8951 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____8989  ->
                    match uu____8989 with
                    | (uu____9004,uu____9005,flags,uu____9007) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_9024  ->
                                match uu___5_9024 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____9027 -> false))))
             in
          if uu____8951
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____8943 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____9064 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____9066 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____9066
              then
                let uu____9073 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____9073, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____9080 =
                       let uu____9089 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____9089]  in
                     let uu____9108 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____9080 uu____9108  in
                   let kwp =
                     let uu____9114 =
                       let uu____9123 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____9123]  in
                     let uu____9142 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____9114 uu____9142  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____9149 =
                       let uu____9150 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____9150]  in
                     let uu____9169 =
                       let uu____9172 =
                         let uu____9179 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____9179
                          in
                       let uu____9180 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____9172 uu____9180  in
                     FStar_Syntax_Util.abs uu____9149 uu____9169
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
                   let uu____9204 =
                     should_not_inline_whole_match ||
                       (let uu____9207 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____9207)
                      in
                   if uu____9204 then cthen true else cthen false  in
                 let uu____9214 =
                   FStar_List.fold_right
                     (fun uu____9267  ->
                        fun uu____9268  ->
                          match (uu____9267, uu____9268) with
                          | ((g,eff_label,uu____9322,cthen),(uu____9324,celse,g_comp))
                              ->
                              let uu____9365 =
                                let uu____9370 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____9370
                                 in
                              (match uu____9365 with
                               | (cthen1,gthen) ->
                                   let uu____9381 =
                                     let uu____9390 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____9390 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____9413 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____9414 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____9413, uu____9414, g_lift)
                                      in
                                   (match uu____9381 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____9464 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____9464
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____9498 =
                                          let uu____9503 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____9503
                                           in
                                        (match uu____9498 with
                                         | (c,g_conjunction) ->
                                             let uu____9514 =
                                               let uu____9515 =
                                                 let uu____9516 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____9516 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____9515 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____9514)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____9214 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____9550::[] -> (comp, g_comp)
                      | uu____9593 ->
                          let uu____9610 =
                            let uu____9612 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____9612
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____9610
                          then (comp, g_comp)
                          else
                            (let comp1 =
                               FStar_TypeChecker_Env.comp_to_comp_typ env
                                 comp
                                in
                             let md1 =
                               FStar_TypeChecker_Env.get_effect_decl env
                                 comp1.FStar_Syntax_Syntax.effect_name
                                in
                             let uu____9625 = destruct_wp_comp comp1  in
                             match uu____9625 with
                             | (uu____9636,uu____9637,wp) ->
                                 let ite_wp =
                                   let uu____9640 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____9640
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____9650 =
                                     let uu____9655 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____9656 =
                                       let uu____9657 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____9666 =
                                         let uu____9677 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____9677]  in
                                       uu____9657 :: uu____9666  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____9655
                                       uu____9656
                                      in
                                   uu____9650 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____9710 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____9710, g_comp))))
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
          let uu____9745 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____9745 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____9761 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____9767 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____9761 uu____9767
              else
                (let uu____9776 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____9782 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____9776 uu____9782)
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
          let uu____9807 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____9807
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____9810 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____9810
        then u_res
        else
          (let is_total =
             let uu____9817 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____9817
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____9828 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____9828 with
              | FStar_Pervasives_Native.None  ->
                  let uu____9831 =
                    let uu____9837 =
                      let uu____9839 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____9839
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____9837)
                     in
                  FStar_Errors.raise_error uu____9831
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
      let uu____9863 = destruct_wp_comp ct  in
      match uu____9863 with
      | (u_t,t,wp) ->
          let vc =
            let uu____9882 = FStar_TypeChecker_Env.get_range env  in
            let uu____9883 =
              let uu____9888 =
                let uu____9889 =
                  let uu____9890 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____9890 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____9889
                 in
              let uu____9897 =
                let uu____9898 = FStar_Syntax_Syntax.as_arg t  in
                let uu____9907 =
                  let uu____9918 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____9918]  in
                uu____9898 :: uu____9907  in
              FStar_Syntax_Syntax.mk_Tm_app uu____9888 uu____9897  in
            uu____9883 FStar_Pervasives_Native.None uu____9882  in
          let uu____9951 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____9951)
  
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
                  let uu____10006 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____10006 with
                  | FStar_Pervasives_Native.Some uu____10021 ->
                      ((let uu____10039 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10039
                        then
                          let uu____10043 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10043
                        else ());
                       (let coercion =
                          let uu____10049 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10049
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10056 =
                            let uu____10057 =
                              let uu____10058 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10058
                               in
                            (FStar_Pervasives_Native.None, uu____10057)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10056
                           in
                        let e1 =
                          let uu____10064 =
                            let uu____10069 =
                              let uu____10070 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10070]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10069
                             in
                          uu____10064 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10104 =
                          let uu____10110 =
                            let uu____10112 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10112
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10110)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10104);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10131 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10149 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10160 -> false 
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
      let uu____10184 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10184 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10229 =
              let uu____10244 =
                let uu____10245 = FStar_Syntax_Subst.compress h1  in
                uu____10245.FStar_Syntax_Syntax.n  in
              (uu____10244, args)  in
            match uu____10229 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10292,uu____10293) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10326) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10347,branches),uu____10349) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10413 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10414 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10414 with
                               | (uu____10415,uu____10416,br_body) ->
                                   let uu____10434 =
                                     let uu____10435 =
                                       let uu____10440 =
                                         let uu____10441 =
                                           let uu____10444 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10444
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10441
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10440  in
                                     FStar_All.pipe_right br_body uu____10435
                                      in
                                   (match uu____10434 with
                                    | No  -> No
                                    | uu____10455 -> Maybe))) No)
            | uu____10456 -> No  in
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
            (((let uu____10508 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10508) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10527 =
                 let uu____10528 = FStar_Syntax_Subst.compress t1  in
                 uu____10528.FStar_Syntax_Syntax.n  in
               match uu____10527 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10533 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10543 =
                 let uu____10544 = FStar_Syntax_Subst.compress t1  in
                 uu____10544.FStar_Syntax_Syntax.n  in
               match uu____10543 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10549 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10559 =
                 let uu____10560 = FStar_Syntax_Subst.compress t1  in
                 uu____10560.FStar_Syntax_Syntax.n  in
               match uu____10559 with
               | FStar_Syntax_Syntax.Tm_type uu____10564 -> true
               | uu____10566 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10569 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10569 with
             | (head1,args) ->
                 ((let uu____10619 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____10619
                   then
                     let uu____10623 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____10625 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____10627 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____10629 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____10623 uu____10625 uu____10627 uu____10629
                   else ());
                  (let mk_erased u t =
                     let uu____10647 =
                       let uu____10650 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____10650 [u]  in
                     let uu____10651 =
                       let uu____10662 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____10662]  in
                     FStar_Syntax_Util.mk_app uu____10647 uu____10651  in
                   let uu____10687 =
                     let uu____10702 =
                       let uu____10703 = FStar_Syntax_Util.un_uinst head1  in
                       uu____10703.FStar_Syntax_Syntax.n  in
                     (uu____10702, args)  in
                   match uu____10687 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____10741 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____10741 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____10781 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10781 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10821 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10821 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10861 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10861 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____10882 ->
                       let uu____10897 =
                         let uu____10902 = check_erased env res_typ  in
                         let uu____10903 = check_erased env exp_t  in
                         (uu____10902, uu____10903)  in
                       (match uu____10897 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10912 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____10912 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____10923 =
                                   let uu____10928 =
                                     let uu____10929 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____10929]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____10928
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____10923 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10964 =
                              let uu____10969 =
                                let uu____10970 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____10970]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____10969
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____10964 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____11003 ->
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
        let uu____11038 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11038 with
        | (hd1,args) ->
            let uu____11087 =
              let uu____11102 =
                let uu____11103 = FStar_Syntax_Subst.compress hd1  in
                uu____11103.FStar_Syntax_Syntax.n  in
              (uu____11102, args)  in
            (match uu____11087 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11141 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11168  -> FStar_Pervasives_Native.Some _11168)
                   uu____11141
             | uu____11169 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11222 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11222
           then
             let uu____11225 = FStar_Syntax_Print.term_to_string e  in
             let uu____11227 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11229 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11225 uu____11227 uu____11229
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____11239 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11239 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11264 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11290 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11290, false)
             else
               (let uu____11300 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11300, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11313) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11325 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11325
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1337_11341 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1337_11341.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1337_11341.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1337_11341.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11348 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11348 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11364 =
                      let uu____11365 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11365 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11385 =
                            let uu____11387 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11387 = FStar_Syntax_Util.Equal  in
                          if uu____11385
                          then
                            ((let uu____11394 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11394
                              then
                                let uu____11398 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11400 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11398 uu____11400
                              else ());
                             (let uu____11405 = set_result_typ1 c  in
                              (uu____11405, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11412 ->
                                   true
                               | uu____11420 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11429 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11429
                                  in
                               let lc1 =
                                 let uu____11431 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11432 =
                                   let uu____11433 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11433)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11431 uu____11432
                                  in
                               ((let uu____11437 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11437
                                 then
                                   let uu____11441 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11443 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11445 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11447 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11441 uu____11443 uu____11445
                                     uu____11447
                                 else ());
                                (let uu____11452 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11452 with
                                 | (c1,g_lc) ->
                                     let uu____11463 = set_result_typ1 c1  in
                                     let uu____11464 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11463, uu____11464)))
                             else
                               ((let uu____11468 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11468
                                 then
                                   let uu____11472 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11474 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11472 uu____11474
                                 else ());
                                (let uu____11479 = set_result_typ1 c  in
                                 (uu____11479, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1374_11483 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1374_11483.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1374_11483.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1374_11483.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11493 =
                      let uu____11494 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11494
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11504 =
                           let uu____11505 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11505.FStar_Syntax_Syntax.n  in
                         match uu____11504 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11512,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11514;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11515;_},uu____11516)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1390_11542 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1390_11542.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1390_11542.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1390_11542.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11543 ->
                             let uu____11544 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11544 with
                              | (c,g_c) ->
                                  ((let uu____11556 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11556
                                    then
                                      let uu____11560 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11562 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11564 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11566 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11560 uu____11562 uu____11564
                                        uu____11566
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
                                        let uu____11579 =
                                          let uu____11584 =
                                            let uu____11585 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11585]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11584
                                           in
                                        uu____11579
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____11612 =
                                      let uu____11617 =
                                        FStar_All.pipe_left
                                          (fun _11638  ->
                                             FStar_Pervasives_Native.Some
                                               _11638)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____11639 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____11640 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____11641 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____11617
                                        uu____11639 e uu____11640 uu____11641
                                       in
                                    match uu____11612 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1408_11649 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1408_11649.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1408_11649.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____11651 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____11651
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____11654 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____11654 with
                                         | (c2,g_lc) ->
                                             ((let uu____11666 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____11666
                                               then
                                                 let uu____11670 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____11670
                                               else ());
                                              (let uu____11675 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____11675))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_11684  ->
                              match uu___6_11684 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____11687 -> []))
                       in
                    let lc1 =
                      let uu____11689 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____11689 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1424_11691 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1424_11691.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1424_11691.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1424_11691.FStar_TypeChecker_Common.implicits)
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
        let uu____11727 =
          let uu____11730 =
            let uu____11735 =
              let uu____11736 =
                let uu____11745 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____11745  in
              [uu____11736]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____11735  in
          uu____11730 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____11727  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____11768 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____11768
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____11787 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____11803 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____11820 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____11820
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____11836)::(ens,uu____11838)::uu____11839 ->
                    let uu____11882 =
                      let uu____11885 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____11885  in
                    let uu____11886 =
                      let uu____11887 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____11887  in
                    (uu____11882, uu____11886)
                | uu____11890 ->
                    let uu____11901 =
                      let uu____11907 =
                        let uu____11909 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____11909
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____11907)
                       in
                    FStar_Errors.raise_error uu____11901
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____11929)::uu____11930 ->
                    let uu____11957 =
                      let uu____11962 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____11962
                       in
                    (match uu____11957 with
                     | (us_r,uu____11994) ->
                         let uu____11995 =
                           let uu____12000 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____12000
                            in
                         (match uu____11995 with
                          | (us_e,uu____12032) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12035 =
                                  let uu____12036 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12036
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12035
                                  us_r
                                 in
                              let as_ens =
                                let uu____12038 =
                                  let uu____12039 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12039
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12038
                                  us_e
                                 in
                              let req =
                                let uu____12043 =
                                  let uu____12048 =
                                    let uu____12049 =
                                      let uu____12060 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12060]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12049
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12048
                                   in
                                uu____12043 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12100 =
                                  let uu____12105 =
                                    let uu____12106 =
                                      let uu____12117 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12117]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12106
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12105
                                   in
                                uu____12100 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12154 =
                                let uu____12157 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12157  in
                              let uu____12158 =
                                let uu____12159 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12159  in
                              (uu____12154, uu____12158)))
                | uu____12162 -> failwith "Impossible"))
  
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
        (let uu____12201 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12201
         then
           let uu____12206 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12208 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12206
             uu____12208
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
          (let uu____12267 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12267
           then
             let uu____12272 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12274 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12272
               uu____12274
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12285 =
      let uu____12287 =
        let uu____12288 = FStar_Syntax_Subst.compress t  in
        uu____12288.FStar_Syntax_Syntax.n  in
      match uu____12287 with
      | FStar_Syntax_Syntax.Tm_app uu____12292 -> false
      | uu____12310 -> true  in
    if uu____12285
    then t
    else
      (let uu____12315 = FStar_Syntax_Util.head_and_args t  in
       match uu____12315 with
       | (head1,args) ->
           let uu____12358 =
             let uu____12360 =
               let uu____12361 = FStar_Syntax_Subst.compress head1  in
               uu____12361.FStar_Syntax_Syntax.n  in
             match uu____12360 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12366 -> false  in
           if uu____12358
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12398 ->
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
          ((let uu____12445 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12445
            then
              let uu____12448 = FStar_Syntax_Print.term_to_string e  in
              let uu____12450 = FStar_Syntax_Print.term_to_string t  in
              let uu____12452 =
                let uu____12454 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12454
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12448 uu____12450 uu____12452
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____12467 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____12467 with
              | (formals,uu____12483) ->
                  let n_implicits =
                    let uu____12505 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____12583  ->
                              match uu____12583 with
                              | (uu____12591,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____12598 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____12598 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____12505 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____12723 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____12723 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____12737 =
                      let uu____12743 =
                        let uu____12745 = FStar_Util.string_of_int n_expected
                           in
                        let uu____12747 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____12749 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____12745 uu____12747 uu____12749
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____12743)
                       in
                    let uu____12753 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____12737 uu____12753
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_12771 =
              match uu___7_12771 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____12814 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____12814 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _12945,uu____12932)
                           when _12945 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____12978,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____12980))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13014 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____13014 with
                            | (v1,uu____13055,g) ->
                                ((let uu____13070 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13070
                                  then
                                    let uu____13073 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13073
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13083 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13083 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13176 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13176))))
                       | (uu____13203,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13240 =
                             let uu____13253 =
                               let uu____13260 =
                                 let uu____13265 = FStar_Dyn.mkdyn env  in
                                 (uu____13265, tau)  in
                               FStar_Pervasives_Native.Some uu____13260  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13253
                              in
                           (match uu____13240 with
                            | (v1,uu____13298,g) ->
                                ((let uu____13313 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13313
                                  then
                                    let uu____13316 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13316
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13326 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13326 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13419 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13419))))
                       | (uu____13446,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13494 =
                       let uu____13521 = inst_n_binders t1  in
                       aux [] uu____13521 bs1  in
                     (match uu____13494 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____13593) -> (e, torig, guard)
                           | (uu____13624,[]) when
                               let uu____13655 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____13655 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____13657 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____13685 ->
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
            | uu____13698 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____13710 =
      let uu____13714 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____13714
        (FStar_List.map
           (fun u  ->
              let uu____13726 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____13726 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____13710 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____13754 = FStar_Util.set_is_empty x  in
      if uu____13754
      then []
      else
        (let s =
           let uu____13772 =
             let uu____13775 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____13775  in
           FStar_All.pipe_right uu____13772 FStar_Util.set_elements  in
         (let uu____13791 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____13791
          then
            let uu____13796 =
              let uu____13798 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____13798  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____13796
          else ());
         (let r =
            let uu____13807 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____13807  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____13846 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____13846
                     then
                       let uu____13851 =
                         let uu____13853 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____13853
                          in
                       let uu____13857 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____13859 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____13851 uu____13857 uu____13859
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
        let uu____13889 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____13889 FStar_Util.set_elements  in
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
        | ([],uu____13928) -> generalized_univ_names
        | (uu____13935,[]) -> explicit_univ_names
        | uu____13942 ->
            let uu____13951 =
              let uu____13957 =
                let uu____13959 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____13959
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____13957)
               in
            FStar_Errors.raise_error uu____13951 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____13981 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____13981
       then
         let uu____13986 = FStar_Syntax_Print.term_to_string t  in
         let uu____13988 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____13986 uu____13988
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____13997 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____13997
        then
          let uu____14002 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____14002
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____14011 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____14011
         then
           let uu____14016 = FStar_Syntax_Print.term_to_string t  in
           let uu____14018 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____14016 uu____14018
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
        let uu____14102 =
          let uu____14104 =
            FStar_Util.for_all
              (fun uu____14118  ->
                 match uu____14118 with
                 | (uu____14128,uu____14129,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14104  in
        if uu____14102
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14181 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14181
              then
                let uu____14184 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14184
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14191 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14191
               then
                 let uu____14194 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14194
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14212 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14212 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14246 =
             match uu____14246 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14283 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14283
                   then
                     let uu____14288 =
                       let uu____14290 =
                         let uu____14294 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14294
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14290
                         (FStar_String.concat ", ")
                        in
                     let uu____14342 =
                       let uu____14344 =
                         let uu____14348 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14348
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14361 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14363 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14361
                                   uu____14363))
                          in
                       FStar_All.pipe_right uu____14344
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14288
                       uu____14342
                   else ());
                  (let univs2 =
                     let uu____14377 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14389 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14389) univs1
                       uu____14377
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14396 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14396
                    then
                      let uu____14401 =
                        let uu____14403 =
                          let uu____14407 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____14407
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14403
                          (FStar_String.concat ", ")
                         in
                      let uu____14455 =
                        let uu____14457 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14471 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14473 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14471
                                    uu____14473))
                           in
                        FStar_All.pipe_right uu____14457
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14401 uu____14455
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____14494 =
             let uu____14511 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14511  in
           match uu____14494 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____14601 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____14601
                 then ()
                 else
                   (let uu____14606 = lec_hd  in
                    match uu____14606 with
                    | (lb1,uu____14614,uu____14615) ->
                        let uu____14616 = lec2  in
                        (match uu____14616 with
                         | (lb2,uu____14624,uu____14625) ->
                             let msg =
                               let uu____14628 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14630 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____14628 uu____14630
                                in
                             let uu____14633 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____14633))
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
                 let uu____14701 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____14701
                 then ()
                 else
                   (let uu____14706 = lec_hd  in
                    match uu____14706 with
                    | (lb1,uu____14714,uu____14715) ->
                        let uu____14716 = lec2  in
                        (match uu____14716 with
                         | (lb2,uu____14724,uu____14725) ->
                             let msg =
                               let uu____14728 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14730 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____14728 uu____14730
                                in
                             let uu____14733 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____14733))
                  in
               let lecs1 =
                 let uu____14744 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____14797 = univs_and_uvars_of_lec this_lec  in
                        match uu____14797 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____14744 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____14902 = lec_hd  in
                   match uu____14902 with
                   | (lbname,e,c) ->
                       let uu____14912 =
                         let uu____14918 =
                           let uu____14920 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____14922 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____14924 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____14920 uu____14922 uu____14924
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____14918)
                          in
                       let uu____14928 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____14912 uu____14928
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____14947 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____14947 with
                         | FStar_Pervasives_Native.Some uu____14956 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____14964 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____14968 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____14968 with
                              | (bs,kres) ->
                                  ((let uu____15012 =
                                      let uu____15013 =
                                        let uu____15016 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____15016
                                         in
                                      uu____15013.FStar_Syntax_Syntax.n  in
                                    match uu____15012 with
                                    | FStar_Syntax_Syntax.Tm_type uu____15017
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15021 =
                                          let uu____15023 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15023  in
                                        if uu____15021
                                        then fail1 kres
                                        else ()
                                    | uu____15028 -> fail1 kres);
                                   (let a =
                                      let uu____15030 =
                                        let uu____15033 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15036  ->
                                             FStar_Pervasives_Native.Some
                                               _15036) uu____15033
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15030
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15044 ->
                                          let uu____15053 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15053
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
                      (fun uu____15156  ->
                         match uu____15156 with
                         | (lbname,e,c) ->
                             let uu____15202 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15263 ->
                                   let uu____15276 = (e, c)  in
                                   (match uu____15276 with
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
                                                (fun uu____15316  ->
                                                   match uu____15316 with
                                                   | (x,uu____15322) ->
                                                       let uu____15323 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15323)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15341 =
                                                let uu____15343 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15343
                                                 in
                                              if uu____15341
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
                                          let uu____15352 =
                                            let uu____15353 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15353.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15352 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15378 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15378 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15389 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15393 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15393, gen_tvars))
                                in
                             (match uu____15202 with
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
        (let uu____15540 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15540
         then
           let uu____15543 =
             let uu____15545 =
               FStar_List.map
                 (fun uu____15560  ->
                    match uu____15560 with
                    | (lb,uu____15569,uu____15570) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15545 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15543
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15596  ->
                match uu____15596 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____15625 = gen env is_rec lecs  in
           match uu____15625 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____15724  ->
                       match uu____15724 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____15786 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____15786
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____15834  ->
                           match uu____15834 with
                           | (l,us,e,c,gvs) ->
                               let uu____15868 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____15870 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____15872 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____15874 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15876 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____15868 uu____15870 uu____15872
                                 uu____15874 uu____15876))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____15921  ->
                match uu____15921 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____15965 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____15965, t, c, gvs)) univnames_lecs
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
        let uu____16020 =
          let uu____16024 =
            let uu____16026 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16026  in
          FStar_Pervasives_Native.Some uu____16024  in
        FStar_Profiling.profile
          (fun uu____16043  -> generalize' env is_rec lecs) uu____16020
          "FStar.TypeChecker.Util.generalize"
  
let (check_and_ascribe :
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
              (let uu____16103 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____16103 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____16109 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _16112  -> FStar_Pervasives_Native.Some _16112)
                     uu____16109)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1881_16132 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1881_16132.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1881_16132.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____16133 -> e2  in
          let uu____16134 = maybe_coerce_lc env1 e lc t2  in
          match uu____16134 with
          | (e1,lc1,g_c) ->
              let uu____16150 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16150 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16159 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16165 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16159 uu____16165
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16174 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16174
                     then
                       let uu____16179 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16179
                     else ());
                    (let uu____16185 = decorate e1 t2  in
                     let uu____16186 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____16185, lc1, uu____16186))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16214 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16214
         then
           let uu____16217 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16217
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16231 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16231 with
         | (c,g_c) ->
             let uu____16243 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16243
             then
               let uu____16251 =
                 let uu____16253 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16253  in
               (uu____16251, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16261 =
                    let uu____16262 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16262
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16261
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16263 = check_trivial_precondition env c1  in
                match uu____16263 with
                | (ct,vc,g_pre) ->
                    ((let uu____16279 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16279
                      then
                        let uu____16284 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16284
                      else ());
                     (let uu____16289 =
                        let uu____16291 =
                          let uu____16292 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16292  in
                        discharge uu____16291  in
                      let uu____16293 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16289, uu____16293)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16327 =
        match uu___8_16327 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16337)::[] -> f fst1
        | uu____16362 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16374 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16374
          (fun _16375  -> FStar_TypeChecker_Common.NonTrivial _16375)
         in
      let op_or_e e =
        let uu____16386 =
          let uu____16387 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16387  in
        FStar_All.pipe_right uu____16386
          (fun _16390  -> FStar_TypeChecker_Common.NonTrivial _16390)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16397  -> FStar_TypeChecker_Common.NonTrivial _16397)
         in
      let op_or_t t =
        let uu____16408 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16408
          (fun _16411  -> FStar_TypeChecker_Common.NonTrivial _16411)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16418  -> FStar_TypeChecker_Common.NonTrivial _16418)
         in
      let short_op_ite uu___9_16424 =
        match uu___9_16424 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16434)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16461)::[] ->
            let uu____16502 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16502
              (fun _16503  -> FStar_TypeChecker_Common.NonTrivial _16503)
        | uu____16504 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16516 =
          let uu____16524 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16524)  in
        let uu____16532 =
          let uu____16542 =
            let uu____16550 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16550)  in
          let uu____16558 =
            let uu____16568 =
              let uu____16576 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16576)  in
            let uu____16584 =
              let uu____16594 =
                let uu____16602 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____16602)  in
              let uu____16610 =
                let uu____16620 =
                  let uu____16628 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____16628)  in
                [uu____16620; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____16594 :: uu____16610  in
            uu____16568 :: uu____16584  in
          uu____16542 :: uu____16558  in
        uu____16516 :: uu____16532  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____16690 =
            FStar_Util.find_map table
              (fun uu____16705  ->
                 match uu____16705 with
                 | (x,mk1) ->
                     let uu____16722 = FStar_Ident.lid_equals x lid  in
                     if uu____16722
                     then
                       let uu____16727 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____16727
                     else FStar_Pervasives_Native.None)
             in
          (match uu____16690 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____16731 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____16739 =
      let uu____16740 = FStar_Syntax_Util.un_uinst l  in
      uu____16740.FStar_Syntax_Syntax.n  in
    match uu____16739 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____16745 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____16781)::uu____16782 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____16801 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____16810,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____16811))::uu____16812 -> bs
      | uu____16830 ->
          let uu____16831 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____16831 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____16835 =
                 let uu____16836 = FStar_Syntax_Subst.compress t  in
                 uu____16836.FStar_Syntax_Syntax.n  in
               (match uu____16835 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____16840) ->
                    let uu____16861 =
                      FStar_Util.prefix_until
                        (fun uu___10_16901  ->
                           match uu___10_16901 with
                           | (uu____16909,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____16910)) ->
                               false
                           | uu____16915 -> true) bs'
                       in
                    (match uu____16861 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____16951,uu____16952) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17024,uu____17025) ->
                         let uu____17098 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17118  ->
                                   match uu____17118 with
                                   | (x,uu____17127) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17098
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17176  ->
                                     match uu____17176 with
                                     | (x,i) ->
                                         let uu____17195 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17195, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17206 -> bs))
  
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
            let uu____17235 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17235
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
          let uu____17266 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17266
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
        (let uu____17309 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17309
         then
           ((let uu____17314 = FStar_Ident.text_of_lid lident  in
             d uu____17314);
            (let uu____17316 = FStar_Ident.text_of_lid lident  in
             let uu____17318 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17316 uu____17318))
         else ());
        (let fv =
           let uu____17324 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17324
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
         let uu____17336 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2042_17338 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2042_17338.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2042_17338.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2042_17338.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2042_17338.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2042_17338.FStar_Syntax_Syntax.sigopts)
           }), uu____17336))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17356 =
        match uu___11_17356 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17359 -> false  in
      let reducibility uu___12_17367 =
        match uu___12_17367 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17374 -> false  in
      let assumption uu___13_17382 =
        match uu___13_17382 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17386 -> false  in
      let reification uu___14_17394 =
        match uu___14_17394 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17397 -> true
        | uu____17399 -> false  in
      let inferred uu___15_17407 =
        match uu___15_17407 with
        | FStar_Syntax_Syntax.Discriminator uu____17409 -> true
        | FStar_Syntax_Syntax.Projector uu____17411 -> true
        | FStar_Syntax_Syntax.RecordType uu____17417 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17427 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17440 -> false  in
      let has_eq uu___16_17448 =
        match uu___16_17448 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17452 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17531 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17538 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17571 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17571))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17602 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____17602
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
           | FStar_Syntax_Syntax.Sig_bundle uu____17622 ->
               let uu____17631 =
                 let uu____17633 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_17639  ->
                           match uu___17_17639 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____17642 -> false))
                    in
                 Prims.op_Negation uu____17633  in
               if uu____17631
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____17649 -> ()
           | uu____17656 ->
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
      let uu____17670 =
        let uu____17672 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_17678  ->
                  match uu___18_17678 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____17681 -> false))
           in
        FStar_All.pipe_right uu____17672 Prims.op_Negation  in
      if uu____17670
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____17702 =
            let uu____17708 =
              let uu____17710 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____17710 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____17708)  in
          FStar_Errors.raise_error uu____17702 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____17728 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____17736 =
            let uu____17738 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____17738  in
          if uu____17736 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____17749),uu____17750) ->
              ((let uu____17762 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____17762
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____17771 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____17771
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____17782 ->
              ((let uu____17792 =
                  let uu____17794 =
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
                  Prims.op_Negation uu____17794  in
                if uu____17792 then err'1 () else ());
               (let uu____17804 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_17810  ->
                           match uu___19_17810 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____17813 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____17804
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____17819 ->
              let uu____17826 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____17826 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____17834 ->
              let uu____17841 =
                let uu____17843 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____17843  in
              if uu____17841 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17853 ->
              let uu____17854 =
                let uu____17856 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____17856  in
              if uu____17854 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17866 ->
              let uu____17879 =
                let uu____17881 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____17881  in
              if uu____17879 then err'1 () else ()
          | uu____17891 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____17930 =
          let uu____17931 = FStar_Syntax_Subst.compress t1  in
          uu____17931.FStar_Syntax_Syntax.n  in
        match uu____17930 with
        | FStar_Syntax_Syntax.Tm_arrow uu____17935 ->
            let uu____17950 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____17950 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17983;
               FStar_Syntax_Syntax.index = uu____17984;
               FStar_Syntax_Syntax.sort = t2;_},uu____17986)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____17995) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18021) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18027 -> false
      
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
        (let uu____18037 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18037
         then
           let uu____18042 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18042
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
                  let uu____18107 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18107 r  in
                let uu____18117 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18117 with
                | (uu____18126,signature) ->
                    let uu____18128 =
                      let uu____18129 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18129.FStar_Syntax_Syntax.n  in
                    (match uu____18128 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18137) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18185 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18200 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18202 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18200 eff_name.FStar_Ident.str
                                       uu____18202) r
                                 in
                              (match uu____18185 with
                               | (is,g) ->
                                   let uu____18215 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18217 =
                                             let uu____18218 =
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
                                                 = uu____18218;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18217
                                            in
                                         let uu____18237 =
                                           let uu____18244 =
                                             let uu____18245 =
                                               let uu____18260 =
                                                 let uu____18269 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18269]  in
                                               (uu____18260, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18245
                                              in
                                           FStar_Syntax_Syntax.mk uu____18244
                                            in
                                         uu____18237
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18300 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18300
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18309 =
                                           let uu____18314 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18314
                                            in
                                         uu____18309
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18215, g))
                          | uu____18323 -> fail1 signature)
                     | uu____18324 -> fail1 signature)
  
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
            let uu____18355 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18355
              (fun ed  ->
                 let uu____18363 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18363 u a_tm)
  
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
              let uu____18399 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18399 with
              | (uu____18404,sig_tm) ->
                  let fail1 t =
                    let uu____18412 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18412 r  in
                  let uu____18418 =
                    let uu____18419 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18419.FStar_Syntax_Syntax.n  in
                  (match uu____18418 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18423) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18446)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18468 -> fail1 sig_tm)
                   | uu____18469 -> fail1 sig_tm)
  
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
          (let uu____18500 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18500
           then
             let uu____18505 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18507 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18505 uu____18507
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18514 =
             let uu____18525 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18526 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18525, (ct.FStar_Syntax_Syntax.result_typ), uu____18526)
              in
           match uu____18514 with
           | (u,a,c_is) ->
               let uu____18574 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18574 with
                | (uu____18583,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18594 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18596 = FStar_Ident.string_of_lid tgt  in
                      let uu____18598 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18594 uu____18596 s uu____18598
                       in
                    let uu____18601 =
                      let uu____18634 =
                        let uu____18635 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____18635.FStar_Syntax_Syntax.n  in
                      match uu____18634 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____18699 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____18699 with
                           | (a_b::bs1,c2) ->
                               let uu____18759 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____18821 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____18759, uu____18821))
                      | uu____18848 ->
                          let uu____18849 =
                            let uu____18855 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18855)
                             in
                          FStar_Errors.raise_error uu____18849 r
                       in
                    (match uu____18601 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____18973 =
                           let uu____18980 =
                             let uu____18981 =
                               let uu____18982 =
                                 let uu____18989 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____18989, a)  in
                               FStar_Syntax_Syntax.NT uu____18982  in
                             [uu____18981]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18980
                             (fun b  ->
                                let uu____19006 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____19008 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____19010 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____19012 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____19006 uu____19008 uu____19010
                                  uu____19012) r
                            in
                         (match uu____18973 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19026 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19026
                                then
                                  let uu____19031 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19040 =
                                             let uu____19042 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19042
                                              in
                                           Prims.op_Hat s uu____19040) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19031
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19073 =
                                           let uu____19080 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19080, t)  in
                                         FStar_Syntax_Syntax.NT uu____19073)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19099 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19099
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19105 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19105
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19114 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19114)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____19118 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19118 r
                                   in
                                let c1 =
                                  let uu____19121 =
                                    let uu____19122 =
                                      let uu____19133 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____19133
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____19122;
                                      FStar_Syntax_Syntax.flags = []
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____19121  in
                                (let uu____19153 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____19153
                                 then
                                   let uu____19158 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____19158
                                 else ());
                                (let uu____19163 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____19163))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19177 .
    'Auu____19177 ->
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
              let uu____19206 =
                let uu____19211 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19211
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19206 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19254 =
                let uu____19255 =
                  let uu____19258 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19258
                    FStar_Syntax_Subst.compress
                   in
                uu____19255.FStar_Syntax_Syntax.n  in
              match uu____19254 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19281::bs,uu____19283)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19323 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19323
                    FStar_Pervasives_Native.fst
              | uu____19429 ->
                  let uu____19430 =
                    let uu____19436 =
                      let uu____19438 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19438
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19436)  in
                  FStar_Errors.raise_error uu____19430
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19465 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19474 =
                let uu____19485 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19521  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19528 =
                  let uu____19539 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19539]  in
                FStar_List.append uu____19485 uu____19528  in
              uu____19465 :: uu____19474  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____19610 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19610 with
        | (uu____19615,t) ->
            let err n1 =
              let uu____19625 =
                let uu____19631 =
                  let uu____19633 = FStar_Ident.string_of_lid datacon  in
                  let uu____19635 = FStar_Util.string_of_int n1  in
                  let uu____19637 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19633 uu____19635 uu____19637
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19631)
                 in
              let uu____19641 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19625 uu____19641  in
            let uu____19642 =
              let uu____19643 = FStar_Syntax_Subst.compress t  in
              uu____19643.FStar_Syntax_Syntax.n  in
            (match uu____19642 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19647) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19702  ->
                           match uu____19702 with
                           | (uu____19710,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____19719 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____19751 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____19751
                      FStar_Pervasives_Native.fst)
             | uu____19762 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____19775 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____19775
      then
        let uu____19778 =
          let uu____19791 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____19791
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____19778;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19826 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____19826 with
           | (uu____19835,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____19854 =
                 let uu____19855 =
                   let uu___2409_19856 = ct  in
                   let uu____19857 =
                     let uu____19868 =
                       let uu____19877 =
                         let uu____19878 =
                           let uu____19885 =
                             let uu____19886 =
                               let uu____19903 =
                                 let uu____19914 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____19914; wp]  in
                               (lift_t, uu____19903)  in
                             FStar_Syntax_Syntax.Tm_app uu____19886  in
                           FStar_Syntax_Syntax.mk uu____19885  in
                         uu____19878 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____19877
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____19868]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2409_19856.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2409_19856.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____19857;
                     FStar_Syntax_Syntax.flags =
                       (uu___2409_19856.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____19855  in
               (uu____19854, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____20014 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____20014 with
           | (uu____20021,lift_t) ->
               let uu____20023 =
                 let uu____20030 =
                   let uu____20031 =
                     let uu____20048 =
                       let uu____20059 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20068 =
                         let uu____20079 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20088 =
                           let uu____20099 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20099]  in
                         uu____20079 :: uu____20088  in
                       uu____20059 :: uu____20068  in
                     (lift_t, uu____20048)  in
                   FStar_Syntax_Syntax.Tm_app uu____20031  in
                 FStar_Syntax_Syntax.mk uu____20030  in
               uu____20023 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20152 =
           let uu____20165 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20165 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20152;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20201  ->
                        fun uu____20202  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20225 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20225
  
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
  