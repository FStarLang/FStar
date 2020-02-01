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
                        let uu____2560 = p_bind_opt  in
                        match uu____2560 with
                        | FStar_Pervasives_Native.Some (p,f_bind) ->
                            let uu____2607 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2607
                             then
                               let uu____2620 = bind_with_return c12 p f_bind
                                  in
                               match uu____2620 with
                               | (c13,g) ->
                                   let uu____2637 =
                                     let uu____2646 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2646, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2637
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2675 =
                      let uu____2684 = try_lift c11 c21  in
                      match uu____2684 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2723 = try_lift c21 c11  in
                          (match uu____2723 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2675 with
                    | (p,c12,c22,g) ->
                        ((let uu____2775 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2775
                          then
                            let uu____2780 = FStar_Ident.string_of_lid p  in
                            let uu____2782 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2784 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2780 uu____2782 uu____2784
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
          let uu____2844 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2844
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2856 =
      let uu____2857 = FStar_Syntax_Subst.compress t  in
      uu____2857.FStar_Syntax_Syntax.n  in
    match uu____2856 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2861 -> true
    | uu____2877 -> false
  
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
              let uu____2947 =
                let uu____2949 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____2949  in
              if uu____2947
              then f
              else (let uu____2956 = reason1 ()  in label uu____2956 r f)
  
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
            let uu___385_2977 = g  in
            let uu____2978 =
              let uu____2979 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____2979  in
            {
              FStar_TypeChecker_Common.guard_f = uu____2978;
              FStar_TypeChecker_Common.deferred =
                (uu___385_2977.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___385_2977.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___385_2977.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3000 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3000
        then c
        else
          (let uu____3005 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3005
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close1 =
                  let uu____3047 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3047 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3075 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3075]  in
                       let us =
                         let uu____3097 =
                           let uu____3100 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3100]  in
                         u_res :: uu____3097  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3106 =
                         let uu____3111 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md close1
                            in
                         let uu____3112 =
                           let uu____3113 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____3122 =
                             let uu____3133 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____3142 =
                               let uu____3153 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____3153]  in
                             uu____3133 :: uu____3142  in
                           uu____3113 :: uu____3122  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3111 uu____3112
                          in
                       uu____3106 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3195 = destruct_wp_comp c1  in
              match uu____3195 with
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
                let uu____3235 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3235
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
                  let uu____3285 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3285
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3298  ->
            match uu___0_3298 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3301 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3326 =
            let uu____3329 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3329 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3326
            (fun c  ->
               (let uu____3385 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3385) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3389 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3389)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3400 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3400 with
                | (head1,uu____3417) ->
                    let uu____3438 =
                      let uu____3439 = FStar_Syntax_Util.un_uinst head1  in
                      uu____3439.FStar_Syntax_Syntax.n  in
                    (match uu____3438 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3444 =
                           let uu____3446 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3446
                            in
                         Prims.op_Negation uu____3444
                     | uu____3447 -> true)))
              &&
              (let uu____3450 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3450)
  
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
            let uu____3478 =
              let uu____3480 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3480  in
            if uu____3478
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3487 = FStar_Syntax_Util.is_unit t  in
               if uu____3487
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
                    let uu____3496 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3496
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3502 =
                         let uu____3503 =
                           let uu____3508 =
                             FStar_TypeChecker_Env.inst_effect_fun_with 
                               [u_t] env m ret_wp
                              in
                           let uu____3509 =
                             let uu____3510 = FStar_Syntax_Syntax.as_arg t
                                in
                             let uu____3519 =
                               let uu____3530 = FStar_Syntax_Syntax.as_arg v1
                                  in
                               [uu____3530]  in
                             uu____3510 :: uu____3519  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3508
                             uu____3509
                            in
                         uu____3503 FStar_Pervasives_Native.None
                           v1.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3502)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3564 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3564
           then
             let uu____3569 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____3571 = FStar_Syntax_Print.term_to_string v1  in
             let uu____3573 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3569 uu____3571 uu____3573
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
                      (let uu____3646 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3646
                       then
                         let uu____3651 =
                           let uu____3653 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3653  in
                         let uu____3654 =
                           let uu____3656 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3656  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3651 uu____3654
                       else ());
                      (let uu____3660 =
                         let uu____3667 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3668 =
                           FStar_TypeChecker_Env.get_effect_decl env n1  in
                         let uu____3669 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3667, uu____3668, uu____3669)  in
                       match uu____3660 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3677 =
                             let uu____3688 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3689 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3688,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3689)
                              in
                           (match uu____3677 with
                            | (u1,t1,is1) ->
                                let uu____3723 =
                                  let uu____3734 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3735 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3734,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3735)
                                   in
                                (match uu____3723 with
                                 | (u2,t2,is2) ->
                                     let uu____3769 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3769 with
                                      | (uu____3778,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3793 =
                                              let uu____3795 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format2
                                                "bind %s does not have proper shape (reason:%s)"
                                                uu____3795 s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3793)
                                             in
                                          let uu____3799 =
                                            let uu____3844 =
                                              let uu____3845 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3845.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3844 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____3921 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____3921 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4006 =
                                                       let uu____4033 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4033
                                                         (fun uu____4118  ->
                                                            match uu____4118
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4199
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4212
                                                                  =
                                                                  let uu____4219
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4219
                                                                   in
                                                                (l1,
                                                                  uu____4199,
                                                                  uu____4212))
                                                        in
                                                     (match uu____4006 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          let uu____4347 =
                                                            FStar_Syntax_Util.comp_to_comp_typ
                                                              c1
                                                             in
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b,
                                                            uu____4347)))
                                            | uu____4380 ->
                                                let uu____4381 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4381 r1
                                             in
                                          (match uu____3799 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_ct)
                                               ->
                                               let uu____4506 =
                                                 let uu____4513 =
                                                   let uu____4514 =
                                                     let uu____4515 =
                                                       let uu____4522 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4522, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4515
                                                      in
                                                   let uu____4533 =
                                                     let uu____4536 =
                                                       let uu____4537 =
                                                         let uu____4544 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4544, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4537
                                                        in
                                                     [uu____4536]  in
                                                   uu____4514 :: uu____4533
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4513
                                                   (fun b1  ->
                                                      let uu____4560 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4562 =
                                                        let uu____4564 =
                                                          FStar_Ident.string_of_lid
                                                            m
                                                           in
                                                        let uu____4566 =
                                                          FStar_Ident.string_of_lid
                                                            n1
                                                           in
                                                        let uu____4568 =
                                                          FStar_Ident.string_of_lid
                                                            p
                                                           in
                                                        FStar_Util.format3
                                                          "(%s, %s) |> %s"
                                                          uu____4564
                                                          uu____4566
                                                          uu____4568
                                                         in
                                                      let uu____4571 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4560 uu____4562
                                                        uu____4571) r1
                                                  in
                                               (match uu____4506 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4608 =
                                                               let uu____4615
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4615,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4608)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4642 =
                                                          let uu____4645 =
                                                            let uu____4646 =
                                                              let uu____4647
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4647.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4646
                                                             in
                                                          let uu____4656 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4645
                                                            uu____4656 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4642
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst1))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4669
                                                                 =
                                                                 FStar_TypeChecker_Rel.teq
                                                                   env i1
                                                                   f_i1
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4669)
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
                                                        let uu____4688 =
                                                          let uu____4689 =
                                                            let uu____4692 =
                                                              let uu____4693
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4693.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4692
                                                             in
                                                          uu____4689.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4688 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4726 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4726
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4736
                                                                    =
                                                                    let uu____4743
                                                                    =
                                                                    let uu____4744
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4744
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4765
                                                                    =
                                                                    let uu____4768
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4768
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4743,
                                                                    uu____4765)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4736
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4782
                                                                   =
                                                                   let uu____4785
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4786
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4785
                                                                    uu____4786
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4782
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst1)))
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4805 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4813
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq
                                                                    env_g i1
                                                                    g_i1
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4813)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4805
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let is =
                                                      let uu____4829 =
                                                        let uu____4832 =
                                                          FStar_Syntax_Subst.compress
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                           in
                                                        let uu____4833 =
                                                          FStar_Syntax_Util.is_layered
                                                            p_ed
                                                           in
                                                        effect_args_from_repr
                                                          uu____4832
                                                          uu____4833 r1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4829
                                                        (FStar_List.map
                                                           (FStar_Syntax_Subst.subst
                                                              subst1))
                                                       in
                                                    let c =
                                                      let uu____4840 =
                                                        let uu____4841 =
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
                                                            = uu____4841;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4840
                                                       in
                                                    ((let uu____4861 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4861
                                                      then
                                                        let uu____4866 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4866
                                                      else ());
                                                     (let uu____4871 =
                                                        FStar_TypeChecker_Env.conj_guards
                                                          [g_uvars;
                                                          f_guard;
                                                          g_guard]
                                                         in
                                                      (c, uu____4871)))))))))
  
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
                let uu____4916 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____4942 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____4942 with
                  | (a,kwp) ->
                      let uu____4973 = destruct_wp_comp ct1  in
                      let uu____4980 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____4973, uu____4980)
                   in
                match uu____4916 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5033 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5033]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5053 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5053]
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
                      let uu____5100 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5109 =
                        let uu____5120 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5129 =
                          let uu____5140 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5149 =
                            let uu____5160 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5169 =
                              let uu____5180 =
                                let uu____5189 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5189  in
                              [uu____5180]  in
                            uu____5160 :: uu____5169  in
                          uu____5140 :: uu____5149  in
                        uu____5120 :: uu____5129  in
                      uu____5100 :: uu____5109  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5242 =
                        let uu____5247 =
                          FStar_TypeChecker_Env.inst_effect_fun_with
                            [u_t1; u_t2] env md bind_wp
                           in
                        FStar_Syntax_Syntax.mk_Tm_app uu____5247 wp_args  in
                      uu____5242 FStar_Pervasives_Native.None
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
              let uu____5295 =
                let uu____5300 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5301 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5300, uu____5301)  in
              match uu____5295 with
              | (ct1,ct2) ->
                  let uu____5308 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5308 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5359 = lift_comps env c1 c2 b true  in
                       (match uu____5359 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5377 =
                              let uu____5382 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5383 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5382, uu____5383)  in
                            (match uu____5377 with
                             | (ct11,ct21) ->
                                 let uu____5390 =
                                   let uu____5395 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5395
                                   then
                                     let bind_t =
                                       let uu____5403 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5403
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5406 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5406,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5390 with
                                  | (c,g_bind) ->
                                      let uu____5413 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5413)))))
  
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
            let uu____5449 =
              let uu____5450 =
                let uu____5461 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5461]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5450;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5449  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5506 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5512  ->
              match uu___1_5512 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5515 -> false))
       in
    if uu____5506
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5527  ->
              match uu___2_5527 with
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
        let uu____5555 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5555
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5566 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5566  in
           let pure_assume_wp1 =
             let uu____5571 = FStar_TypeChecker_Env.get_range env  in
             let uu____5572 =
               let uu____5577 =
                 let uu____5578 =
                   FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
                 [uu____5578]  in
               FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5577  in
             uu____5572 FStar_Pervasives_Native.None uu____5571  in
           let uu____5611 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5611)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5639 =
          let uu____5640 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5640 with
          | (c,g_c) ->
              let uu____5651 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5651
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5665 = weaken_comp env c f1  in
                     (match uu____5665 with
                      | (c1,g_w) ->
                          let uu____5676 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5676)))
           in
        let uu____5677 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5677 weaken
  
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
                 let uu____5734 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5734  in
               let pure_assert_wp1 =
                 let uu____5739 =
                   let uu____5744 =
                     let uu____5745 =
                       let uu____5754 = label_opt env reason r f  in
                       FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                         uu____5754
                        in
                     [uu____5745]  in
                   FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5744
                    in
                 uu____5739 FStar_Pervasives_Native.None r  in
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
       (let uu____5846 = FStar_Options.debug_any ()  in
        if uu____5846
        then
          let uu____5849 = FStar_Util.string_of_int n1  in
          let uu____5851 =
            let uu____5853 =
              let uu____5855 = FStar_Util.time_diff start fin  in
              FStar_Pervasives_Native.snd uu____5855  in
            FStar_Util.string_of_int uu____5853  in
          FStar_Util.print2 "Simplify_guard %s in %s ms\n" uu____5849
            uu____5851
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
            let uu____5910 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5910
            then (lc, g0)
            else
              (let flags =
                 let uu____5922 =
                   let uu____5930 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5930
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5922 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5960 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5968  ->
                               match uu___3_5968 with
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
                               | uu____5971 -> []))
                        in
                     FStar_List.append flags uu____5960
                  in
               let strengthen uu____5981 =
                 let uu____5982 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5982 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6001 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6001 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6008 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6008
                              then
                                let uu____6012 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6014 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6012 uu____6014
                              else ());
                             (let uu____6019 =
                                strengthen_comp env reason c f flags  in
                              match uu____6019 with
                              | (c1,g_s) ->
                                  let uu____6030 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6030))))
                  in
               let uu____6031 =
                 let uu____6032 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6032
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6031,
                 (let uu___700_6034 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___700_6034.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___700_6034.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___700_6034.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6043  ->
            match uu___4_6043 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6047 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6076 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6076
          then e
          else
            (let uu____6083 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6086 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6086)
                in
             if uu____6083
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
                | uu____6156 -> false  in
              if is_unit1
              then
                let uu____6163 =
                  let uu____6165 =
                    let uu____6166 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6166
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6165
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6163
                 then
                   let uu____6175 =
                     FStar_Syntax_Subst.open_term
                       [(b, FStar_Pervasives_Native.None)] phi
                      in
                   match uu____6175 with
                   | (b1::[],phi1) ->
                       let phi2 =
                         let uu____6219 =
                           let uu____6222 =
                             let uu____6223 =
                               let uu____6230 =
                                 FStar_All.pipe_right b1
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____6230, FStar_Syntax_Syntax.unit_const)
                                in
                             FStar_Syntax_Syntax.NT uu____6223  in
                           [uu____6222]  in
                         FStar_Syntax_Subst.subst uu____6219 phi1  in
                       weaken_comp env c phi2
                 else
                   (let uu____6243 = close_wp_comp env [x] c  in
                    (uu____6243, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6246 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6274  ->
            match uu____6274 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____6294 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6294 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6307 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6307
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6317 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6317
                       then
                         let uu____6322 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6322
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6329 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6329
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6338 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6338
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6345 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6345
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6361 =
                  let uu____6362 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6362
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6370 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6370, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6373 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6373 with
                     | (c1,g_c1) ->
                         let uu____6384 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6384 with
                          | (c2,g_c2) ->
                              (debug1
                                 (fun uu____6404  ->
                                    let uu____6405 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6407 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6412 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6405 uu____6407 uu____6412);
                               (let aux uu____6430 =
                                  let uu____6431 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6431
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6462
                                        ->
                                        let uu____6463 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6463
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6495 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6495
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6542 =
                                  let aux_with_trivial_guard uu____6572 =
                                    let uu____6573 = aux ()  in
                                    match uu____6573 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c,
                                            FStar_TypeChecker_Env.trivial_guard,
                                            reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6631 =
                                    let uu____6633 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6633  in
                                  if uu____6631
                                  then
                                    let uu____6649 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6649
                                     then
                                       FStar_Util.Inl
                                         (c2,
                                           FStar_TypeChecker_Env.trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6676 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6676))
                                  else
                                    (let uu____6693 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6693
                                     then
                                       let close1 x reason c =
                                         let x1 =
                                           let uu___799_6739 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___799_6739.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___799_6739.FStar_Syntax_Syntax.index);
                                             FStar_Syntax_Syntax.sort =
                                               (FStar_Syntax_Util.comp_result
                                                  c1)
                                           }  in
                                         let uu____6740 =
                                           maybe_capture_unit_refinement env
                                             x1.FStar_Syntax_Syntax.sort x1 c
                                            in
                                         match uu____6740 with
                                         | (c3,g_c) ->
                                             FStar_Util.Inl (c3, g_c, reason)
                                          in
                                       match (e1opt, b) with
                                       | (FStar_Pervasives_Native.Some
                                          e,FStar_Pervasives_Native.Some x)
                                           ->
                                           let uu____6798 =
                                             FStar_All.pipe_right c2
                                               (FStar_Syntax_Subst.subst_comp
                                                  [FStar_Syntax_Syntax.NT
                                                     (x, e)])
                                              in
                                           FStar_All.pipe_right uu____6798
                                             (close1 x "c1 Tot")
                                       | (uu____6814,FStar_Pervasives_Native.Some
                                          x) ->
                                           FStar_All.pipe_right c2
                                             (close1 x "c1 Tot only close")
                                       | (uu____6839,uu____6840) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6855 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6855
                                        then
                                          let uu____6870 =
                                            let uu____6878 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6878,
                                              FStar_TypeChecker_Env.trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6870
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6891 = try_simplify ()  in
                                match uu____6891 with
                                | FStar_Util.Inl (c,g_c,reason) ->
                                    (debug1
                                       (fun uu____6926  ->
                                          let uu____6927 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6927);
                                     (let uu____6930 =
                                        let uu____6931 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c1 g_c2
                                           in
                                        FStar_TypeChecker_Env.conj_guard g_c
                                          uu____6931
                                         in
                                      (c, uu____6930)))
                                | FStar_Util.Inr reason ->
                                    (debug1
                                       (fun uu____6945  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 =
                                        let uu____6971 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____6971 with
                                        | (c,g_bind) ->
                                            let uu____6982 =
                                              let uu____6983 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g_c1 g_c2
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                uu____6983 g_bind
                                               in
                                            (c, uu____6982)
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
                                        let uu____7010 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7010 with
                                        | (m,uu____7022,lift2) ->
                                            let uu____7024 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7024 with
                                             | (c23,g2) ->
                                                 let uu____7035 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7035 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7051 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7051
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7061 =
                                                          let uu____7066 =
                                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                                              [u1] env
                                                              md_pure_or_ghost
                                                              trivial
                                                             in
                                                          let uu____7067 =
                                                            let uu____7068 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t1
                                                               in
                                                            let uu____7077 =
                                                              let uu____7088
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  wp1
                                                                 in
                                                              [uu____7088]
                                                               in
                                                            uu____7068 ::
                                                              uu____7077
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7066
                                                            uu____7067
                                                           in
                                                        uu____7061
                                                          FStar_Pervasives_Native.None
                                                          r1
                                                         in
                                                      let uu____7121 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7121 with
                                                       | (c,g_s) ->
                                                           let uu____7136 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7136))))
                                         in
                                      let uu____7137 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7153 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7153, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7137 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7169 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7169
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7178 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7178
                                             then
                                               (debug1
                                                  (fun uu____7192  ->
                                                     let uu____7193 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7195 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7193 uu____7195);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 mk_bind1 c1 b c21))
                                             else
                                               (let uu____7203 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7206 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7206)
                                                   in
                                                if uu____7203
                                                then
                                                  let e1' =
                                                    let uu____7231 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7231
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug1
                                                     (fun uu____7243  ->
                                                        let uu____7244 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7246 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7244
                                                          uu____7246);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug1
                                                     (fun uu____7261  ->
                                                        let uu____7262 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7264 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7262
                                                          uu____7264);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7271 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7271
                                                       in
                                                    let uu____7272 =
                                                      let uu____7277 =
                                                        let uu____7278 =
                                                          let uu____7279 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7279]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7278
                                                         in
                                                      weaken_comp uu____7277
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7272 with
                                                    | (c22,g_w) ->
                                                        let uu____7304 =
                                                          mk_bind1 c1 b c22
                                                           in
                                                        (match uu____7304
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7315 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7315))))))
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
      | uu____7332 -> g2
  
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
            (let uu____7356 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7356)
           in
        let flags =
          if should_return1
          then
            let uu____7364 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7364
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine1 uu____7382 =
          let uu____7383 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7383 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7396 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7396
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7404 =
                  let uu____7406 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7406  in
                (if uu____7404
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___918_7415 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___918_7415.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___918_7415.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___918_7415.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7416 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7416, g_c)
                 else
                   (let uu____7419 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7419, g_c)))
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
                   let uu____7430 =
                     let uu____7431 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7431
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7430
                    in
                 let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret1
                     (FStar_TypeChecker_Common.NonTrivial eq1)
                    in
                 let uu____7434 =
                   let uu____7439 =
                     let uu____7440 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7440
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7439  in
                 match uu____7434 with
                 | (bind_c,g_bind) ->
                     let uu____7449 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7450 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7449, uu____7450))
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
            fun uu____7486  ->
              match uu____7486 with
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
                    let uu____7498 =
                      ((let uu____7502 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7502) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7498
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7520 =
        let uu____7521 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7521  in
      FStar_Syntax_Syntax.fvar uu____7520 FStar_Syntax_Syntax.delta_constant
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
                  let uu____7571 =
                    let uu____7576 =
                      let uu____7577 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7577 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7576 [u_a]
                     in
                  match uu____7571 with
                  | (uu____7588,conjunction) ->
                      let uu____7590 =
                        let uu____7599 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7614 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7599, uu____7614)  in
                      (match uu____7590 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7660 =
                               let uu____7662 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format2
                                 "conjunction %s does not have proper shape (reason:%s)"
                                 uu____7662 s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7660)
                              in
                           let uu____7666 =
                             let uu____7711 =
                               let uu____7712 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7712.FStar_Syntax_Syntax.n  in
                             match uu____7711 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7761) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7793 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7793 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7865 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7865 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8013 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8013)))
                             | uu____8046 ->
                                 let uu____8047 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8047 r
                              in
                           (match uu____7666 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8172 =
                                  let uu____8179 =
                                    let uu____8180 =
                                      let uu____8181 =
                                        let uu____8188 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8188, a)  in
                                      FStar_Syntax_Syntax.NT uu____8181  in
                                    [uu____8180]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8179
                                    (fun b  ->
                                       let uu____8204 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8206 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8208 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8204 uu____8206 uu____8208) r
                                   in
                                (match uu____8172 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8246 =
                                                let uu____8253 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8253, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8246) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8292 =
                                           let uu____8293 =
                                             let uu____8296 =
                                               let uu____8297 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8297.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8296
                                              in
                                           uu____8293.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8292 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8308,uu____8309::is) ->
                                             let uu____8351 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8351
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8384 ->
                                             let uu____8385 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8385 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8401 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i1 f_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8401)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8406 =
                                           let uu____8407 =
                                             let uu____8410 =
                                               let uu____8411 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8411.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8410
                                              in
                                           uu____8407.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8406 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8422,uu____8423::is) ->
                                             let uu____8465 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8465
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8498 ->
                                             let uu____8499 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8499 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8515 =
                                                  FStar_TypeChecker_Rel.teq
                                                    env i2 g_i
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8515)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8520 =
                                         let uu____8521 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8521.FStar_Syntax_Syntax.n  in
                                       match uu____8520 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8526,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8581 ->
                                           let uu____8582 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8582 r
                                        in
                                     let uu____8591 =
                                       let uu____8592 =
                                         let uu____8593 =
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
                                             uu____8593;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8592
                                        in
                                     let uu____8616 =
                                       let uu____8617 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8617 g_guard
                                        in
                                     (uu____8591, uu____8616))))
  
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
                fun uu____8662  ->
                  let if_then_else1 =
                    let uu____8668 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8668 FStar_Util.must  in
                  let uu____8675 = destruct_wp_comp ct1  in
                  match uu____8675 with
                  | (uu____8686,uu____8687,wp_t) ->
                      let uu____8689 = destruct_wp_comp ct2  in
                      (match uu____8689 with
                       | (uu____8700,uu____8701,wp_e) ->
                           let wp =
                             let uu____8706 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             let uu____8707 =
                               let uu____8712 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_a] env ed if_then_else1
                                  in
                               let uu____8713 =
                                 let uu____8714 =
                                   FStar_Syntax_Syntax.as_arg a  in
                                 let uu____8723 =
                                   let uu____8734 =
                                     FStar_Syntax_Syntax.as_arg p  in
                                   let uu____8743 =
                                     let uu____8754 =
                                       FStar_Syntax_Syntax.as_arg wp_t  in
                                     let uu____8763 =
                                       let uu____8774 =
                                         FStar_Syntax_Syntax.as_arg wp_e  in
                                       [uu____8774]  in
                                     uu____8754 :: uu____8763  in
                                   uu____8734 :: uu____8743  in
                                 uu____8714 :: uu____8723  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____8712
                                 uu____8713
                                in
                             uu____8707 FStar_Pervasives_Native.None
                               uu____8706
                              in
                           let uu____8823 = mk_comp ed u_a a wp []  in
                           (uu____8823, FStar_TypeChecker_Env.trivial_guard))
  
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
               fun uu____8893  ->
                 match uu____8893 with
                 | (uu____8907,eff_label,uu____8909,uu____8910) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____8923 =
          let uu____8931 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____8969  ->
                    match uu____8969 with
                    | (uu____8984,uu____8985,flags,uu____8987) ->
                        FStar_All.pipe_right flags
                          (FStar_Util.for_some
                             (fun uu___5_9004  ->
                                match uu___5_9004 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____9007 -> false))))
             in
          if uu____8931
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____8923 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____9044 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____9046 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____9046
              then
                let uu____9053 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                   in
                (uu____9053, FStar_TypeChecker_Env.trivial_guard)
              else
                (let default_case =
                   let post_k =
                     let uu____9060 =
                       let uu____9069 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____9069]  in
                     let uu____9088 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____9060 uu____9088  in
                   let kwp =
                     let uu____9094 =
                       let uu____9103 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____9103]  in
                     let uu____9122 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____9094 uu____9122  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____9129 =
                       let uu____9130 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____9130]  in
                     let uu____9149 =
                       let uu____9152 =
                         let uu____9159 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____9159
                          in
                       let uu____9160 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____9152 uu____9160  in
                     FStar_Syntax_Util.abs uu____9129 uu____9149
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
                   let uu____9184 =
                     should_not_inline_whole_match ||
                       (let uu____9187 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____9187)
                      in
                   if uu____9184 then cthen true else cthen false  in
                 let uu____9194 =
                   FStar_List.fold_right
                     (fun uu____9247  ->
                        fun uu____9248  ->
                          match (uu____9247, uu____9248) with
                          | ((g,eff_label,uu____9302,cthen),(uu____9304,celse,g_comp))
                              ->
                              let uu____9345 =
                                let uu____9350 = maybe_return eff_label cthen
                                   in
                                FStar_TypeChecker_Common.lcomp_comp
                                  uu____9350
                                 in
                              (match uu____9345 with
                               | (cthen1,gthen) ->
                                   let uu____9361 =
                                     let uu____9370 =
                                       lift_comps env cthen1 celse
                                         FStar_Pervasives_Native.None false
                                        in
                                     match uu____9370 with
                                     | (m,cthen2,celse1,g_lift) ->
                                         let md =
                                           FStar_TypeChecker_Env.get_effect_decl
                                             env m
                                            in
                                         let uu____9393 =
                                           FStar_All.pipe_right cthen2
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         let uu____9394 =
                                           FStar_All.pipe_right celse1
                                             FStar_Syntax_Util.comp_to_comp_typ
                                            in
                                         (md, uu____9393, uu____9394, g_lift)
                                      in
                                   (match uu____9361 with
                                    | (md,ct_then,ct_else,g_lift) ->
                                        let fn =
                                          let uu____9444 =
                                            FStar_All.pipe_right md
                                              FStar_Syntax_Util.is_layered
                                             in
                                          if uu____9444
                                          then mk_layered_conjunction
                                          else mk_non_layered_conjunction  in
                                        let uu____9478 =
                                          let uu____9483 =
                                            FStar_TypeChecker_Env.get_range
                                              env
                                             in
                                          fn env md u_res_t res_t g ct_then
                                            ct_else uu____9483
                                           in
                                        (match uu____9478 with
                                         | (c,g_conjunction) ->
                                             let uu____9494 =
                                               let uu____9495 =
                                                 let uu____9496 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_comp gthen
                                                    in
                                                 FStar_TypeChecker_Env.conj_guard
                                                   uu____9496 g_lift
                                                  in
                                               FStar_TypeChecker_Env.conj_guard
                                                 uu____9495 g_conjunction
                                                in
                                             ((FStar_Pervasives_Native.Some
                                                 md), c, uu____9494)))))
                     lcases
                     (FStar_Pervasives_Native.None, default_case,
                       FStar_TypeChecker_Env.trivial_guard)
                    in
                 match uu____9194 with
                 | (md,comp,g_comp) ->
                     (match lcases with
                      | [] -> (comp, g_comp)
                      | uu____9530::[] -> (comp, g_comp)
                      | uu____9573 ->
                          let uu____9590 =
                            let uu____9592 =
                              FStar_All.pipe_right md FStar_Util.must  in
                            FStar_All.pipe_right uu____9592
                              FStar_Syntax_Util.is_layered
                             in
                          if uu____9590
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
                             let uu____9605 = destruct_wp_comp comp1  in
                             match uu____9605 with
                             | (uu____9616,uu____9617,wp) ->
                                 let ite_wp =
                                   let uu____9620 =
                                     FStar_All.pipe_right md1
                                       FStar_Syntax_Util.get_wp_ite_combinator
                                      in
                                   FStar_All.pipe_right uu____9620
                                     FStar_Util.must
                                    in
                                 let wp1 =
                                   let uu____9630 =
                                     let uu____9635 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [u_res_t] env md1 ite_wp
                                        in
                                     let uu____9636 =
                                       let uu____9637 =
                                         FStar_Syntax_Syntax.as_arg res_t  in
                                       let uu____9646 =
                                         let uu____9657 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [uu____9657]  in
                                       uu____9637 :: uu____9646  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____9635
                                       uu____9636
                                      in
                                   uu____9630 FStar_Pervasives_Native.None
                                     wp.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____9690 =
                                   mk_comp md1 u_res_t res_t wp1
                                     bind_cases_flags
                                    in
                                 (uu____9690, g_comp))))
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
          let uu____9725 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____9725 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____9741 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____9747 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____9741 uu____9747
              else
                (let uu____9756 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____9762 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____9756 uu____9762)
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
          let uu____9787 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____9787
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____9790 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____9790
        then u_res
        else
          (let is_total =
             let uu____9797 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____9797
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____9808 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____9808 with
              | FStar_Pervasives_Native.None  ->
                  let uu____9811 =
                    let uu____9817 =
                      let uu____9819 = FStar_Syntax_Print.lid_to_string c_lid
                         in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____9819
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____9817)
                     in
                  FStar_Errors.raise_error uu____9811
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
      let uu____9843 = destruct_wp_comp ct  in
      match uu____9843 with
      | (u_t,t,wp) ->
          let vc =
            let uu____9862 = FStar_TypeChecker_Env.get_range env  in
            let uu____9863 =
              let uu____9868 =
                let uu____9869 =
                  let uu____9870 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_trivial_combinator
                     in
                  FStar_All.pipe_right uu____9870 FStar_Util.must  in
                FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                  uu____9869
                 in
              let uu____9877 =
                let uu____9878 = FStar_Syntax_Syntax.as_arg t  in
                let uu____9887 =
                  let uu____9898 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____9898]  in
                uu____9878 :: uu____9887  in
              FStar_Syntax_Syntax.mk_Tm_app uu____9868 uu____9877  in
            uu____9863 FStar_Pervasives_Native.None uu____9862  in
          let uu____9931 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____9931)
  
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
                  let uu____9986 = FStar_TypeChecker_Env.try_lookup_lid env f
                     in
                  match uu____9986 with
                  | FStar_Pervasives_Native.Some uu____10001 ->
                      ((let uu____10019 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____10019
                        then
                          let uu____10023 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____10023
                        else ());
                       (let coercion =
                          let uu____10029 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____10029
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____10036 =
                            let uu____10037 =
                              let uu____10038 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____10038
                               in
                            (FStar_Pervasives_Native.None, uu____10037)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____10036
                           in
                        let e1 =
                          let uu____10044 =
                            let uu____10049 =
                              let uu____10050 = FStar_Syntax_Syntax.as_arg e
                                 in
                              [uu____10050]  in
                            FStar_Syntax_Syntax.mk_Tm_app coercion2
                              uu____10049
                             in
                          uu____10044 FStar_Pervasives_Native.None
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____10084 =
                          let uu____10090 =
                            let uu____10092 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____10092
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____10090)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____10084);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____10111 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10129 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10140 -> false 
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
      let uu____10164 = FStar_Syntax_Util.head_and_args t2  in
      match uu____10164 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____10209 =
              let uu____10224 =
                let uu____10225 = FStar_Syntax_Subst.compress h1  in
                uu____10225.FStar_Syntax_Syntax.n  in
              (uu____10224, args)  in
            match uu____10209 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____10272,uu____10273) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____10306) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____10327,branches),uu____10329) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____10393 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____10394 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____10394 with
                               | (uu____10395,uu____10396,br_body) ->
                                   let uu____10414 =
                                     let uu____10415 =
                                       let uu____10420 =
                                         let uu____10421 =
                                           let uu____10424 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____10424
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____10421
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____10420  in
                                     FStar_All.pipe_right br_body uu____10415
                                      in
                                   (match uu____10414 with
                                    | No  -> No
                                    | uu____10435 -> Maybe))) No)
            | uu____10436 -> No  in
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
            (((let uu____10488 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____10488) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10507 =
                 let uu____10508 = FStar_Syntax_Subst.compress t1  in
                 uu____10508.FStar_Syntax_Syntax.n  in
               match uu____10507 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____10513 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10523 =
                 let uu____10524 = FStar_Syntax_Subst.compress t1  in
                 uu____10524.FStar_Syntax_Syntax.n  in
               match uu____10523 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____10529 -> false  in
             let is_type1 t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____10539 =
                 let uu____10540 = FStar_Syntax_Subst.compress t1  in
                 uu____10540.FStar_Syntax_Syntax.n  in
               match uu____10539 with
               | FStar_Syntax_Syntax.Tm_type uu____10544 -> true
               | uu____10546 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____10549 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____10549 with
             | (head1,args) ->
                 ((let uu____10599 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____10599
                   then
                     let uu____10603 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____10605 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____10607 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____10609 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____10603 uu____10605 uu____10607 uu____10609
                   else ());
                  (let mk_erased u t =
                     let uu____10627 =
                       let uu____10630 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____10630 [u]  in
                     let uu____10631 =
                       let uu____10642 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____10642]  in
                     FStar_Syntax_Util.mk_app uu____10627 uu____10631  in
                   let uu____10667 =
                     let uu____10682 =
                       let uu____10683 = FStar_Syntax_Util.un_uinst head1  in
                       uu____10683.FStar_Syntax_Syntax.n  in
                     (uu____10682, args)  in
                   match uu____10667 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type1 exp_t)
                       ->
                       let uu____10721 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____10721 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____10761 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10761 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10801 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10801 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____10841 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____10841 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____10862 ->
                       let uu____10877 =
                         let uu____10882 = check_erased env res_typ  in
                         let uu____10883 = check_erased env exp_t  in
                         (uu____10882, uu____10883)  in
                       (match uu____10877 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10892 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____10892 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____10903 =
                                   let uu____10908 =
                                     let uu____10909 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____10909]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____10908
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____10903 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____10944 =
                              let uu____10949 =
                                let uu____10950 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____10950]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____10949
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____10944 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____10983 ->
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
        let uu____11018 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____11018 with
        | (hd1,args) ->
            let uu____11067 =
              let uu____11082 =
                let uu____11083 = FStar_Syntax_Subst.compress hd1  in
                uu____11083.FStar_Syntax_Syntax.n  in
              (uu____11082, args)  in
            (match uu____11067 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____11121 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun _11148  -> FStar_Pervasives_Native.Some _11148)
                   uu____11121
             | uu____11149 -> FStar_Pervasives_Native.None)
  
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
          (let uu____11202 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____11202
           then
             let uu____11205 = FStar_Syntax_Print.term_to_string e  in
             let uu____11207 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____11209 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____11205 uu____11207 uu____11209
           else ());
          (let use_eq =
             env.FStar_TypeChecker_Env.use_eq ||
               (let uu____11219 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____11219 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____11244 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____11270 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____11270, false)
             else
               (let uu____11280 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____11280, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____11293) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____11305 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____11305
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1338_11321 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1338_11321.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1338_11321.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1338_11321.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard1) ->
               let uu____11328 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____11328 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____11344 =
                      let uu____11345 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____11345 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ1 c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____11365 =
                            let uu____11367 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____11367 = FStar_Syntax_Util.Equal  in
                          if uu____11365
                          then
                            ((let uu____11374 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____11374
                              then
                                let uu____11378 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____11380 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____11378 uu____11380
                              else ());
                             (let uu____11385 = set_result_typ1 c  in
                              (uu____11385, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____11392 ->
                                   true
                               | uu____11400 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____11409 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____11409
                                  in
                               let lc1 =
                                 let uu____11411 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____11412 =
                                   let uu____11413 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____11413)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____11411 uu____11412
                                  in
                               ((let uu____11417 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11417
                                 then
                                   let uu____11421 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____11423 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____11425 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____11427 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____11421 uu____11423 uu____11425
                                     uu____11427
                                 else ());
                                (let uu____11432 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____11432 with
                                 | (c1,g_lc) ->
                                     let uu____11443 = set_result_typ1 c1  in
                                     let uu____11444 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____11443, uu____11444)))
                             else
                               ((let uu____11448 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____11448
                                 then
                                   let uu____11452 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____11454 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____11452 uu____11454
                                 else ());
                                (let uu____11459 = set_result_typ1 c  in
                                 (uu____11459, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1375_11463 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1375_11463.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1375_11463.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1375_11463.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____11473 =
                      let uu____11474 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____11474
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____11484 =
                           let uu____11485 = FStar_Syntax_Subst.compress f1
                              in
                           uu____11485.FStar_Syntax_Syntax.n  in
                         match uu____11484 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____11492,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____11494;
                                            FStar_Syntax_Syntax.vars =
                                              uu____11495;_},uu____11496)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1391_11522 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1391_11522.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1391_11522.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1391_11522.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____11523 ->
                             let uu____11524 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____11524 with
                              | (c,g_c) ->
                                  ((let uu____11536 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____11536
                                    then
                                      let uu____11540 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____11542 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____11544 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____11546 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____11540 uu____11542 uu____11544
                                        uu____11546
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
                                        let uu____11559 =
                                          let uu____11564 =
                                            let uu____11565 =
                                              FStar_Syntax_Syntax.as_arg xexp
                                               in
                                            [uu____11565]  in
                                          FStar_Syntax_Syntax.mk_Tm_app f1
                                            uu____11564
                                           in
                                        uu____11559
                                          FStar_Pervasives_Native.None
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____11592 =
                                      let uu____11597 =
                                        FStar_All.pipe_left
                                          (fun _11618  ->
                                             FStar_Pervasives_Native.Some
                                               _11618)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____11619 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____11620 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____11621 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____11597
                                        uu____11619 e uu____11620 uu____11621
                                       in
                                    match uu____11592 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1409_11629 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1409_11629.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1409_11629.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____11631 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____11631
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____11634 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____11634 with
                                         | (c2,g_lc) ->
                                             ((let uu____11646 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____11646
                                               then
                                                 let uu____11650 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____11650
                                               else ());
                                              (let uu____11655 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____11655))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_11664  ->
                              match uu___6_11664 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____11667 -> []))
                       in
                    let lc1 =
                      let uu____11669 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____11669 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1425_11671 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1425_11671.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1425_11671.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1425_11671.FStar_TypeChecker_Common.implicits)
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
        let uu____11707 =
          let uu____11710 =
            let uu____11715 =
              let uu____11716 =
                let uu____11725 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____11725  in
              [uu____11716]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____11715  in
          uu____11710 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____11707  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____11748 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____11748
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____11767 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____11783 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____11800 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____11800
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____11816)::(ens,uu____11818)::uu____11819 ->
                    let uu____11862 =
                      let uu____11865 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____11865  in
                    let uu____11866 =
                      let uu____11867 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____11867  in
                    (uu____11862, uu____11866)
                | uu____11870 ->
                    let uu____11881 =
                      let uu____11887 =
                        let uu____11889 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____11889
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____11887)
                       in
                    FStar_Errors.raise_error uu____11881
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____11909)::uu____11910 ->
                    let uu____11937 =
                      let uu____11942 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____11942
                       in
                    (match uu____11937 with
                     | (us_r,uu____11974) ->
                         let uu____11975 =
                           let uu____11980 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____11980
                            in
                         (match uu____11975 with
                          | (us_e,uu____12012) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____12015 =
                                  let uu____12016 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12016
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12015
                                  us_r
                                 in
                              let as_ens =
                                let uu____12018 =
                                  let uu____12019 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____12019
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____12018
                                  us_e
                                 in
                              let req =
                                let uu____12023 =
                                  let uu____12028 =
                                    let uu____12029 =
                                      let uu____12040 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12040]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12029
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____12028
                                   in
                                uu____12023 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____12080 =
                                  let uu____12085 =
                                    let uu____12086 =
                                      let uu____12097 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____12097]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____12086
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____12085
                                   in
                                uu____12080 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____12134 =
                                let uu____12137 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____12137  in
                              let uu____12138 =
                                let uu____12139 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____12139  in
                              (uu____12134, uu____12138)))
                | uu____12142 -> failwith "Impossible"))
  
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
        (let uu____12181 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____12181
         then
           let uu____12186 = FStar_Syntax_Print.term_to_string tm  in
           let uu____12188 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____12186
             uu____12188
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
          (let uu____12247 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____12247
           then
             let uu____12252 = FStar_Syntax_Print.term_to_string tm  in
             let uu____12254 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____12252
               uu____12254
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____12265 =
      let uu____12267 =
        let uu____12268 = FStar_Syntax_Subst.compress t  in
        uu____12268.FStar_Syntax_Syntax.n  in
      match uu____12267 with
      | FStar_Syntax_Syntax.Tm_app uu____12272 -> false
      | uu____12290 -> true  in
    if uu____12265
    then t
    else
      (let uu____12295 = FStar_Syntax_Util.head_and_args t  in
       match uu____12295 with
       | (head1,args) ->
           let uu____12338 =
             let uu____12340 =
               let uu____12341 = FStar_Syntax_Subst.compress head1  in
               uu____12341.FStar_Syntax_Syntax.n  in
             match uu____12340 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____12346 -> false  in
           if uu____12338
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____12378 ->
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
          ((let uu____12425 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____12425
            then
              let uu____12428 = FStar_Syntax_Print.term_to_string e  in
              let uu____12430 = FStar_Syntax_Print.term_to_string t  in
              let uu____12432 =
                let uu____12434 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____12434
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____12428 uu____12430 uu____12432
            else ());
           (let number_of_implicits t1 =
              let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
              let uu____12447 = FStar_Syntax_Util.arrow_formals t2  in
              match uu____12447 with
              | (formals,uu____12463) ->
                  let n_implicits =
                    let uu____12485 =
                      FStar_All.pipe_right formals
                        (FStar_Util.prefix_until
                           (fun uu____12563  ->
                              match uu____12563 with
                              | (uu____12571,imp) ->
                                  (FStar_Option.isNone imp) ||
                                    (let uu____12578 =
                                       FStar_Syntax_Util.eq_aqual imp
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.Equality)
                                        in
                                     uu____12578 = FStar_Syntax_Util.Equal)))
                       in
                    match uu____12485 with
                    | FStar_Pervasives_Native.None  ->
                        FStar_List.length formals
                    | FStar_Pervasives_Native.Some
                        (implicits,_first_explicit,_rest) ->
                        FStar_List.length implicits
                     in
                  n_implicits
               in
            let inst_n_binders t1 =
              let uu____12703 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____12703 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____12717 =
                      let uu____12723 =
                        let uu____12725 = FStar_Util.string_of_int n_expected
                           in
                        let uu____12727 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____12729 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____12725 uu____12727 uu____12729
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____12723)
                       in
                    let uu____12733 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____12717 uu____12733
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_12751 =
              match uu___7_12751 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____12794 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____12794 with
                 | (bs1,c1) ->
                     let rec aux subst1 inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some _12925,uu____12912)
                           when _12925 = Prims.int_zero ->
                           ([], bs2, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____12958,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____12960))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____12994 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____12994 with
                            | (v1,uu____13035,g) ->
                                ((let uu____13050 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13050
                                  then
                                    let uu____13053 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____13053
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13063 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13063 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13156 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13156))))
                       | (uu____13183,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst1
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____13220 =
                             let uu____13233 =
                               let uu____13240 =
                                 let uu____13245 = FStar_Dyn.mkdyn env  in
                                 (uu____13245, tau)  in
                               FStar_Pervasives_Native.Some uu____13240  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____13233
                              in
                           (match uu____13220 with
                            | (v1,uu____13278,g) ->
                                ((let uu____13293 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____13293
                                  then
                                    let uu____13296 =
                                      FStar_Syntax_Print.term_to_string v1
                                       in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____13296
                                  else ());
                                 (let subst2 =
                                    (FStar_Syntax_Syntax.NT (x, v1)) ::
                                    subst1  in
                                  let uu____13306 =
                                    aux subst2 (decr_inst inst_n) rest  in
                                  match uu____13306 with
                                  | (args,bs3,subst3,g') ->
                                      let uu____13399 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v1,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst3, uu____13399))))
                       | (uu____13426,bs3) ->
                           ([], bs3, subst1,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____13474 =
                       let uu____13501 = inst_n_binders t1  in
                       aux [] uu____13501 bs1  in
                     (match uu____13474 with
                      | (args,bs2,subst1,guard) ->
                          (match (args, bs2) with
                           | ([],uu____13573) -> (e, torig, guard)
                           | (uu____13604,[]) when
                               let uu____13635 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____13635 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____13637 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____13665 ->
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
            | uu____13678 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____13690 =
      let uu____13694 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____13694
        (FStar_List.map
           (fun u  ->
              let uu____13706 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____13706 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____13690 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____13734 = FStar_Util.set_is_empty x  in
      if uu____13734
      then []
      else
        (let s =
           let uu____13752 =
             let uu____13755 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____13755  in
           FStar_All.pipe_right uu____13752 FStar_Util.set_elements  in
         (let uu____13771 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____13771
          then
            let uu____13776 =
              let uu____13778 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____13778  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____13776
          else ());
         (let r =
            let uu____13787 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____13787  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____13826 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____13826
                     then
                       let uu____13831 =
                         let uu____13833 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____13833
                          in
                       let uu____13837 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____13839 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____13831 uu____13837 uu____13839
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
        let uu____13869 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____13869 FStar_Util.set_elements  in
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
        | ([],uu____13908) -> generalized_univ_names
        | (uu____13915,[]) -> explicit_univ_names
        | uu____13922 ->
            let uu____13931 =
              let uu____13937 =
                let uu____13939 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____13939
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____13937)
               in
            FStar_Errors.raise_error uu____13931 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____13961 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____13961
       then
         let uu____13966 = FStar_Syntax_Print.term_to_string t  in
         let uu____13968 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____13966 uu____13968
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____13977 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____13977
        then
          let uu____13982 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____13982
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____13991 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____13991
         then
           let uu____13996 = FStar_Syntax_Print.term_to_string t  in
           let uu____13998 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____13996 uu____13998
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
        let uu____14082 =
          let uu____14084 =
            FStar_Util.for_all
              (fun uu____14098  ->
                 match uu____14098 with
                 | (uu____14108,uu____14109,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____14084  in
        if uu____14082
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____14161 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____14161
              then
                let uu____14164 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____14164
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____14171 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____14171
               then
                 let uu____14174 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____14174
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____14192 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____14192 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____14226 =
             match uu____14226 with
             | (lbname,e,c) ->
                 let c1 = norm1 c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____14263 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____14263
                   then
                     let uu____14268 =
                       let uu____14270 =
                         let uu____14274 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____14274
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____14270
                         (FStar_String.concat ", ")
                        in
                     let uu____14322 =
                       let uu____14324 =
                         let uu____14328 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____14328
                           (FStar_List.map
                              (fun u  ->
                                 let uu____14341 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____14343 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____14341
                                   uu____14343))
                          in
                       FStar_All.pipe_right uu____14324
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____14268
                       uu____14322
                   else ());
                  (let univs2 =
                     let uu____14357 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____14369 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____14369) univs1
                       uu____14357
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____14376 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____14376
                    then
                      let uu____14381 =
                        let uu____14383 =
                          let uu____14387 = FStar_Util.set_elements univs2
                             in
                          FStar_All.pipe_right uu____14387
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____14383
                          (FStar_String.concat ", ")
                         in
                      let uu____14435 =
                        let uu____14437 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____14451 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____14453 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____14451
                                    uu____14453))
                           in
                        FStar_All.pipe_right uu____14437
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____14381 uu____14435
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____14474 =
             let uu____14491 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____14491  in
           match uu____14474 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____14581 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____14581
                 then ()
                 else
                   (let uu____14586 = lec_hd  in
                    match uu____14586 with
                    | (lb1,uu____14594,uu____14595) ->
                        let uu____14596 = lec2  in
                        (match uu____14596 with
                         | (lb2,uu____14604,uu____14605) ->
                             let msg =
                               let uu____14608 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14610 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____14608 uu____14610
                                in
                             let uu____14613 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____14613))
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
                 let uu____14681 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____14681
                 then ()
                 else
                   (let uu____14686 = lec_hd  in
                    match uu____14686 with
                    | (lb1,uu____14694,uu____14695) ->
                        let uu____14696 = lec2  in
                        (match uu____14696 with
                         | (lb2,uu____14704,uu____14705) ->
                             let msg =
                               let uu____14708 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____14710 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____14708 uu____14710
                                in
                             let uu____14713 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____14713))
                  in
               let lecs1 =
                 let uu____14724 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____14777 = univs_and_uvars_of_lec this_lec  in
                        match uu____14777 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____14724 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____14882 = lec_hd  in
                   match uu____14882 with
                   | (lbname,e,c) ->
                       let uu____14892 =
                         let uu____14898 =
                           let uu____14900 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____14902 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____14904 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____14900 uu____14902 uu____14904
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____14898)
                          in
                       let uu____14908 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____14892 uu____14908
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____14927 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____14927 with
                         | FStar_Pervasives_Native.Some uu____14936 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____14944 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____14948 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____14948 with
                              | (bs,kres) ->
                                  ((let uu____14992 =
                                      let uu____14993 =
                                        let uu____14996 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____14996
                                         in
                                      uu____14993.FStar_Syntax_Syntax.n  in
                                    match uu____14992 with
                                    | FStar_Syntax_Syntax.Tm_type uu____14997
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____15001 =
                                          let uu____15003 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____15003  in
                                        if uu____15001
                                        then fail1 kres
                                        else ()
                                    | uu____15008 -> fail1 kres);
                                   (let a =
                                      let uu____15010 =
                                        let uu____15013 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _15016  ->
                                             FStar_Pervasives_Native.Some
                                               _15016) uu____15013
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____15010
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____15024 ->
                                          let uu____15033 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____15033
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
                      (fun uu____15136  ->
                         match uu____15136 with
                         | (lbname,e,c) ->
                             let uu____15182 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____15243 ->
                                   let uu____15256 = (e, c)  in
                                   (match uu____15256 with
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
                                                (fun uu____15296  ->
                                                   match uu____15296 with
                                                   | (x,uu____15302) ->
                                                       let uu____15303 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____15303)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____15321 =
                                                let uu____15323 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____15323
                                                 in
                                              if uu____15321
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
                                          let uu____15332 =
                                            let uu____15333 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____15333.FStar_Syntax_Syntax.n
                                             in
                                          match uu____15332 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____15358 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____15358 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____15369 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____15373 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____15373, gen_tvars))
                                in
                             (match uu____15182 with
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
        (let uu____15520 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____15520
         then
           let uu____15523 =
             let uu____15525 =
               FStar_List.map
                 (fun uu____15540  ->
                    match uu____15540 with
                    | (lb,uu____15549,uu____15550) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____15525 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____15523
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____15576  ->
                match uu____15576 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____15605 = gen env is_rec lecs  in
           match uu____15605 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____15704  ->
                       match uu____15704 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____15766 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____15766
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____15814  ->
                           match uu____15814 with
                           | (l,us,e,c,gvs) ->
                               let uu____15848 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____15850 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____15852 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____15854 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____15856 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____15848 uu____15850 uu____15852
                                 uu____15854 uu____15856))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____15901  ->
                match uu____15901 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____15945 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____15945, t, c, gvs)) univnames_lecs
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
        let uu____16000 =
          let uu____16004 =
            let uu____16006 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____16006  in
          FStar_Pervasives_Native.Some uu____16004  in
        FStar_Profiling.profile
          (fun uu____16023  -> generalize' env is_rec lecs) uu____16000
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
              (let uu____16083 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                  in
               match uu____16083 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____16089 = FStar_TypeChecker_Env.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _16092  -> FStar_Pervasives_Native.Some _16092)
                     uu____16089)
             in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___1882_16112 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___1882_16112.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___1882_16112.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____16113 -> e2  in
          let uu____16114 = maybe_coerce_lc env1 e lc t2  in
          match uu____16114 with
          | (e1,lc1,g_c) ->
              let uu____16130 =
                check1 env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____16130 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16139 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____16145 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____16139 uu____16145
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____16154 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____16154
                     then
                       let uu____16159 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____16159
                     else ());
                    (let uu____16165 = decorate e1 t2  in
                     let uu____16166 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (uu____16165, lc1, uu____16166))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____16194 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____16194
         then
           let uu____16197 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____16197
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____16211 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____16211 with
         | (c,g_c) ->
             let uu____16223 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____16223
             then
               let uu____16231 =
                 let uu____16233 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____16233  in
               (uu____16231, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____16241 =
                    let uu____16242 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____16242
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____16241
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____16243 = check_trivial_precondition env c1  in
                match uu____16243 with
                | (ct,vc,g_pre) ->
                    ((let uu____16259 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____16259
                      then
                        let uu____16264 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____16264
                      else ());
                     (let uu____16269 =
                        let uu____16271 =
                          let uu____16272 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____16272  in
                        discharge uu____16271  in
                      let uu____16273 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____16269, uu____16273)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___8_16307 =
        match uu___8_16307 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____16317)::[] -> f fst1
        | uu____16342 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____16354 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____16354
          (fun _16355  -> FStar_TypeChecker_Common.NonTrivial _16355)
         in
      let op_or_e e =
        let uu____16366 =
          let uu____16367 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____16367  in
        FStar_All.pipe_right uu____16366
          (fun _16370  -> FStar_TypeChecker_Common.NonTrivial _16370)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _16377  -> FStar_TypeChecker_Common.NonTrivial _16377)
         in
      let op_or_t t =
        let uu____16388 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____16388
          (fun _16391  -> FStar_TypeChecker_Common.NonTrivial _16391)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _16398  -> FStar_TypeChecker_Common.NonTrivial _16398)
         in
      let short_op_ite uu___9_16404 =
        match uu___9_16404 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____16414)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____16441)::[] ->
            let uu____16482 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____16482
              (fun _16483  -> FStar_TypeChecker_Common.NonTrivial _16483)
        | uu____16484 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____16496 =
          let uu____16504 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____16504)  in
        let uu____16512 =
          let uu____16522 =
            let uu____16530 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____16530)  in
          let uu____16538 =
            let uu____16548 =
              let uu____16556 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____16556)  in
            let uu____16564 =
              let uu____16574 =
                let uu____16582 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____16582)  in
              let uu____16590 =
                let uu____16600 =
                  let uu____16608 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____16608)  in
                [uu____16600; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____16574 :: uu____16590  in
            uu____16548 :: uu____16564  in
          uu____16522 :: uu____16538  in
        uu____16496 :: uu____16512  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____16670 =
            FStar_Util.find_map table
              (fun uu____16685  ->
                 match uu____16685 with
                 | (x,mk1) ->
                     let uu____16702 = FStar_Ident.lid_equals x lid  in
                     if uu____16702
                     then
                       let uu____16707 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____16707
                     else FStar_Pervasives_Native.None)
             in
          (match uu____16670 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____16711 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____16719 =
      let uu____16720 = FStar_Syntax_Util.un_uinst l  in
      uu____16720.FStar_Syntax_Syntax.n  in
    match uu____16719 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____16725 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____16761)::uu____16762 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____16781 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____16790,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____16791))::uu____16792 -> bs
      | uu____16810 ->
          let uu____16811 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____16811 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____16815 =
                 let uu____16816 = FStar_Syntax_Subst.compress t  in
                 uu____16816.FStar_Syntax_Syntax.n  in
               (match uu____16815 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____16820) ->
                    let uu____16841 =
                      FStar_Util.prefix_until
                        (fun uu___10_16881  ->
                           match uu___10_16881 with
                           | (uu____16889,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____16890)) ->
                               false
                           | uu____16895 -> true) bs'
                       in
                    (match uu____16841 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____16931,uu____16932) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____17004,uu____17005) ->
                         let uu____17078 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____17098  ->
                                   match uu____17098 with
                                   | (x,uu____17107) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____17078
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____17156  ->
                                     match uu____17156 with
                                     | (x,i) ->
                                         let uu____17175 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____17175, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____17186 -> bs))
  
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
            let uu____17215 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____17215
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
          let uu____17246 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____17246
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
        (let uu____17289 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____17289
         then
           ((let uu____17294 = FStar_Ident.text_of_lid lident  in
             d uu____17294);
            (let uu____17296 = FStar_Ident.text_of_lid lident  in
             let uu____17298 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____17296 uu____17298))
         else ());
        (let fv =
           let uu____17304 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____17304
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
         let uu____17316 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___2043_17318 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2043_17318.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2043_17318.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2043_17318.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2043_17318.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2043_17318.FStar_Syntax_Syntax.sigopts)
           }), uu____17316))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_17336 =
        match uu___11_17336 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17339 -> false  in
      let reducibility uu___12_17347 =
        match uu___12_17347 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____17354 -> false  in
      let assumption uu___13_17362 =
        match uu___13_17362 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____17366 -> false  in
      let reification uu___14_17374 =
        match uu___14_17374 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____17377 -> true
        | uu____17379 -> false  in
      let inferred uu___15_17387 =
        match uu___15_17387 with
        | FStar_Syntax_Syntax.Discriminator uu____17389 -> true
        | FStar_Syntax_Syntax.Projector uu____17391 -> true
        | FStar_Syntax_Syntax.RecordType uu____17397 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____17407 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____17420 -> false  in
      let has_eq uu___16_17428 =
        match uu___16_17428 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____17432 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____17511 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____17518 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____17551 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____17551))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____17582 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____17582
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
           | FStar_Syntax_Syntax.Sig_bundle uu____17602 ->
               let uu____17611 =
                 let uu____17613 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_17619  ->
                           match uu___17_17619 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____17622 -> false))
                    in
                 Prims.op_Negation uu____17613  in
               if uu____17611
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____17629 -> ()
           | uu____17636 ->
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
      let uu____17650 =
        let uu____17652 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_17658  ->
                  match uu___18_17658 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____17661 -> false))
           in
        FStar_All.pipe_right uu____17652 Prims.op_Negation  in
      if uu____17650
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____17682 =
            let uu____17688 =
              let uu____17690 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____17690 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____17688)  in
          FStar_Errors.raise_error uu____17682 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____17708 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____17716 =
            let uu____17718 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____17718  in
          if uu____17716 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____17729),uu____17730) ->
              ((let uu____17742 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____17742
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____17751 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____17751
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____17762 ->
              ((let uu____17772 =
                  let uu____17774 =
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
                  Prims.op_Negation uu____17774  in
                if uu____17772 then err'1 () else ());
               (let uu____17784 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_17790  ->
                           match uu___19_17790 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____17793 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____17784
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____17799 ->
              let uu____17806 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____17806 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____17814 ->
              let uu____17821 =
                let uu____17823 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____17823  in
              if uu____17821 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17833 ->
              let uu____17834 =
                let uu____17836 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____17836  in
              if uu____17834 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17846 ->
              let uu____17859 =
                let uu____17861 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____17861  in
              if uu____17859 then err'1 () else ()
          | uu____17871 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____17910 =
          let uu____17911 = FStar_Syntax_Subst.compress t1  in
          uu____17911.FStar_Syntax_Syntax.n  in
        match uu____17910 with
        | FStar_Syntax_Syntax.Tm_arrow uu____17915 ->
            let uu____17930 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____17930 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____17963;
               FStar_Syntax_Syntax.index = uu____17964;
               FStar_Syntax_Syntax.sort = t2;_},uu____17966)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____17975) -> descend env head1
        | FStar_Syntax_Syntax.Tm_uinst (head1,uu____18001) ->
            descend env head1
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____18007 -> false
      
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
        (let uu____18017 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____18017
         then
           let uu____18022 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____18022
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
                  let uu____18087 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____18087 r  in
                let uu____18097 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____18097 with
                | (uu____18106,signature) ->
                    let uu____18108 =
                      let uu____18109 = FStar_Syntax_Subst.compress signature
                         in
                      uu____18109.FStar_Syntax_Syntax.n  in
                    (match uu____18108 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18117) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____18165 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____18180 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____18182 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____18180 eff_name.FStar_Ident.str
                                       uu____18182) r
                                 in
                              (match uu____18165 with
                               | (is,g) ->
                                   let uu____18195 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____18197 =
                                             let uu____18198 =
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
                                                 = uu____18198;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____18197
                                            in
                                         let uu____18217 =
                                           let uu____18224 =
                                             let uu____18225 =
                                               let uu____18240 =
                                                 let uu____18249 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     FStar_Syntax_Syntax.t_unit
                                                    in
                                                 [uu____18249]  in
                                               (uu____18240, eff_c)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____18225
                                              in
                                           FStar_Syntax_Syntax.mk uu____18224
                                            in
                                         uu____18217
                                           FStar_Pervasives_Native.None r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____18280 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____18280
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____18289 =
                                           let uu____18294 =
                                             FStar_List.map
                                               FStar_Syntax_Syntax.as_arg
                                               (a_tm :: is)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____18294
                                            in
                                         uu____18289
                                           FStar_Pervasives_Native.None r
                                      in
                                   (uu____18195, g))
                          | uu____18303 -> fail1 signature)
                     | uu____18304 -> fail1 signature)
  
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
            let uu____18335 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____18335
              (fun ed  ->
                 let uu____18343 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____18343 u a_tm)
  
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
              let uu____18379 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____18379 with
              | (uu____18384,sig_tm) ->
                  let fail1 t =
                    let uu____18392 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____18392 r  in
                  let uu____18398 =
                    let uu____18399 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____18399.FStar_Syntax_Syntax.n  in
                  (match uu____18398 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____18403) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____18426)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____18448 -> fail1 sig_tm)
                   | uu____18449 -> fail1 sig_tm)
  
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
          (let uu____18480 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____18480
           then
             let uu____18485 = FStar_Syntax_Print.comp_to_string c  in
             let uu____18487 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____18485 uu____18487
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____18494 =
             let uu____18505 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____18506 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____18505, (ct.FStar_Syntax_Syntax.result_typ), uu____18506)
              in
           match uu____18494 with
           | (u,a,c_is) ->
               let uu____18554 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____18554 with
                | (uu____18563,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____18574 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____18576 = FStar_Ident.string_of_lid tgt  in
                      let uu____18578 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____18574 uu____18576 s uu____18578
                       in
                    let uu____18581 =
                      let uu____18614 =
                        let uu____18615 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____18615.FStar_Syntax_Syntax.n  in
                      match uu____18614 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____18679 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____18679 with
                           | (a_b::bs1,c2) ->
                               let uu____18739 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               let uu____18801 =
                                 FStar_Syntax_Util.comp_to_comp_typ c2  in
                               (a_b, uu____18739, uu____18801))
                      | uu____18828 ->
                          let uu____18829 =
                            let uu____18835 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____18835)
                             in
                          FStar_Errors.raise_error uu____18829 r
                       in
                    (match uu____18581 with
                     | (a_b,(rest_bs,f_b::[]),lift_ct) ->
                         let uu____18953 =
                           let uu____18960 =
                             let uu____18961 =
                               let uu____18962 =
                                 let uu____18969 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____18969, a)  in
                               FStar_Syntax_Syntax.NT uu____18962  in
                             [uu____18961]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____18960
                             (fun b  ->
                                let uu____18986 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____18988 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____18990 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____18992 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____18986 uu____18988 uu____18990
                                  uu____18992) r
                            in
                         (match uu____18953 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____19006 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____19006
                                then
                                  let uu____19011 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____19020 =
                                             let uu____19022 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____19022
                                              in
                                           Prims.op_Hat s uu____19020) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____19011
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____19053 =
                                           let uu____19060 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____19060, t)  in
                                         FStar_Syntax_Syntax.NT uu____19053)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____19079 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____19079
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____19085 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____19085
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____19094 =
                                             FStar_TypeChecker_Rel.teq env i1
                                               i2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____19094)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let is =
                                  let uu____19098 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____19098 r
                                   in
                                let c1 =
                                  let uu____19101 =
                                    let uu____19102 =
                                      let uu____19113 =
                                        FStar_All.pipe_right is
                                          (FStar_List.map
                                             (FStar_Syntax_Subst.subst substs))
                                         in
                                      FStar_All.pipe_right uu____19113
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.as_arg)
                                       in
                                    {
                                      FStar_Syntax_Syntax.comp_univs =
                                        (lift_ct.FStar_Syntax_Syntax.comp_univs);
                                      FStar_Syntax_Syntax.effect_name = tgt;
                                      FStar_Syntax_Syntax.result_typ = a;
                                      FStar_Syntax_Syntax.effect_args =
                                        uu____19102;
                                      FStar_Syntax_Syntax.flags = []
                                    }  in
                                  FStar_Syntax_Syntax.mk_Comp uu____19101  in
                                (let uu____19133 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____19133
                                 then
                                   let uu____19138 =
                                     FStar_Syntax_Print.comp_to_string c1  in
                                   FStar_Util.print1 "} Lifted comp: %s\n"
                                     uu____19138
                                 else ());
                                (let uu____19143 =
                                   FStar_TypeChecker_Env.conj_guard g guard_f
                                    in
                                 (c1, uu____19143))))))))
  
let lift_tf_layered_effect_term :
  'Auu____19157 .
    'Auu____19157 ->
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
              let uu____19186 =
                let uu____19191 =
                  FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____19191
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____19186 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____19234 =
                let uu____19235 =
                  let uu____19238 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____19238
                    FStar_Syntax_Subst.compress
                   in
                uu____19235.FStar_Syntax_Syntax.n  in
              match uu____19234 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____19261::bs,uu____19263)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____19303 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____19303
                    FStar_Pervasives_Native.fst
              | uu____19409 ->
                  let uu____19410 =
                    let uu____19416 =
                      let uu____19418 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____19418
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____19416)  in
                  FStar_Errors.raise_error uu____19410
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____19445 = FStar_Syntax_Syntax.as_arg a  in
              let uu____19454 =
                let uu____19465 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____19501  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____19508 =
                  let uu____19519 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____19519]  in
                FStar_List.append uu____19465 uu____19508  in
              uu____19445 :: uu____19454  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index1  ->
        let uu____19590 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____19590 with
        | (uu____19595,t) ->
            let err n1 =
              let uu____19605 =
                let uu____19611 =
                  let uu____19613 = FStar_Ident.string_of_lid datacon  in
                  let uu____19615 = FStar_Util.string_of_int n1  in
                  let uu____19617 = FStar_Util.string_of_int index1  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____19613 uu____19615 uu____19617
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____19611)
                 in
              let uu____19621 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____19605 uu____19621  in
            let uu____19622 =
              let uu____19623 = FStar_Syntax_Subst.compress t  in
              uu____19623.FStar_Syntax_Syntax.n  in
            (match uu____19622 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19627) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____19682  ->
                           match uu____19682 with
                           | (uu____19690,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____19699 -> true)))
                    in
                 if (FStar_List.length bs1) <= index1
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index1  in
                    let uu____19731 =
                      FStar_Syntax_Util.mk_field_projector_name datacon
                        (FStar_Pervasives_Native.fst b) index1
                       in
                    FStar_All.pipe_right uu____19731
                      FStar_Pervasives_Native.fst)
             | uu____19742 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub1  ->
      let uu____19755 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub1.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub1.FStar_Syntax_Syntax.target)
         in
      if uu____19755
      then
        let uu____19758 =
          let uu____19771 =
            FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub1.FStar_Syntax_Syntax.target uu____19771
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____19758;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub1))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____19806 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____19806 with
           | (uu____19815,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____19834 =
                 let uu____19835 =
                   let uu___2410_19836 = ct  in
                   let uu____19837 =
                     let uu____19848 =
                       let uu____19857 =
                         let uu____19858 =
                           let uu____19865 =
                             let uu____19866 =
                               let uu____19883 =
                                 let uu____19894 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 [uu____19894; wp]  in
                               (lift_t, uu____19883)  in
                             FStar_Syntax_Syntax.Tm_app uu____19866  in
                           FStar_Syntax_Syntax.mk uu____19865  in
                         uu____19858 FStar_Pervasives_Native.None
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____19857
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____19848]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2410_19836.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub1.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2410_19836.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____19837;
                     FStar_Syntax_Syntax.flags =
                       (uu___2410_19836.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____19835  in
               (uu____19834, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____19994 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____19994 with
           | (uu____20001,lift_t) ->
               let uu____20003 =
                 let uu____20010 =
                   let uu____20011 =
                     let uu____20028 =
                       let uu____20039 = FStar_Syntax_Syntax.as_arg r  in
                       let uu____20048 =
                         let uu____20059 =
                           FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                            in
                         let uu____20068 =
                           let uu____20079 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____20079]  in
                         uu____20059 :: uu____20068  in
                       uu____20039 :: uu____20048  in
                     (lift_t, uu____20028)  in
                   FStar_Syntax_Syntax.Tm_app uu____20011  in
                 FStar_Syntax_Syntax.mk uu____20010  in
               uu____20003 FStar_Pervasives_Native.None
                 e.FStar_Syntax_Syntax.pos
            in
         let uu____20132 =
           let uu____20145 =
             FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____20145 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____20132;
           FStar_TypeChecker_Env.mlift_term =
             (match sub1.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____20181  ->
                        fun uu____20182  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub1  ->
      let uu____20205 = get_mlift_for_subeff env sub1  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub1.FStar_Syntax_Syntax.source sub1.FStar_Syntax_Syntax.target
        uu____20205
  
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
  