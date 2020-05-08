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
    let mk f = FStar_Syntax_Syntax.mk f pat.FStar_Syntax_Syntax.p  in
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
                let uu____1372 =
                  FStar_TypeChecker_Env.inst_effect_fun_with [u_a] env ed
                    ret_wp
                   in
                let uu____1373 =
                  let uu____1374 = FStar_Syntax_Syntax.as_arg a  in
                  let uu____1383 =
                    let uu____1394 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____1394]  in
                  uu____1374 :: uu____1383  in
                FStar_Syntax_Syntax.mk_Tm_app uu____1372 uu____1373 r  in
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
              (let uu____1467 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____1467
               then
                 let uu____1472 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____1474 = FStar_Syntax_Print.univ_to_string u_a  in
                 let uu____1476 = FStar_Syntax_Print.term_to_string a  in
                 let uu____1478 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print4
                   "Computing %s.return for u_a:%s, a:%s, and e:%s{\n"
                   uu____1472 uu____1474 uu____1476 uu____1478
               else ());
              (let uu____1483 =
                 let uu____1488 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_return_vc_combinator
                    in
                 FStar_TypeChecker_Env.inst_tscheme_with uu____1488 [u_a]  in
               match uu____1483 with
               | (uu____1493,return_t) ->
                   let return_t_shape_error s =
                     let uu____1508 =
                       let uu____1510 =
                         FStar_Ident.string_of_lid
                           ed.FStar_Syntax_Syntax.mname
                          in
                       let uu____1512 =
                         FStar_Syntax_Print.term_to_string return_t  in
                       FStar_Util.format3
                         "%s.return %s does not have proper shape (reason:%s)"
                         uu____1510 uu____1512 s
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____1508)  in
                   let uu____1516 =
                     let uu____1545 =
                       let uu____1546 = FStar_Syntax_Subst.compress return_t
                          in
                       uu____1546.FStar_Syntax_Syntax.n  in
                     match uu____1545 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                         (FStar_List.length bs) >= (Prims.of_int (2)) ->
                         let uu____1606 = FStar_Syntax_Subst.open_comp bs c
                            in
                         (match uu____1606 with
                          | (a_b::x_b::bs1,c1) ->
                              let uu____1675 =
                                FStar_Syntax_Util.comp_to_comp_typ c1  in
                              (a_b, x_b, bs1, uu____1675))
                     | uu____1696 ->
                         let uu____1697 =
                           return_t_shape_error
                             "Either not an arrow or not enough binders"
                            in
                         FStar_Errors.raise_error uu____1697 r
                      in
                   (match uu____1516 with
                    | (a_b,x_b,rest_bs,return_ct) ->
                        let uu____1780 =
                          let uu____1787 =
                            let uu____1788 =
                              let uu____1789 =
                                let uu____1796 =
                                  FStar_All.pipe_right a_b
                                    FStar_Pervasives_Native.fst
                                   in
                                (uu____1796, a)  in
                              FStar_Syntax_Syntax.NT uu____1789  in
                            let uu____1807 =
                              let uu____1810 =
                                let uu____1811 =
                                  let uu____1818 =
                                    FStar_All.pipe_right x_b
                                      FStar_Pervasives_Native.fst
                                     in
                                  (uu____1818, e)  in
                                FStar_Syntax_Syntax.NT uu____1811  in
                              [uu____1810]  in
                            uu____1788 :: uu____1807  in
                          FStar_TypeChecker_Env.uvars_for_binders env rest_bs
                            uu____1787
                            (fun b  ->
                               let uu____1834 =
                                 FStar_Syntax_Print.binder_to_string b  in
                               let uu____1836 =
                                 let uu____1838 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Util.format1 "%s.return" uu____1838
                                  in
                               let uu____1841 = FStar_Range.string_of_range r
                                  in
                               FStar_Util.format3
                                 "implicit var for binder %s of %s at %s"
                                 uu____1834 uu____1836 uu____1841) r
                           in
                        (match uu____1780 with
                         | (rest_bs_uvars,g_uvars) ->
                             let subst =
                               FStar_List.map2
                                 (fun b  ->
                                    fun t  ->
                                      let uu____1878 =
                                        let uu____1885 =
                                          FStar_All.pipe_right b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____1885, t)  in
                                      FStar_Syntax_Syntax.NT uu____1878) (a_b
                                 :: x_b :: rest_bs) (a :: e :: rest_bs_uvars)
                                in
                             let is =
                               let uu____1911 =
                                 let uu____1914 =
                                   FStar_Syntax_Subst.compress
                                     return_ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 let uu____1915 =
                                   FStar_Syntax_Util.is_layered ed  in
                                 effect_args_from_repr uu____1914 uu____1915
                                   r
                                  in
                               FStar_All.pipe_right uu____1911
                                 (FStar_List.map
                                    (FStar_Syntax_Subst.subst subst))
                                in
                             let c =
                               let uu____1922 =
                                 let uu____1923 =
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
                                     uu____1923;
                                   FStar_Syntax_Syntax.flags = []
                                 }  in
                               FStar_Syntax_Syntax.mk_Comp uu____1922  in
                             ((let uu____1947 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____1947
                               then
                                 let uu____1952 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.print1 "} c after return %s\n"
                                   uu____1952
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
              let uu____1996 =
                FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
              if uu____1996
              then mk_indexed_return env ed u_a a e r
              else
                (let uu____2006 = mk_wp_return env ed u_a a e r  in
                 (uu____2006, FStar_TypeChecker_Env.trivial_guard))
  
let (lift_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp_typ ->
      FStar_TypeChecker_Env.mlift ->
        (FStar_Syntax_Syntax.comp * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      fun lift  ->
        let uu____2031 =
          FStar_All.pipe_right
            (let uu___251_2033 = c  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___251_2033.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___251_2033.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ =
                 (uu___251_2033.FStar_Syntax_Syntax.result_typ);
               FStar_Syntax_Syntax.effect_args =
                 (uu___251_2033.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags = []
             }) FStar_Syntax_Syntax.mk_Comp
           in
        FStar_All.pipe_right uu____2031
          (lift.FStar_TypeChecker_Env.mlift_wp env)
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1_in  ->
      fun l2_in  ->
        let uu____2054 =
          let uu____2059 = FStar_TypeChecker_Env.norm_eff_name env l1_in  in
          let uu____2060 = FStar_TypeChecker_Env.norm_eff_name env l2_in  in
          (uu____2059, uu____2060)  in
        match uu____2054 with
        | (l1,l2) ->
            let uu____2063 = FStar_TypeChecker_Env.join_opt env l1 l2  in
            (match uu____2063 with
             | FStar_Pervasives_Native.Some (m,uu____2073,uu____2074) -> m
             | FStar_Pervasives_Native.None  ->
                 let uu____2087 =
                   FStar_TypeChecker_Env.exists_polymonadic_bind env l1 l2
                    in
                 (match uu____2087 with
                  | FStar_Pervasives_Native.Some (m,uu____2101) -> m
                  | FStar_Pervasives_Native.None  ->
                      let uu____2134 =
                        let uu____2140 =
                          let uu____2142 =
                            FStar_Syntax_Print.lid_to_string l1_in  in
                          let uu____2144 =
                            FStar_Syntax_Print.lid_to_string l2_in  in
                          FStar_Util.format2
                            "Effects %s and %s cannot be composed" uu____2142
                            uu____2144
                           in
                        (FStar_Errors.Fatal_EffectsCannotBeComposed,
                          uu____2140)
                         in
                      FStar_Errors.raise_error uu____2134
                        env.FStar_TypeChecker_Env.range))
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____2164 =
          (FStar_TypeChecker_Common.is_total_lcomp c1) &&
            (FStar_TypeChecker_Common.is_total_lcomp c2)
           in
        if uu____2164
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
            let uu____2223 =
              FStar_TypeChecker_Env.join_opt env
                c11.FStar_Syntax_Syntax.effect_name
                c21.FStar_Syntax_Syntax.effect_name
               in
            match uu____2223 with
            | FStar_Pervasives_Native.Some (m,lift1,lift2) ->
                let uu____2251 = lift_comp env c11 lift1  in
                (match uu____2251 with
                 | (c12,g1) ->
                     let uu____2268 =
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
                          let uu____2307 = lift_comp env_x c21 lift2  in
                          match uu____2307 with
                          | (c22,g2) ->
                              let uu____2318 =
                                FStar_TypeChecker_Env.close_guard env 
                                  [x_a] g2
                                 in
                              (c22, uu____2318))
                        in
                     (match uu____2268 with
                      | (c22,g2) -> (m, c12, c22, g1, g2)))
            | FStar_Pervasives_Native.None  ->
                let rng = env.FStar_TypeChecker_Env.range  in
                let err uu____2365 =
                  let uu____2366 =
                    let uu____2372 =
                      let uu____2374 =
                        FStar_Syntax_Print.lid_to_string
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2376 =
                        FStar_Syntax_Print.lid_to_string
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____2374
                        uu____2376
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____2372)
                     in
                  FStar_Errors.raise_error uu____2366 rng  in
                ((let uu____2391 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "LayeredEffects")
                     in
                  if uu____2391
                  then
                    let uu____2396 =
                      let uu____2398 =
                        FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2398
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2400 =
                      let uu____2402 =
                        FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                         in
                      FStar_All.pipe_right uu____2402
                        FStar_Syntax_Print.comp_to_string
                       in
                    let uu____2404 = FStar_Util.string_of_bool for_bind  in
                    FStar_Util.print3
                      "Lifting comps %s and %s with for_bind %s{\n"
                      uu____2396 uu____2400 uu____2404
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
                      let uu____2460 =
                        let uu____2465 =
                          FStar_TypeChecker_Env.push_bv env x_bv  in
                        let uu____2466 =
                          FStar_TypeChecker_Env.get_effect_decl env ret_eff
                           in
                        let uu____2467 =
                          FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
                        let uu____2468 = FStar_Syntax_Syntax.bv_to_name x_bv
                           in
                        mk_return uu____2465 uu____2466 uu____2467
                          ct.FStar_Syntax_Syntax.result_typ uu____2468 rng
                         in
                      match uu____2460 with
                      | (c_ret,g_ret) ->
                          let uu____2475 =
                            let uu____2480 =
                              FStar_Syntax_Util.comp_to_comp_typ c_ret  in
                            f_bind env ct (FStar_Pervasives_Native.Some x_bv)
                              uu____2480 [] rng
                             in
                          (match uu____2475 with
                           | (c,g_bind) ->
                               let uu____2487 =
                                 FStar_TypeChecker_Env.conj_guard g_ret
                                   g_bind
                                  in
                               (c, uu____2487))
                       in
                    let try_lift c12 c22 =
                      let p_bind_opt =
                        FStar_TypeChecker_Env.exists_polymonadic_bind env
                          c12.FStar_Syntax_Syntax.effect_name
                          c22.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____2532 =
                        FStar_All.pipe_right p_bind_opt FStar_Util.is_some
                         in
                      if uu____2532
                      then
                        let uu____2568 =
                          FStar_All.pipe_right p_bind_opt FStar_Util.must  in
                        match uu____2568 with
                        | (p,f_bind) ->
                            let uu____2635 =
                              FStar_Ident.lid_equals p
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            (if uu____2635
                             then
                               let uu____2648 = bind_with_return c12 p f_bind
                                  in
                               match uu____2648 with
                               | (c13,g) ->
                                   let uu____2665 =
                                     let uu____2674 =
                                       FStar_Syntax_Syntax.mk_Comp c22  in
                                     ((c22.FStar_Syntax_Syntax.effect_name),
                                       c13, uu____2674, g)
                                      in
                                   FStar_Pervasives_Native.Some uu____2665
                             else FStar_Pervasives_Native.None)
                      else FStar_Pervasives_Native.None  in
                    let uu____2703 =
                      let uu____2714 = try_lift c11 c21  in
                      match uu____2714 with
                      | FStar_Pervasives_Native.Some (p,c12,c22,g) ->
                          (p, c12, c22, g,
                            FStar_TypeChecker_Env.trivial_guard)
                      | FStar_Pervasives_Native.None  ->
                          let uu____2755 = try_lift c21 c11  in
                          (match uu____2755 with
                           | FStar_Pervasives_Native.Some (p,c22,c12,g) ->
                               (p, c12, c22,
                                 FStar_TypeChecker_Env.trivial_guard, g)
                           | FStar_Pervasives_Native.None  -> err ())
                       in
                    match uu____2703 with
                    | (p,c12,c22,g1,g2) ->
                        ((let uu____2812 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2812
                          then
                            let uu____2817 = FStar_Ident.string_of_lid p  in
                            let uu____2819 =
                              FStar_Syntax_Print.comp_to_string c12  in
                            let uu____2821 =
                              FStar_Syntax_Print.comp_to_string c22  in
                            FStar_Util.print3
                              "} Returning p %s, c1 %s, and c2 %s\n"
                              uu____2817 uu____2819 uu____2821
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
            let uu____2874 = lift_comps_sep_guards env c1 c2 b for_bind  in
            match uu____2874 with
            | (l,c11,c21,g1,g2) ->
                let uu____2898 = FStar_TypeChecker_Env.conj_guard g1 g2  in
                (l, c11, c21, uu____2898)
  
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
          let uu____2954 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____2954
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2966 =
      let uu____2967 = FStar_Syntax_Subst.compress t  in
      uu____2967.FStar_Syntax_Syntax.n  in
    match uu____2966 with
    | FStar_Syntax_Syntax.Tm_arrow uu____2971 -> true
    | uu____2987 -> false
  
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
          f.FStar_Syntax_Syntax.pos
  
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
              let uu____3057 =
                let uu____3059 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____3059  in
              if uu____3057
              then f
              else (let uu____3066 = reason1 ()  in label uu____3066 r f)
  
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
            let uu___396_3087 = g  in
            let uu____3088 =
              let uu____3089 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____3089  in
            {
              FStar_TypeChecker_Common.guard_f = uu____3088;
              FStar_TypeChecker_Common.deferred =
                (uu___396_3087.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___396_3087.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___396_3087.FStar_TypeChecker_Common.implicits)
            }
  
let (close_wp_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____3110 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____3110
        then c
        else
          (let uu____3115 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____3115
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                let close =
                  let uu____3157 =
                    FStar_All.pipe_right md
                      FStar_Syntax_Util.get_wp_close_combinator
                     in
                  FStar_All.pipe_right uu____3157 FStar_Util.must  in
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____3186 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____3186]  in
                       let us =
                         let uu____3208 =
                           let uu____3211 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____3211]  in
                         u_res :: uu____3208  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____3217 =
                         FStar_TypeChecker_Env.inst_effect_fun_with us env md
                           close
                          in
                       let uu____3218 =
                         let uu____3219 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____3228 =
                           let uu____3239 =
                             FStar_Syntax_Syntax.as_arg
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____3248 =
                             let uu____3259 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____3259]  in
                           uu____3239 :: uu____3248  in
                         uu____3219 :: uu____3228  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____3217 uu____3218
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____3301 = destruct_wp_comp c1  in
              match uu____3301 with
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
                let uu____3341 =
                  FStar_All.pipe_right g
                    (FStar_TypeChecker_Env.close_guard env bs)
                   in
                FStar_All.pipe_right uu____3341
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
                  let uu____3391 =
                    FStar_All.pipe_right g
                      (FStar_TypeChecker_Env.close_guard env bs)
                     in
                  FStar_All.pipe_right uu____3391
                    (close_guard_implicits env false bs)))
  
let (should_not_inline_lc : FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
      (FStar_Util.for_some
         (fun uu___0_3404  ->
            match uu___0_3404 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____3407 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Common.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        let lc_is_unit_or_effectful =
          let uu____3432 =
            let uu____3435 =
              FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                FStar_Syntax_Util.arrow_formals_comp
               in
            FStar_All.pipe_right uu____3435 FStar_Pervasives_Native.snd  in
          FStar_All.pipe_right uu____3432
            (fun c  ->
               (let uu____3459 =
                  FStar_TypeChecker_Env.is_reifiable_comp env c  in
                Prims.op_Negation uu____3459) &&
                 ((FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Util.is_unit)
                    ||
                    (let uu____3463 =
                       FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                     Prims.op_Negation uu____3463)))
           in
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_TypeChecker_Common.is_pure_or_ghost_lcomp lc) &&
                (Prims.op_Negation lc_is_unit_or_effectful))
               &&
               (let uu____3474 = FStar_Syntax_Util.head_and_args' e  in
                match uu____3474 with
                | (head,uu____3491) ->
                    let uu____3512 =
                      let uu____3513 = FStar_Syntax_Util.un_uinst head  in
                      uu____3513.FStar_Syntax_Syntax.n  in
                    (match uu____3512 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____3518 =
                           let uu____3520 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____3520
                            in
                         Prims.op_Negation uu____3518
                     | uu____3521 -> true)))
              &&
              (let uu____3524 = should_not_inline_lc lc  in
               Prims.op_Negation uu____3524)
  
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
            let uu____3552 =
              let uu____3554 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____3554  in
            if uu____3552
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____3561 = FStar_Syntax_Util.is_unit t  in
               if uu____3561
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
                    let uu____3570 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____3570
                    then FStar_Syntax_Syntax.tun
                    else
                      (let ret_wp =
                         FStar_All.pipe_right m
                           FStar_Syntax_Util.get_return_vc_combinator
                          in
                       let uu____3576 =
                         let uu____3577 =
                           FStar_TypeChecker_Env.inst_effect_fun_with 
                             [u_t] env m ret_wp
                            in
                         let uu____3578 =
                           let uu____3579 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____3588 =
                             let uu____3599 = FStar_Syntax_Syntax.as_arg v
                                in
                             [uu____3599]  in
                           uu____3579 :: uu____3588  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____3577 uu____3578
                           v.FStar_Syntax_Syntax.pos
                          in
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Env.Beta;
                         FStar_TypeChecker_Env.NoFullNorm] env uu____3576)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____3633 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____3633
           then
             let uu____3638 =
               FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos  in
             let uu____3640 = FStar_Syntax_Print.term_to_string v  in
             let uu____3642 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____3638 uu____3640 uu____3642
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
                      let bind_name =
                        let uu____3716 =
                          let uu____3718 =
                            FStar_All.pipe_right m FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3718
                            FStar_Ident.string_of_id
                           in
                        let uu____3720 =
                          let uu____3722 =
                            FStar_All.pipe_right n FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3722
                            FStar_Ident.string_of_id
                           in
                        let uu____3724 =
                          let uu____3726 =
                            FStar_All.pipe_right p FStar_Ident.ident_of_lid
                             in
                          FStar_All.pipe_right uu____3726
                            FStar_Ident.string_of_id
                           in
                        FStar_Util.format3 "(%s, %s) |> %s" uu____3716
                          uu____3720 uu____3724
                         in
                      (let uu____3730 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LayeredEffects")
                          in
                       if uu____3730
                       then
                         let uu____3735 =
                           let uu____3737 = FStar_Syntax_Syntax.mk_Comp ct1
                              in
                           FStar_Syntax_Print.comp_to_string uu____3737  in
                         let uu____3738 =
                           let uu____3740 = FStar_Syntax_Syntax.mk_Comp ct2
                              in
                           FStar_Syntax_Print.comp_to_string uu____3740  in
                         FStar_Util.print2 "Binding c1:%s and c2:%s {\n"
                           uu____3735 uu____3738
                       else ());
                      (let uu____3744 =
                         let uu____3751 =
                           FStar_TypeChecker_Env.get_effect_decl env m  in
                         let uu____3752 =
                           FStar_TypeChecker_Env.get_effect_decl env n  in
                         let uu____3753 =
                           FStar_TypeChecker_Env.get_effect_decl env p  in
                         (uu____3751, uu____3752, uu____3753)  in
                       match uu____3744 with
                       | (m_ed,n_ed,p_ed) ->
                           let uu____3761 =
                             let uu____3772 =
                               FStar_List.hd
                                 ct1.FStar_Syntax_Syntax.comp_univs
                                in
                             let uu____3773 =
                               FStar_List.map FStar_Pervasives_Native.fst
                                 ct1.FStar_Syntax_Syntax.effect_args
                                in
                             (uu____3772,
                               (ct1.FStar_Syntax_Syntax.result_typ),
                               uu____3773)
                              in
                           (match uu____3761 with
                            | (u1,t1,is1) ->
                                let uu____3807 =
                                  let uu____3818 =
                                    FStar_List.hd
                                      ct2.FStar_Syntax_Syntax.comp_univs
                                     in
                                  let uu____3819 =
                                    FStar_List.map
                                      FStar_Pervasives_Native.fst
                                      ct2.FStar_Syntax_Syntax.effect_args
                                     in
                                  (uu____3818,
                                    (ct2.FStar_Syntax_Syntax.result_typ),
                                    uu____3819)
                                   in
                                (match uu____3807 with
                                 | (u2,t2,is2) ->
                                     let uu____3853 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         bind_t [u1; u2]
                                        in
                                     (match uu____3853 with
                                      | (uu____3862,bind_t1) ->
                                          let bind_t_shape_error s =
                                            let uu____3877 =
                                              let uu____3879 =
                                                FStar_Syntax_Print.term_to_string
                                                  bind_t1
                                                 in
                                              FStar_Util.format3
                                                "bind %s (%s) does not have proper shape (reason:%s)"
                                                uu____3879 bind_name s
                                               in
                                            (FStar_Errors.Fatal_UnexpectedEffect,
                                              uu____3877)
                                             in
                                          let uu____3883 =
                                            let uu____3928 =
                                              let uu____3929 =
                                                FStar_Syntax_Subst.compress
                                                  bind_t1
                                                 in
                                              uu____3929.FStar_Syntax_Syntax.n
                                               in
                                            match uu____3928 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs,c) when
                                                (FStar_List.length bs) >=
                                                  (Prims.of_int (4))
                                                ->
                                                let uu____4005 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs c
                                                   in
                                                (match uu____4005 with
                                                 | (a_b::b_b::bs1,c1) ->
                                                     let uu____4090 =
                                                       let uu____4117 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2)))
                                                           bs1
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____4117
                                                         (fun uu____4202  ->
                                                            match uu____4202
                                                            with
                                                            | (l1,l2) ->
                                                                let uu____4283
                                                                  =
                                                                  FStar_List.hd
                                                                    l2
                                                                   in
                                                                let uu____4296
                                                                  =
                                                                  let uu____4303
                                                                    =
                                                                    FStar_List.tl
                                                                    l2  in
                                                                  FStar_List.hd
                                                                    uu____4303
                                                                   in
                                                                (l1,
                                                                  uu____4283,
                                                                  uu____4296))
                                                        in
                                                     (match uu____4090 with
                                                      | (rest_bs,f_b,g_b) ->
                                                          (a_b, b_b, rest_bs,
                                                            f_b, g_b, c1)))
                                            | uu____4463 ->
                                                let uu____4464 =
                                                  bind_t_shape_error
                                                    "Either not an arrow or not enough binders"
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4464 r1
                                             in
                                          (match uu____3883 with
                                           | (a_b,b_b,rest_bs,f_b,g_b,bind_c)
                                               ->
                                               let uu____4589 =
                                                 let uu____4596 =
                                                   let uu____4597 =
                                                     let uu____4598 =
                                                       let uu____4605 =
                                                         FStar_All.pipe_right
                                                           a_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       (uu____4605, t1)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4598
                                                      in
                                                   let uu____4616 =
                                                     let uu____4619 =
                                                       let uu____4620 =
                                                         let uu____4627 =
                                                           FStar_All.pipe_right
                                                             b_b
                                                             FStar_Pervasives_Native.fst
                                                            in
                                                         (uu____4627, t2)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4620
                                                        in
                                                     [uu____4619]  in
                                                   uu____4597 :: uu____4616
                                                    in
                                                 FStar_TypeChecker_Env.uvars_for_binders
                                                   env rest_bs uu____4596
                                                   (fun b1  ->
                                                      let uu____4642 =
                                                        FStar_Syntax_Print.binder_to_string
                                                          b1
                                                         in
                                                      let uu____4644 =
                                                        FStar_Range.string_of_range
                                                          r1
                                                         in
                                                      FStar_Util.format3
                                                        "implicit var for binder %s of %s at %s"
                                                        uu____4642 bind_name
                                                        uu____4644) r1
                                                  in
                                               (match uu____4589 with
                                                | (rest_bs_uvars,g_uvars) ->
                                                    let subst =
                                                      FStar_List.map2
                                                        (fun b1  ->
                                                           fun t  ->
                                                             let uu____4681 =
                                                               let uu____4688
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   b1
                                                                   FStar_Pervasives_Native.fst
                                                                  in
                                                               (uu____4688,
                                                                 t)
                                                                in
                                                             FStar_Syntax_Syntax.NT
                                                               uu____4681)
                                                        (a_b :: b_b ::
                                                        rest_bs) (t1 :: t2 ::
                                                        rest_bs_uvars)
                                                       in
                                                    let f_guard =
                                                      let f_sort_is =
                                                        let uu____4715 =
                                                          let uu____4718 =
                                                            let uu____4719 =
                                                              let uu____4720
                                                                =
                                                                FStar_All.pipe_right
                                                                  f_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4720.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4719
                                                             in
                                                          let uu____4729 =
                                                            FStar_Syntax_Util.is_layered
                                                              m_ed
                                                             in
                                                          effect_args_from_repr
                                                            uu____4718
                                                            uu____4729 r1
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4715
                                                          (FStar_List.map
                                                             (FStar_Syntax_Subst.subst
                                                                subst))
                                                         in
                                                      FStar_List.fold_left2
                                                        (fun g  ->
                                                           fun i1  ->
                                                             fun f_i1  ->
                                                               let uu____4742
                                                                 =
                                                                 FStar_TypeChecker_Rel.layered_effect_teq
                                                                   env i1
                                                                   f_i1
                                                                   (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                  in
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g uu____4742)
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
                                                        let uu____4762 =
                                                          let uu____4763 =
                                                            let uu____4766 =
                                                              let uu____4767
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_b
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              uu____4767.FStar_Syntax_Syntax.sort
                                                               in
                                                            FStar_Syntax_Subst.compress
                                                              uu____4766
                                                             in
                                                          uu____4763.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____4762 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____4800 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____4800
                                                             with
                                                             | (bs1,c1) ->
                                                                 let bs_subst
                                                                   =
                                                                   let uu____4810
                                                                    =
                                                                    let uu____4817
                                                                    =
                                                                    let uu____4818
                                                                    =
                                                                    FStar_List.hd
                                                                    bs1  in
                                                                    FStar_All.pipe_right
                                                                    uu____4818
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    let uu____4839
                                                                    =
                                                                    let uu____4842
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    x_a
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____4842
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                     in
                                                                    (uu____4817,
                                                                    uu____4839)
                                                                     in
                                                                   FStar_Syntax_Syntax.NT
                                                                    uu____4810
                                                                    in
                                                                 let c2 =
                                                                   FStar_Syntax_Subst.subst_comp
                                                                    [bs_subst]
                                                                    c1
                                                                    in
                                                                 let uu____4856
                                                                   =
                                                                   let uu____4859
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c2)  in
                                                                   let uu____4860
                                                                    =
                                                                    FStar_Syntax_Util.is_layered
                                                                    n_ed  in
                                                                   effect_args_from_repr
                                                                    uu____4859
                                                                    uu____4860
                                                                    r1
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____4856
                                                                   (FStar_List.map
                                                                    (FStar_Syntax_Subst.subst
                                                                    subst)))
                                                        | uu____4866 ->
                                                            failwith
                                                              "impossible: mk_indexed_bind"
                                                         in
                                                      let env_g =
                                                        FStar_TypeChecker_Env.push_binders
                                                          env [x_a]
                                                         in
                                                      let uu____4883 =
                                                        FStar_List.fold_left2
                                                          (fun g  ->
                                                             fun i1  ->
                                                               fun g_i1  ->
                                                                 let uu____4891
                                                                   =
                                                                   FStar_TypeChecker_Rel.layered_effect_teq
                                                                    env_g i1
                                                                    g_i1
                                                                    (FStar_Pervasives_Native.Some
                                                                    bind_name)
                                                                    in
                                                                 FStar_TypeChecker_Env.conj_guard
                                                                   g
                                                                   uu____4891)
                                                          FStar_TypeChecker_Env.trivial_guard
                                                          is2 g_sort_is
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4883
                                                        (FStar_TypeChecker_Env.close_guard
                                                           env [x_a])
                                                       in
                                                    let bind_ct =
                                                      let uu____4906 =
                                                        FStar_All.pipe_right
                                                          bind_c
                                                          (FStar_Syntax_Subst.subst_comp
                                                             subst)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4906
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                       in
                                                    let fml =
                                                      let uu____4908 =
                                                        let uu____4913 =
                                                          FStar_List.hd
                                                            bind_ct.FStar_Syntax_Syntax.comp_univs
                                                           in
                                                        let uu____4914 =
                                                          let uu____4915 =
                                                            FStar_List.hd
                                                              bind_ct.FStar_Syntax_Syntax.effect_args
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____4915
                                                           in
                                                        (uu____4913,
                                                          uu____4914)
                                                         in
                                                      match uu____4908 with
                                                      | (u,wp) ->
                                                          FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                            env u
                                                            bind_ct.FStar_Syntax_Syntax.result_typ
                                                            wp
                                                            FStar_Range.dummyRange
                                                       in
                                                    let is =
                                                      let uu____4941 =
                                                        FStar_Syntax_Subst.compress
                                                          bind_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      let uu____4942 =
                                                        FStar_Syntax_Util.is_layered
                                                          p_ed
                                                         in
                                                      effect_args_from_repr
                                                        uu____4941 uu____4942
                                                        r1
                                                       in
                                                    let c =
                                                      let uu____4945 =
                                                        let uu____4946 =
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
                                                            = uu____4946;
                                                          FStar_Syntax_Syntax.flags
                                                            = flags
                                                        }  in
                                                      FStar_Syntax_Syntax.mk_Comp
                                                        uu____4945
                                                       in
                                                    ((let uu____4966 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "LayeredEffects")
                                                         in
                                                      if uu____4966
                                                      then
                                                        let uu____4971 =
                                                          FStar_Syntax_Print.comp_to_string
                                                            c
                                                           in
                                                        FStar_Util.print1
                                                          "} c after bind: %s\n"
                                                          uu____4971
                                                      else ());
                                                     (let uu____4976 =
                                                        let uu____4977 =
                                                          let uu____4980 =
                                                            let uu____4983 =
                                                              let uu____4986
                                                                =
                                                                let uu____4989
                                                                  =
                                                                  FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    fml)
                                                                   in
                                                                [uu____4989]
                                                                 in
                                                              g_guard ::
                                                                uu____4986
                                                               in
                                                            f_guard ::
                                                              uu____4983
                                                             in
                                                          g_uvars ::
                                                            uu____4980
                                                           in
                                                        FStar_TypeChecker_Env.conj_guards
                                                          uu____4977
                                                         in
                                                      (c, uu____4976)))))))))
  
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
                let uu____5034 =
                  let md = FStar_TypeChecker_Env.get_effect_decl env m  in
                  let uu____5060 = FStar_TypeChecker_Env.wp_signature env m
                     in
                  match uu____5060 with
                  | (a,kwp) ->
                      let uu____5091 = destruct_wp_comp ct1  in
                      let uu____5098 = destruct_wp_comp ct2  in
                      ((md, a, kwp), uu____5091, uu____5098)
                   in
                match uu____5034 with
                | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                    let bs =
                      match b with
                      | FStar_Pervasives_Native.None  ->
                          let uu____5151 = FStar_Syntax_Syntax.null_binder t1
                             in
                          [uu____5151]
                      | FStar_Pervasives_Native.Some x ->
                          let uu____5171 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____5171]
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
                           (FStar_Const.Const_range r1)) r1
                       in
                    let wp_args =
                      let uu____5218 = FStar_Syntax_Syntax.as_arg r11  in
                      let uu____5227 =
                        let uu____5238 = FStar_Syntax_Syntax.as_arg t1  in
                        let uu____5247 =
                          let uu____5258 = FStar_Syntax_Syntax.as_arg t2  in
                          let uu____5267 =
                            let uu____5278 = FStar_Syntax_Syntax.as_arg wp1
                               in
                            let uu____5287 =
                              let uu____5298 =
                                let uu____5307 = mk_lam wp2  in
                                FStar_Syntax_Syntax.as_arg uu____5307  in
                              [uu____5298]  in
                            uu____5278 :: uu____5287  in
                          uu____5258 :: uu____5267  in
                        uu____5238 :: uu____5247  in
                      uu____5218 :: uu____5227  in
                    let bind_wp =
                      FStar_All.pipe_right md
                        FStar_Syntax_Util.get_bind_vc_combinator
                       in
                    let wp =
                      let uu____5358 =
                        FStar_TypeChecker_Env.inst_effect_fun_with
                          [u_t1; u_t2] env md bind_wp
                         in
                      FStar_Syntax_Syntax.mk_Tm_app uu____5358 wp_args
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
              let uu____5406 =
                let uu____5411 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
                let uu____5412 =
                  FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
                (uu____5411, uu____5412)  in
              match uu____5406 with
              | (ct1,ct2) ->
                  let uu____5419 =
                    FStar_TypeChecker_Env.exists_polymonadic_bind env
                      ct1.FStar_Syntax_Syntax.effect_name
                      ct2.FStar_Syntax_Syntax.effect_name
                     in
                  (match uu____5419 with
                   | FStar_Pervasives_Native.Some (p,f_bind) ->
                       f_bind env ct1 b ct2 flags r1
                   | FStar_Pervasives_Native.None  ->
                       let uu____5470 = lift_comps env c1 c2 b true  in
                       (match uu____5470 with
                        | (m,c11,c21,g_lift) ->
                            let uu____5488 =
                              let uu____5493 =
                                FStar_Syntax_Util.comp_to_comp_typ c11  in
                              let uu____5494 =
                                FStar_Syntax_Util.comp_to_comp_typ c21  in
                              (uu____5493, uu____5494)  in
                            (match uu____5488 with
                             | (ct11,ct21) ->
                                 let uu____5501 =
                                   let uu____5506 =
                                     FStar_TypeChecker_Env.is_layered_effect
                                       env m
                                      in
                                   if uu____5506
                                   then
                                     let bind_t =
                                       let uu____5514 =
                                         FStar_All.pipe_right m
                                           (FStar_TypeChecker_Env.get_effect_decl
                                              env)
                                          in
                                       FStar_All.pipe_right uu____5514
                                         FStar_Syntax_Util.get_bind_vc_combinator
                                        in
                                     mk_indexed_bind env m m m bind_t ct11 b
                                       ct21 flags r1
                                   else
                                     (let uu____5517 =
                                        mk_wp_bind env m ct11 b ct21 flags r1
                                         in
                                      (uu____5517,
                                        FStar_TypeChecker_Env.trivial_guard))
                                    in
                                 (match uu____5501 with
                                  | (c,g_bind) ->
                                      let uu____5524 =
                                        FStar_TypeChecker_Env.conj_guard
                                          g_lift g_bind
                                         in
                                      (c, uu____5524)))))
  
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
            let uu____5560 =
              let uu____5561 =
                let uu____5572 =
                  FStar_All.pipe_right wp1 FStar_Syntax_Syntax.as_arg  in
                [uu____5572]  in
              {
                FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
                FStar_Syntax_Syntax.effect_args = uu____5561;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____5560  in
          mk_bind env pure_c FStar_Pervasives_Native.None c flags r
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    let uu____5617 =
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___1_5623  ->
              match uu___1_5623 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____5626 -> false))
       in
    if uu____5617
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags
        (FStar_List.collect
           (fun uu___2_5638  ->
              match uu___2_5638 with
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
        let uu____5666 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____5666
        then (c, FStar_TypeChecker_Env.trivial_guard)
        else
          (let ct = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let pure_assume_wp =
             let uu____5677 =
               FStar_Syntax_Syntax.lid_as_fv
                 FStar_Parser_Const.pure_assume_wp_lid
                 (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                 FStar_Pervasives_Native.None
                in
             FStar_Syntax_Syntax.fv_to_tm uu____5677  in
           let pure_assume_wp1 =
             let uu____5680 =
               let uu____5681 =
                 FStar_All.pipe_left FStar_Syntax_Syntax.as_arg formula  in
               [uu____5681]  in
             let uu____5714 = FStar_TypeChecker_Env.get_range env  in
             FStar_Syntax_Syntax.mk_Tm_app pure_assume_wp uu____5680
               uu____5714
              in
           let uu____5715 = weaken_flags ct.FStar_Syntax_Syntax.flags  in
           bind_pure_wp_with env pure_assume_wp1 c uu____5715)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp ->
      FStar_TypeChecker_Common.guard_formula ->
        FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____5743 =
          let uu____5744 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____5744 with
          | (c,g_c) ->
              let uu____5755 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____5755
              then (c, g_c)
              else
                (match f with
                 | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                 | FStar_TypeChecker_Common.NonTrivial f1 ->
                     let uu____5769 = weaken_comp env c f1  in
                     (match uu____5769 with
                      | (c1,g_w) ->
                          let uu____5780 =
                            FStar_TypeChecker_Env.conj_guard g_c g_w  in
                          (c1, uu____5780)))
           in
        let uu____5781 = weaken_flags lc.FStar_TypeChecker_Common.cflags  in
        FStar_TypeChecker_Common.mk_lcomp
          lc.FStar_TypeChecker_Common.eff_name
          lc.FStar_TypeChecker_Common.res_typ uu____5781 weaken
  
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
                 let uu____5838 =
                   FStar_Syntax_Syntax.lid_as_fv
                     FStar_Parser_Const.pure_assert_wp_lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____5838  in
               let pure_assert_wp1 =
                 let uu____5841 =
                   let uu____5842 =
                     let uu____5851 = label_opt env reason r f  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                       uu____5851
                      in
                   [uu____5842]  in
                 FStar_Syntax_Syntax.mk_Tm_app pure_assert_wp uu____5841 r
                  in
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
            let uu____5921 =
              FStar_TypeChecker_Env.is_trivial_guard_formula g0  in
            if uu____5921
            then (lc, g0)
            else
              (let flags =
                 let uu____5933 =
                   let uu____5941 =
                     FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc  in
                   if uu____5941
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5933 with
                 | (maybe_trivial_post,flags) ->
                     let uu____5971 =
                       FStar_All.pipe_right
                         lc.FStar_TypeChecker_Common.cflags
                         (FStar_List.collect
                            (fun uu___3_5979  ->
                               match uu___3_5979 with
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
                               | uu____5982 -> []))
                        in
                     FStar_List.append flags uu____5971
                  in
               let strengthen uu____5992 =
                 let uu____5993 = FStar_TypeChecker_Common.lcomp_comp lc  in
                 match uu____5993 with
                 | (c,g_c) ->
                     if env.FStar_TypeChecker_Env.lax
                     then (c, g_c)
                     else
                       (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0
                           in
                        let uu____6012 = FStar_TypeChecker_Env.guard_form g01
                           in
                        match uu____6012 with
                        | FStar_TypeChecker_Common.Trivial  -> (c, g_c)
                        | FStar_TypeChecker_Common.NonTrivial f ->
                            ((let uu____6019 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____6019
                              then
                                let uu____6023 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env e_for_debugging_only
                                   in
                                let uu____6025 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f
                                   in
                                FStar_Util.print2
                                  "-------------Strengthening pre-condition of term %s with guard %s\n"
                                  uu____6023 uu____6025
                              else ());
                             (let uu____6030 =
                                strengthen_comp env reason c f flags  in
                              match uu____6030 with
                              | (c1,g_s) ->
                                  let uu____6041 =
                                    FStar_TypeChecker_Env.conj_guard g_c g_s
                                     in
                                  (c1, uu____6041))))
                  in
               let uu____6042 =
                 let uu____6043 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_TypeChecker_Common.eff_name
                    in
                 FStar_TypeChecker_Common.mk_lcomp uu____6043
                   lc.FStar_TypeChecker_Common.res_typ flags strengthen
                  in
               (uu____6042,
                 (let uu___708_6045 = g0  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___708_6045.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___708_6045.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___708_6045.FStar_TypeChecker_Common.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_TypeChecker_Common.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___4_6054  ->
            match uu___4_6054 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____6058 -> false) lc.FStar_TypeChecker_Common.cflags)
  
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
          let uu____6087 =
            (FStar_TypeChecker_Common.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____6087
          then e
          else
            (let uu____6094 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____6097 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____6097)
                in
             if uu____6094
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
                | uu____6167 -> false  in
              if is_unit
              then
                let uu____6174 =
                  let uu____6176 =
                    let uu____6177 =
                      FStar_All.pipe_right c
                        FStar_Syntax_Util.comp_effect_name
                       in
                    FStar_All.pipe_right uu____6177
                      (FStar_TypeChecker_Env.norm_eff_name env)
                     in
                  FStar_All.pipe_right uu____6176
                    (FStar_TypeChecker_Env.is_layered_effect env)
                   in
                (if uu____6174
                 then
                   let uu____6186 = FStar_Syntax_Subst.open_term_bv b phi  in
                   match uu____6186 with
                   | (b1,phi1) ->
                       let phi2 =
                         FStar_Syntax_Subst.subst
                           [FStar_Syntax_Syntax.NT
                              (b1, FStar_Syntax_Syntax.unit_const)] phi1
                          in
                       weaken_comp env c phi2
                 else
                   (let uu____6202 = close_wp_comp env [x] c  in
                    (uu____6202, FStar_TypeChecker_Env.trivial_guard)))
              else (c, FStar_TypeChecker_Env.trivial_guard)
          | uu____6205 -> (c, FStar_TypeChecker_Env.trivial_guard)
  
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
          fun uu____6233  ->
            match uu____6233 with
            | (b,lc2) ->
                let debug f =
                  let uu____6253 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____6253 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____6266 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____6266
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags =
                       let uu____6276 =
                         FStar_TypeChecker_Common.is_total_lcomp lc11  in
                       if uu____6276
                       then
                         let uu____6281 =
                           FStar_TypeChecker_Common.is_total_lcomp lc21  in
                         (if uu____6281
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____6288 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21
                                in
                             if uu____6288
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____6297 =
                            (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                               lc11)
                              &&
                              (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 lc21)
                             in
                          if uu____6297
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____6304 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____6304
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags
                     else flags)
                   in
                let bind_it uu____6320 =
                  let uu____6321 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____6321
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_TypeChecker_Common.res_typ
                       in
                    let uu____6329 =
                      lax_mk_tot_or_comp_l joined_eff u_t
                        lc21.FStar_TypeChecker_Common.res_typ []
                       in
                    (uu____6329, FStar_TypeChecker_Env.trivial_guard)
                  else
                    (let uu____6332 =
                       FStar_TypeChecker_Common.lcomp_comp lc11  in
                     match uu____6332 with
                     | (c1,g_c1) ->
                         let uu____6343 =
                           FStar_TypeChecker_Common.lcomp_comp lc21  in
                         (match uu____6343 with
                          | (c2,g_c2) ->
                              let trivial_guard =
                                let uu____6355 =
                                  match b with
                                  | FStar_Pervasives_Native.Some x ->
                                      let b1 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      let uu____6358 =
                                        FStar_Syntax_Syntax.is_null_binder b1
                                         in
                                      if uu____6358
                                      then g_c2
                                      else
                                        FStar_TypeChecker_Env.close_guard env
                                          [b1] g_c2
                                  | FStar_Pervasives_Native.None  -> g_c2  in
                                FStar_TypeChecker_Env.conj_guard g_c1
                                  uu____6355
                                 in
                              (debug
                                 (fun uu____6384  ->
                                    let uu____6385 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    let uu____6387 =
                                      match b with
                                      | FStar_Pervasives_Native.None  ->
                                          "none"
                                      | FStar_Pervasives_Native.Some x ->
                                          FStar_Syntax_Print.bv_to_string x
                                       in
                                    let uu____6392 =
                                      FStar_Syntax_Print.comp_to_string c2
                                       in
                                    FStar_Util.print3
                                      "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                                      uu____6385 uu____6387 uu____6392);
                               (let aux uu____6410 =
                                  let uu____6411 =
                                    FStar_Syntax_Util.is_trivial_wp c1  in
                                  if uu____6411
                                  then
                                    match b with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Util.Inl
                                          (c2, "trivial no binder")
                                    | FStar_Pervasives_Native.Some uu____6442
                                        ->
                                        let uu____6443 =
                                          FStar_Syntax_Util.is_ml_comp c2  in
                                        (if uu____6443
                                         then
                                           FStar_Util.Inl (c2, "trivial ml")
                                         else
                                           FStar_Util.Inr
                                             "c1 trivial; but c2 is not ML")
                                  else
                                    (let uu____6475 =
                                       (FStar_Syntax_Util.is_ml_comp c1) &&
                                         (FStar_Syntax_Util.is_ml_comp c2)
                                        in
                                     if uu____6475
                                     then FStar_Util.Inl (c2, "both ml")
                                     else
                                       FStar_Util.Inr
                                         "c1 not trivial, and both are not ML")
                                   in
                                let try_simplify uu____6522 =
                                  let aux_with_trivial_guard uu____6552 =
                                    let uu____6553 = aux ()  in
                                    match uu____6553 with
                                    | FStar_Util.Inl (c,reason) ->
                                        FStar_Util.Inl
                                          (c, trivial_guard, reason)
                                    | FStar_Util.Inr reason ->
                                        FStar_Util.Inr reason
                                     in
                                  let uu____6611 =
                                    let uu____6613 =
                                      FStar_TypeChecker_Env.try_lookup_effect_lid
                                        env
                                        FStar_Parser_Const.effect_GTot_lid
                                       in
                                    FStar_Option.isNone uu____6613  in
                                  if uu____6611
                                  then
                                    let uu____6629 =
                                      (FStar_Syntax_Util.is_tot_or_gtot_comp
                                         c1)
                                        &&
                                        (FStar_Syntax_Util.is_tot_or_gtot_comp
                                           c2)
                                       in
                                    (if uu____6629
                                     then
                                       FStar_Util.Inl
                                         (c2, trivial_guard,
                                           "Early in prims; we don't have bind yet")
                                     else
                                       (let uu____6656 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                            "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                          uu____6656))
                                  else
                                    (let uu____6673 =
                                       FStar_Syntax_Util.is_total_comp c1  in
                                     if uu____6673
                                     then
                                       let close_with_type_of_x x c =
                                         let x1 =
                                           let uu___811_6704 = x  in
                                           {
                                             FStar_Syntax_Syntax.ppname =
                                               (uu___811_6704.FStar_Syntax_Syntax.ppname);
                                             FStar_Syntax_Syntax.index =
                                               (uu___811_6704.FStar_Syntax_Syntax.index);
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
                                           let uu____6735 =
                                             let uu____6740 =
                                               FStar_All.pipe_right c2
                                                 (FStar_Syntax_Subst.subst_comp
                                                    [FStar_Syntax_Syntax.NT
                                                       (x, e)])
                                                in
                                             FStar_All.pipe_right uu____6740
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6735 with
                                            | (c21,g_close) ->
                                                let uu____6761 =
                                                  let uu____6769 =
                                                    let uu____6770 =
                                                      let uu____6773 =
                                                        let uu____6776 =
                                                          FStar_TypeChecker_Env.map_guard
                                                            g_c2
                                                            (FStar_Syntax_Subst.subst
                                                               [FStar_Syntax_Syntax.NT
                                                                  (x, e)])
                                                           in
                                                        [uu____6776; g_close]
                                                         in
                                                      g_c1 :: uu____6773  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6770
                                                     in
                                                  (c21, uu____6769, "c1 Tot")
                                                   in
                                                FStar_Util.Inl uu____6761)
                                       | (uu____6789,FStar_Pervasives_Native.Some
                                          x) ->
                                           let uu____6801 =
                                             FStar_All.pipe_right c2
                                               (close_with_type_of_x x)
                                              in
                                           (match uu____6801 with
                                            | (c21,g_close) ->
                                                let uu____6824 =
                                                  let uu____6832 =
                                                    let uu____6833 =
                                                      let uu____6836 =
                                                        let uu____6839 =
                                                          let uu____6840 =
                                                            let uu____6841 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x
                                                               in
                                                            [uu____6841]  in
                                                          FStar_TypeChecker_Env.close_guard
                                                            env uu____6840
                                                            g_c2
                                                           in
                                                        [uu____6839; g_close]
                                                         in
                                                      g_c1 :: uu____6836  in
                                                    FStar_TypeChecker_Env.conj_guards
                                                      uu____6833
                                                     in
                                                  (c21, uu____6832,
                                                    "c1 Tot only close")
                                                   in
                                                FStar_Util.Inl uu____6824)
                                       | (uu____6870,uu____6871) ->
                                           aux_with_trivial_guard ()
                                     else
                                       (let uu____6886 =
                                          (FStar_Syntax_Util.is_tot_or_gtot_comp
                                             c1)
                                            &&
                                            (FStar_Syntax_Util.is_tot_or_gtot_comp
                                               c2)
                                           in
                                        if uu____6886
                                        then
                                          let uu____6901 =
                                            let uu____6909 =
                                              FStar_Syntax_Syntax.mk_GTotal
                                                (FStar_Syntax_Util.comp_result
                                                   c2)
                                               in
                                            (uu____6909, trivial_guard,
                                              "both GTot")
                                             in
                                          FStar_Util.Inl uu____6901
                                        else aux_with_trivial_guard ()))
                                   in
                                let uu____6922 = try_simplify ()  in
                                match uu____6922 with
                                | FStar_Util.Inl (c,g,reason) ->
                                    (debug
                                       (fun uu____6957  ->
                                          let uu____6958 =
                                            FStar_Syntax_Print.comp_to_string
                                              c
                                             in
                                          FStar_Util.print2
                                            "(2) bind: Simplified (because %s) to\n\t%s\n"
                                            reason uu____6958);
                                     (c, g))
                                | FStar_Util.Inr reason ->
                                    (debug
                                       (fun uu____6974  ->
                                          FStar_Util.print1
                                            "(2) bind: Not simplified because %s\n"
                                            reason);
                                     (let mk_bind1 c11 b1 c21 g =
                                        let uu____7005 =
                                          mk_bind env c11 b1 c21 bind_flags
                                            r1
                                           in
                                        match uu____7005 with
                                        | (c,g_bind) ->
                                            let uu____7016 =
                                              FStar_TypeChecker_Env.conj_guard
                                                g g_bind
                                               in
                                            (c, uu____7016)
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
                                        let uu____7043 =
                                          FStar_TypeChecker_Env.join env
                                            c12.FStar_Syntax_Syntax.effect_name
                                            c22.FStar_Syntax_Syntax.effect_name
                                           in
                                        match uu____7043 with
                                        | (m,uu____7055,lift2) ->
                                            let uu____7057 =
                                              lift_comp env c22 lift2  in
                                            (match uu____7057 with
                                             | (c23,g2) ->
                                                 let uu____7068 =
                                                   destruct_wp_comp c12  in
                                                 (match uu____7068 with
                                                  | (u1,t1,wp1) ->
                                                      let md_pure_or_ghost =
                                                        FStar_TypeChecker_Env.get_effect_decl
                                                          env
                                                          c12.FStar_Syntax_Syntax.effect_name
                                                         in
                                                      let trivial =
                                                        let uu____7084 =
                                                          FStar_All.pipe_right
                                                            md_pure_or_ghost
                                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7084
                                                          FStar_Util.must
                                                         in
                                                      let vc1 =
                                                        let uu____7092 =
                                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                                            [u1] env
                                                            md_pure_or_ghost
                                                            trivial
                                                           in
                                                        let uu____7093 =
                                                          let uu____7094 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t1
                                                             in
                                                          let uu____7103 =
                                                            let uu____7114 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                wp1
                                                               in
                                                            [uu____7114]  in
                                                          uu____7094 ::
                                                            uu____7103
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7092
                                                          uu____7093 r1
                                                         in
                                                      let uu____7147 =
                                                        strengthen_comp env
                                                          FStar_Pervasives_Native.None
                                                          c23 vc1 bind_flags
                                                         in
                                                      (match uu____7147 with
                                                       | (c,g_s) ->
                                                           let uu____7162 =
                                                             FStar_TypeChecker_Env.conj_guards
                                                               [g_c1;
                                                               g_c2;
                                                               g2;
                                                               g_s]
                                                              in
                                                           (c, uu____7162))))
                                         in
                                      let uu____7163 =
                                        let t =
                                          FStar_Syntax_Util.comp_result c1
                                           in
                                        match comp_univ_opt c1 with
                                        | FStar_Pervasives_Native.None  ->
                                            let uu____7179 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env t
                                               in
                                            (uu____7179, t)
                                        | FStar_Pervasives_Native.Some u ->
                                            (u, t)
                                         in
                                      match uu____7163 with
                                      | (u_res_t1,res_t1) ->
                                          let uu____7195 =
                                            (FStar_Option.isSome b) &&
                                              (should_return env e1opt lc11)
                                             in
                                          if uu____7195
                                          then
                                            let e1 = FStar_Option.get e1opt
                                               in
                                            let x = FStar_Option.get b  in
                                            let uu____7204 =
                                              FStar_Syntax_Util.is_partial_return
                                                c1
                                               in
                                            (if uu____7204
                                             then
                                               (debug
                                                  (fun uu____7218  ->
                                                     let uu____7219 =
                                                       FStar_TypeChecker_Normalize.term_to_string
                                                         env e1
                                                        in
                                                     let uu____7221 =
                                                       FStar_Syntax_Print.bv_to_string
                                                         x
                                                        in
                                                     FStar_Util.print2
                                                       "(3) bind (case a): Substituting %s for %s"
                                                       uu____7219 uu____7221);
                                                (let c21 =
                                                   FStar_Syntax_Subst.subst_comp
                                                     [FStar_Syntax_Syntax.NT
                                                        (x, e1)] c2
                                                    in
                                                 let g =
                                                   let uu____7228 =
                                                     FStar_TypeChecker_Env.map_guard
                                                       g_c2
                                                       (FStar_Syntax_Subst.subst
                                                          [FStar_Syntax_Syntax.NT
                                                             (x, e1)])
                                                      in
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g_c1 uu____7228
                                                    in
                                                 mk_bind1 c1 b c21 g))
                                             else
                                               (let uu____7233 =
                                                  ((FStar_Options.vcgen_optimize_bind_as_seq
                                                      ())
                                                     &&
                                                     (lcomp_has_trivial_postcondition
                                                        lc11))
                                                    &&
                                                    (let uu____7236 =
                                                       FStar_TypeChecker_Env.try_lookup_lid
                                                         env
                                                         FStar_Parser_Const.with_type_lid
                                                        in
                                                     FStar_Option.isSome
                                                       uu____7236)
                                                   in
                                                if uu____7233
                                                then
                                                  let e1' =
                                                    let uu____7261 =
                                                      FStar_Options.vcgen_decorate_with_type
                                                        ()
                                                       in
                                                    if uu____7261
                                                    then
                                                      FStar_Syntax_Util.mk_with_type
                                                        u_res_t1 res_t1 e1
                                                    else e1  in
                                                  (debug
                                                     (fun uu____7273  ->
                                                        let uu____7274 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1'
                                                           in
                                                        let uu____7276 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case b): Substituting %s for %s"
                                                          uu____7274
                                                          uu____7276);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1')] c2
                                                       in
                                                    mk_seq c1 b c21))
                                                else
                                                  (debug
                                                     (fun uu____7291  ->
                                                        let uu____7292 =
                                                          FStar_TypeChecker_Normalize.term_to_string
                                                            env e1
                                                           in
                                                        let uu____7294 =
                                                          FStar_Syntax_Print.bv_to_string
                                                            x
                                                           in
                                                        FStar_Util.print2
                                                          "(3) bind (case c): Adding equality %s = %s"
                                                          uu____7292
                                                          uu____7294);
                                                   (let c21 =
                                                      FStar_Syntax_Subst.subst_comp
                                                        [FStar_Syntax_Syntax.NT
                                                           (x, e1)] c2
                                                       in
                                                    let x_eq_e =
                                                      let uu____7301 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x
                                                         in
                                                      FStar_Syntax_Util.mk_eq2
                                                        u_res_t1 res_t1 e1
                                                        uu____7301
                                                       in
                                                    let uu____7302 =
                                                      let uu____7307 =
                                                        let uu____7308 =
                                                          let uu____7309 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              x
                                                             in
                                                          [uu____7309]  in
                                                        FStar_TypeChecker_Env.push_binders
                                                          env uu____7308
                                                         in
                                                      weaken_comp uu____7307
                                                        c21 x_eq_e
                                                       in
                                                    match uu____7302 with
                                                    | (c22,g_w) ->
                                                        let g =
                                                          let uu____7335 =
                                                            let uu____7336 =
                                                              let uu____7337
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  x
                                                                 in
                                                              [uu____7337]
                                                               in
                                                            let uu____7356 =
                                                              FStar_TypeChecker_Common.weaken_guard_formula
                                                                g_c2 x_eq_e
                                                               in
                                                            FStar_TypeChecker_Env.close_guard
                                                              env uu____7336
                                                              uu____7356
                                                             in
                                                          FStar_TypeChecker_Env.conj_guard
                                                            g_c1 uu____7335
                                                           in
                                                        let uu____7357 =
                                                          mk_bind1 c1 b c22 g
                                                           in
                                                        (match uu____7357
                                                         with
                                                         | (c,g_bind) ->
                                                             let uu____7368 =
                                                               FStar_TypeChecker_Env.conj_guard
                                                                 g_w g_bind
                                                                in
                                                             (c, uu____7368))))))
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
      | uu____7385 -> g2
  
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
            (let uu____7409 =
               FStar_TypeChecker_Common.is_lcomp_partial_return lc  in
             Prims.op_Negation uu____7409)
           in
        let flags =
          if should_return1
          then
            let uu____7417 = FStar_TypeChecker_Common.is_total_lcomp lc  in
            (if uu____7417
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_TypeChecker_Common.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_TypeChecker_Common.cflags))
          else lc.FStar_TypeChecker_Common.cflags  in
        let refine uu____7435 =
          let uu____7436 = FStar_TypeChecker_Common.lcomp_comp lc  in
          match uu____7436 with
          | (c,g_c) ->
              let u_t =
                match comp_univ_opt c with
                | FStar_Pervasives_Native.Some u_t -> u_t
                | FStar_Pervasives_Native.None  ->
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Syntax_Util.comp_result c)
                 in
              let uu____7449 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
              if uu____7449
              then
                let retc =
                  return_value env (FStar_Pervasives_Native.Some u_t)
                    (FStar_Syntax_Util.comp_result c) e
                   in
                let uu____7457 =
                  let uu____7459 = FStar_Syntax_Util.is_pure_comp c  in
                  Prims.op_Negation uu____7459  in
                (if uu____7457
                 then
                   let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
                   let retc2 =
                     let uu___936_7468 = retc1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___936_7468.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         FStar_Parser_Const.effect_GHOST_lid;
                       FStar_Syntax_Syntax.result_typ =
                         (uu___936_7468.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___936_7468.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags = flags
                     }  in
                   let uu____7469 = FStar_Syntax_Syntax.mk_Comp retc2  in
                   (uu____7469, g_c)
                 else
                   (let uu____7472 =
                      FStar_Syntax_Util.comp_set_flags retc flags  in
                    (uu____7472, g_c)))
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
                   let uu____7483 =
                     let uu____7484 =
                       return_value env (FStar_Pervasives_Native.Some u_t) t
                         xexp
                        in
                     FStar_Syntax_Util.comp_set_flags uu____7484
                       [FStar_Syntax_Syntax.PARTIAL_RETURN]
                      in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____7483
                    in
                 let eq = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
                 let eq_ret =
                   weaken_precondition env ret
                     (FStar_TypeChecker_Common.NonTrivial eq)
                    in
                 let uu____7487 =
                   let uu____7492 =
                     let uu____7493 =
                       FStar_TypeChecker_Common.lcomp_of_comp c2  in
                     bind e.FStar_Syntax_Syntax.pos env
                       FStar_Pervasives_Native.None uu____7493
                       ((FStar_Pervasives_Native.Some x), eq_ret)
                      in
                   FStar_TypeChecker_Common.lcomp_comp uu____7492  in
                 match uu____7487 with
                 | (bind_c,g_bind) ->
                     let uu____7502 =
                       FStar_Syntax_Util.comp_set_flags bind_c flags  in
                     let uu____7503 =
                       FStar_TypeChecker_Env.conj_guard g_c g_bind  in
                     (uu____7502, uu____7503))
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
            fun uu____7539  ->
              match uu____7539 with
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
                    let uu____7551 =
                      ((let uu____7555 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____7555) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____7551
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____7573 =
        let uu____7574 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____7574  in
      FStar_Syntax_Syntax.fvar uu____7573 FStar_Syntax_Syntax.delta_constant
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
                  let conjunction_name =
                    let uu____7626 =
                      FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname
                       in
                    FStar_Util.format1 "%s.conjunction" uu____7626  in
                  let uu____7629 =
                    let uu____7634 =
                      let uu____7635 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator
                         in
                      FStar_All.pipe_right uu____7635 FStar_Util.must  in
                    FStar_TypeChecker_Env.inst_tscheme_with uu____7634 [u_a]
                     in
                  match uu____7629 with
                  | (uu____7646,conjunction) ->
                      let uu____7648 =
                        let uu____7657 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct1.FStar_Syntax_Syntax.effect_args
                           in
                        let uu____7672 =
                          FStar_List.map FStar_Pervasives_Native.fst
                            ct2.FStar_Syntax_Syntax.effect_args
                           in
                        (uu____7657, uu____7672)  in
                      (match uu____7648 with
                       | (is1,is2) ->
                           let conjunction_t_error s =
                             let uu____7718 =
                               let uu____7720 =
                                 FStar_Syntax_Print.term_to_string
                                   conjunction
                                  in
                               FStar_Util.format3
                                 "conjunction %s (%s) does not have proper shape (reason:%s)"
                                 uu____7720 conjunction_name s
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect,
                               uu____7718)
                              in
                           let uu____7724 =
                             let uu____7769 =
                               let uu____7770 =
                                 FStar_Syntax_Subst.compress conjunction  in
                               uu____7770.FStar_Syntax_Syntax.n  in
                             match uu____7769 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (bs,body,uu____7819) when
                                 (FStar_List.length bs) >= (Prims.of_int (4))
                                 ->
                                 let uu____7851 =
                                   FStar_Syntax_Subst.open_term bs body  in
                                 (match uu____7851 with
                                  | (a_b::bs1,body1) ->
                                      let uu____7923 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             (Prims.of_int (3))) bs1
                                         in
                                      (match uu____7923 with
                                       | (rest_bs,f_b::g_b::p_b::[]) ->
                                           let uu____8071 =
                                             FStar_All.pipe_right body1
                                               FStar_Syntax_Util.unascribe
                                              in
                                           (a_b, rest_bs, f_b, g_b, p_b,
                                             uu____8071)))
                             | uu____8104 ->
                                 let uu____8105 =
                                   conjunction_t_error
                                     "Either not an abstraction or not enough binders"
                                    in
                                 FStar_Errors.raise_error uu____8105 r
                              in
                           (match uu____7724 with
                            | (a_b,rest_bs,f_b,g_b,p_b,body) ->
                                let uu____8230 =
                                  let uu____8237 =
                                    let uu____8238 =
                                      let uu____8239 =
                                        let uu____8246 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____8246, a)  in
                                      FStar_Syntax_Syntax.NT uu____8239  in
                                    [uu____8238]  in
                                  FStar_TypeChecker_Env.uvars_for_binders env
                                    rest_bs uu____8237
                                    (fun b  ->
                                       let uu____8262 =
                                         FStar_Syntax_Print.binder_to_string
                                           b
                                          in
                                       let uu____8264 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname
                                          in
                                       let uu____8266 =
                                         FStar_All.pipe_right r
                                           FStar_Range.string_of_range
                                          in
                                       FStar_Util.format3
                                         "implicit var for binder %s of %s:conjunction at %s"
                                         uu____8262 uu____8264 uu____8266) r
                                   in
                                (match uu____8230 with
                                 | (rest_bs_uvars,g_uvars) ->
                                     let substs =
                                       FStar_List.map2
                                         (fun b  ->
                                            fun t  ->
                                              let uu____8304 =
                                                let uu____8311 =
                                                  FStar_All.pipe_right b
                                                    FStar_Pervasives_Native.fst
                                                   in
                                                (uu____8311, t)  in
                                              FStar_Syntax_Syntax.NT
                                                uu____8304) (a_b ::
                                         (FStar_List.append rest_bs [p_b]))
                                         (a ::
                                         (FStar_List.append rest_bs_uvars [p]))
                                        in
                                     let f_guard =
                                       let f_sort_is =
                                         let uu____8350 =
                                           let uu____8351 =
                                             let uu____8354 =
                                               let uu____8355 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8355.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8354
                                              in
                                           uu____8351.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8350 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8366,uu____8367::is) ->
                                             let uu____8409 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8409
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8442 ->
                                             let uu____8443 =
                                               conjunction_t_error
                                                 "f's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8443 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i1  ->
                                              fun f_i  ->
                                                let uu____8459 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i1 f_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8459)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is1 f_sort_is
                                        in
                                     let g_guard =
                                       let g_sort_is =
                                         let uu____8465 =
                                           let uu____8466 =
                                             let uu____8469 =
                                               let uu____8470 =
                                                 FStar_All.pipe_right g_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____8470.FStar_Syntax_Syntax.sort
                                                in
                                             FStar_Syntax_Subst.compress
                                               uu____8469
                                              in
                                           uu____8466.FStar_Syntax_Syntax.n
                                            in
                                         match uu____8465 with
                                         | FStar_Syntax_Syntax.Tm_app
                                             (uu____8481,uu____8482::is) ->
                                             let uu____8524 =
                                               FStar_All.pipe_right is
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_All.pipe_right uu____8524
                                               (FStar_List.map
                                                  (FStar_Syntax_Subst.subst
                                                     substs))
                                         | uu____8557 ->
                                             let uu____8558 =
                                               conjunction_t_error
                                                 "g's type is not a repr type"
                                                in
                                             FStar_Errors.raise_error
                                               uu____8558 r
                                          in
                                       FStar_List.fold_left2
                                         (fun g  ->
                                            fun i2  ->
                                              fun g_i  ->
                                                let uu____8574 =
                                                  FStar_TypeChecker_Rel.layered_effect_teq
                                                    env i2 g_i
                                                    (FStar_Pervasives_Native.Some
                                                       conjunction_name)
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  g uu____8574)
                                         FStar_TypeChecker_Env.trivial_guard
                                         is2 g_sort_is
                                        in
                                     let body1 =
                                       FStar_Syntax_Subst.subst substs body
                                        in
                                     let is =
                                       let uu____8580 =
                                         let uu____8581 =
                                           FStar_Syntax_Subst.compress body1
                                            in
                                         uu____8581.FStar_Syntax_Syntax.n  in
                                       match uu____8580 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____8586,a1::args) ->
                                           FStar_List.map
                                             FStar_Pervasives_Native.fst args
                                       | uu____8641 ->
                                           let uu____8642 =
                                             conjunction_t_error
                                               "body is not a repr type"
                                              in
                                           FStar_Errors.raise_error
                                             uu____8642 r
                                        in
                                     let uu____8651 =
                                       let uu____8652 =
                                         let uu____8653 =
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
                                             uu____8653;
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       FStar_Syntax_Syntax.mk_Comp uu____8652
                                        in
                                     let uu____8676 =
                                       let uu____8677 =
                                         FStar_TypeChecker_Env.conj_guard
                                           g_uvars f_guard
                                          in
                                       FStar_TypeChecker_Env.conj_guard
                                         uu____8677 g_guard
                                        in
                                     (uu____8651, uu____8676))))
  
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
                fun uu____8722  ->
                  let if_then_else =
                    let uu____8728 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_wp_if_then_else_combinator
                       in
                    FStar_All.pipe_right uu____8728 FStar_Util.must  in
                  let uu____8735 = destruct_wp_comp ct1  in
                  match uu____8735 with
                  | (uu____8746,uu____8747,wp_t) ->
                      let uu____8749 = destruct_wp_comp ct2  in
                      (match uu____8749 with
                       | (uu____8760,uu____8761,wp_e) ->
                           let wp =
                             let uu____8764 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 [u_a] env ed if_then_else
                                in
                             let uu____8765 =
                               let uu____8766 = FStar_Syntax_Syntax.as_arg a
                                  in
                               let uu____8775 =
                                 let uu____8786 =
                                   FStar_Syntax_Syntax.as_arg p  in
                                 let uu____8795 =
                                   let uu____8806 =
                                     FStar_Syntax_Syntax.as_arg wp_t  in
                                   let uu____8815 =
                                     let uu____8826 =
                                       FStar_Syntax_Syntax.as_arg wp_e  in
                                     [uu____8826]  in
                                   uu____8806 :: uu____8815  in
                                 uu____8786 :: uu____8795  in
                               uu____8766 :: uu____8775  in
                             let uu____8875 =
                               FStar_Range.union_ranges
                                 wp_t.FStar_Syntax_Syntax.pos
                                 wp_e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Syntax.mk_Tm_app uu____8764
                               uu____8765 uu____8875
                              in
                           let uu____8876 = mk_comp ed u_a a wp []  in
                           (uu____8876, FStar_TypeChecker_Env.trivial_guard))
  
let (comp_pure_wp_false :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        let post_k =
          let uu____8896 =
            let uu____8905 = FStar_Syntax_Syntax.null_binder t  in
            [uu____8905]  in
          let uu____8924 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8896 uu____8924  in
        let kwp =
          let uu____8930 =
            let uu____8939 = FStar_Syntax_Syntax.null_binder post_k  in
            [uu____8939]  in
          let uu____8958 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
          FStar_Syntax_Util.arrow uu____8930 uu____8958  in
        let post =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None post_k  in
        let wp =
          let uu____8965 =
            let uu____8966 = FStar_Syntax_Syntax.mk_binder post  in
            [uu____8966]  in
          let uu____8985 = fvar_const env FStar_Parser_Const.false_lid  in
          FStar_Syntax_Util.abs uu____8965 uu____8985
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
            let uu____9044 =
              let uu____9045 =
                FStar_All.pipe_right scrutinee FStar_Syntax_Syntax.mk_binder
                 in
              [uu____9045]  in
            FStar_TypeChecker_Env.push_binders env0 uu____9044  in
          let eff =
            FStar_List.fold_left
              (fun eff  ->
                 fun uu____9092  ->
                   match uu____9092 with
                   | (uu____9106,eff_label,uu____9108,uu____9109) ->
                       join_effects env eff eff_label)
              FStar_Parser_Const.effect_PURE_lid lcases
             in
          let uu____9122 =
            let uu____9130 =
              FStar_All.pipe_right lcases
                (FStar_Util.for_some
                   (fun uu____9168  ->
                      match uu____9168 with
                      | (uu____9183,uu____9184,flags,uu____9186) ->
                          FStar_All.pipe_right flags
                            (FStar_Util.for_some
                               (fun uu___5_9203  ->
                                  match uu___5_9203 with
                                  | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                      true
                                  | uu____9206 -> false))))
               in
            if uu____9130
            then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
            else (false, [])  in
          match uu____9122 with
          | (should_not_inline_whole_match,bind_cases_flags) ->
              let bind_cases uu____9243 =
                let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                   in
                let uu____9245 =
                  env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                   in
                if uu____9245
                then
                  let uu____9252 = lax_mk_tot_or_comp_l eff u_res_t res_t []
                     in
                  (uu____9252, FStar_TypeChecker_Env.trivial_guard)
                else
                  (let maybe_return eff_label_then cthen =
                     let uu____9273 =
                       should_not_inline_whole_match ||
                         (let uu____9276 = is_pure_or_ghost_effect env eff
                             in
                          Prims.op_Negation uu____9276)
                        in
                     if uu____9273 then cthen true else cthen false  in
                   let uu____9283 =
                     let uu____9294 =
                       let uu____9307 =
                         let uu____9312 =
                           let uu____9323 =
                             FStar_All.pipe_right lcases
                               (FStar_List.map
                                  (fun uu____9373  ->
                                     match uu____9373 with
                                     | (g,uu____9392,uu____9393,uu____9394)
                                         -> g))
                              in
                           FStar_All.pipe_right uu____9323
                             (FStar_List.fold_left
                                (fun uu____9442  ->
                                   fun g  ->
                                     match uu____9442 with
                                     | (conds,acc) ->
                                         let cond =
                                           let uu____9483 =
                                             FStar_Syntax_Util.mk_neg g  in
                                           FStar_Syntax_Util.mk_conj acc
                                             uu____9483
                                            in
                                         ((FStar_List.append conds [cond]),
                                           cond))
                                ([FStar_Syntax_Util.t_true],
                                  FStar_Syntax_Util.t_true))
                            in
                         FStar_All.pipe_right uu____9312
                           FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____9307
                         (fun l  ->
                            FStar_List.splitAt
                              ((FStar_List.length l) - Prims.int_one) l)
                        in
                     FStar_All.pipe_right uu____9294
                       (fun uu____9581  ->
                          match uu____9581 with
                          | (l1,l2) ->
                              let uu____9622 = FStar_List.hd l2  in
                              (l1, uu____9622))
                      in
                   match uu____9283 with
                   | (neg_branch_conds,exhaustiveness_branch_cond) ->
                       let uu____9651 =
                         match lcases with
                         | [] ->
                             let uu____9682 =
                               comp_pure_wp_false env u_res_t res_t  in
                             (FStar_Pervasives_Native.None, uu____9682,
                               FStar_TypeChecker_Env.trivial_guard)
                         | uu____9685 ->
                             let uu____9702 =
                               let uu____9735 =
                                 let uu____9746 =
                                   FStar_All.pipe_right neg_branch_conds
                                     (FStar_List.splitAt
                                        ((FStar_List.length lcases) -
                                           Prims.int_one))
                                    in
                                 FStar_All.pipe_right uu____9746
                                   (fun uu____9818  ->
                                      match uu____9818 with
                                      | (l1,l2) ->
                                          let uu____9859 = FStar_List.hd l2
                                             in
                                          (l1, uu____9859))
                                  in
                               match uu____9735 with
                               | (neg_branch_conds1,neg_last) ->
                                   let uu____9916 =
                                     let uu____9955 =
                                       FStar_All.pipe_right lcases
                                         (FStar_List.splitAt
                                            ((FStar_List.length lcases) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____9955
                                       (fun uu____10167  ->
                                          match uu____10167 with
                                          | (l1,l2) ->
                                              let uu____10318 =
                                                FStar_List.hd l2  in
                                              (l1, uu____10318))
                                      in
                                   (match uu____9916 with
                                    | (lcases1,(g_last,eff_last,uu____10420,c_last))
                                        ->
                                        let uu____10490 =
                                          let lc =
                                            maybe_return eff_last c_last  in
                                          let uu____10496 =
                                            FStar_TypeChecker_Common.lcomp_comp
                                              lc
                                             in
                                          match uu____10496 with
                                          | (c,g) ->
                                              let uu____10507 =
                                                let uu____10508 =
                                                  FStar_Syntax_Util.mk_conj
                                                    g_last neg_last
                                                   in
                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                  g uu____10508
                                                 in
                                              (c, uu____10507)
                                           in
                                        (match uu____10490 with
                                         | (c,g) ->
                                             let uu____10543 =
                                               let uu____10544 =
                                                 FStar_All.pipe_right
                                                   eff_last
                                                   (FStar_TypeChecker_Env.norm_eff_name
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____10544
                                                 (FStar_TypeChecker_Env.get_effect_decl
                                                    env)
                                                in
                                             (lcases1, neg_branch_conds1,
                                               uu____10543, c, g)))
                                in
                             (match uu____9702 with
                              | (lcases1,neg_branch_conds1,md,comp,g_comp) ->
                                  FStar_List.fold_right2
                                    (fun uu____10676  ->
                                       fun neg_cond  ->
                                         fun uu____10678  ->
                                           match (uu____10676, uu____10678)
                                           with
                                           | ((g,eff_label,uu____10738,cthen),
                                              (uu____10740,celse,g_comp1)) ->
                                               let uu____10787 =
                                                 let uu____10792 =
                                                   maybe_return eff_label
                                                     cthen
                                                    in
                                                 FStar_TypeChecker_Common.lcomp_comp
                                                   uu____10792
                                                  in
                                               (match uu____10787 with
                                                | (cthen1,g_then) ->
                                                    let uu____10803 =
                                                      let uu____10814 =
                                                        lift_comps_sep_guards
                                                          env cthen1 celse
                                                          FStar_Pervasives_Native.None
                                                          false
                                                         in
                                                      match uu____10814 with
                                                      | (m,cthen2,celse1,g_lift_then,g_lift_else)
                                                          ->
                                                          let md1 =
                                                            FStar_TypeChecker_Env.get_effect_decl
                                                              env m
                                                             in
                                                          let uu____10842 =
                                                            FStar_All.pipe_right
                                                              cthen2
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          let uu____10843 =
                                                            FStar_All.pipe_right
                                                              celse1
                                                              FStar_Syntax_Util.comp_to_comp_typ
                                                             in
                                                          (md1, uu____10842,
                                                            uu____10843,
                                                            g_lift_then,
                                                            g_lift_else)
                                                       in
                                                    (match uu____10803 with
                                                     | (md1,ct_then,ct_else,g_lift_then,g_lift_else)
                                                         ->
                                                         let fn =
                                                           let uu____10894 =
                                                             FStar_All.pipe_right
                                                               md1
                                                               FStar_Syntax_Util.is_layered
                                                              in
                                                           if uu____10894
                                                           then
                                                             mk_layered_conjunction
                                                           else
                                                             mk_non_layered_conjunction
                                                            in
                                                         let uu____10928 =
                                                           let uu____10933 =
                                                             FStar_TypeChecker_Env.get_range
                                                               env
                                                              in
                                                           fn env md1 u_res_t
                                                             res_t g ct_then
                                                             ct_else
                                                             uu____10933
                                                            in
                                                         (match uu____10928
                                                          with
                                                          | (c,g_conjunction)
                                                              ->
                                                              let g_then1 =
                                                                let uu____10945
                                                                  =
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_then
                                                                    g_lift_then
                                                                   in
                                                                let uu____10946
                                                                  =
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    g
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  uu____10945
                                                                  uu____10946
                                                                 in
                                                              let g_else =
                                                                let uu____10948
                                                                  =
                                                                  let uu____10949
                                                                    =
                                                                    FStar_Syntax_Util.mk_neg
                                                                    g  in
                                                                  FStar_Syntax_Util.mk_conj
                                                                    neg_cond
                                                                    uu____10949
                                                                   in
                                                                FStar_TypeChecker_Common.weaken_guard_formula
                                                                  g_lift_else
                                                                  uu____10948
                                                                 in
                                                              let uu____10952
                                                                =
                                                                FStar_TypeChecker_Env.conj_guards
                                                                  [g_comp1;
                                                                  g_then1;
                                                                  g_else;
                                                                  g_conjunction]
                                                                 in
                                                              ((FStar_Pervasives_Native.Some
                                                                  md1), c,
                                                                uu____10952)))))
                                    lcases1 neg_branch_conds1
                                    ((FStar_Pervasives_Native.Some md), comp,
                                      g_comp))
                          in
                       (match uu____9651 with
                        | (md,comp,g_comp) ->
                            let uu____10968 =
                              let uu____10973 =
                                let check =
                                  FStar_Syntax_Util.mk_imp
                                    exhaustiveness_branch_cond
                                    FStar_Syntax_Util.t_false
                                   in
                                let check1 =
                                  let uu____10980 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  label
                                    FStar_TypeChecker_Err.exhaustiveness_check
                                    uu____10980 check
                                   in
                                strengthen_comp env
                                  FStar_Pervasives_Native.None comp check1
                                  bind_cases_flags
                                 in
                              match uu____10973 with
                              | (c,g) ->
                                  let uu____10991 =
                                    FStar_TypeChecker_Env.conj_guard g_comp g
                                     in
                                  (c, uu____10991)
                               in
                            (match uu____10968 with
                             | (comp1,g_comp1) ->
                                 let g_comp2 =
                                   let uu____10999 =
                                     let uu____11000 =
                                       FStar_All.pipe_right scrutinee
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     [uu____11000]  in
                                   FStar_TypeChecker_Env.close_guard env0
                                     uu____10999 g_comp1
                                    in
                                 (match lcases with
                                  | [] -> (comp1, g_comp2)
                                  | uu____11043::[] -> (comp1, g_comp2)
                                  | uu____11086 ->
                                      let uu____11103 =
                                        let uu____11105 =
                                          FStar_All.pipe_right md
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____11105
                                          FStar_Syntax_Util.is_layered
                                         in
                                      if uu____11103
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
                                         let uu____11118 =
                                           destruct_wp_comp comp2  in
                                         match uu____11118 with
                                         | (uu____11129,uu____11130,wp) ->
                                             let ite_wp =
                                               let uu____11133 =
                                                 FStar_All.pipe_right md1
                                                   FStar_Syntax_Util.get_wp_ite_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11133 FStar_Util.must
                                                in
                                             let wp1 =
                                               let uu____11141 =
                                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                                   [u_res_t] env md1 ite_wp
                                                  in
                                               let uu____11142 =
                                                 let uu____11143 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     res_t
                                                    in
                                                 let uu____11152 =
                                                   let uu____11163 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       wp
                                                      in
                                                   [uu____11163]  in
                                                 uu____11143 :: uu____11152
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____11141 uu____11142
                                                 wp.FStar_Syntax_Syntax.pos
                                                in
                                             let uu____11196 =
                                               mk_comp md1 u_res_t res_t wp1
                                                 bind_cases_flags
                                                in
                                             (uu____11196, g_comp2))))))
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
          let uu____11231 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____11231 with
          | FStar_Pervasives_Native.None  ->
              if env.FStar_TypeChecker_Env.use_eq
              then
                let uu____11247 =
                  FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
                    env e c c'
                   in
                let uu____11253 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error uu____11247 uu____11253
              else
                (let uu____11262 =
                   FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                     env e c c'
                    in
                 let uu____11268 = FStar_TypeChecker_Env.get_range env  in
                 FStar_Errors.raise_error uu____11262 uu____11268)
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
          let uu____11293 =
            FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_name  in
          FStar_All.pipe_right uu____11293
            (FStar_TypeChecker_Env.norm_eff_name env)
           in
        let uu____11296 = FStar_Syntax_Util.is_pure_or_ghost_effect c_lid  in
        if uu____11296
        then u_res
        else
          (let is_total =
             let uu____11303 =
               FStar_TypeChecker_Env.lookup_effect_quals env c_lid  in
             FStar_All.pipe_right uu____11303
               (FStar_List.existsb
                  (fun q  -> q = FStar_Syntax_Syntax.TotalEffect))
              in
           if Prims.op_Negation is_total
           then FStar_Syntax_Syntax.U_zero
           else
             (let uu____11314 = FStar_TypeChecker_Env.effect_repr env c u_res
                 in
              match uu____11314 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11317 =
                    let uu____11323 =
                      let uu____11325 =
                        FStar_Syntax_Print.lid_to_string c_lid  in
                      FStar_Util.format1
                        "Effect %s is marked total but does not have a repr"
                        uu____11325
                       in
                    (FStar_Errors.Fatal_EffectCannotBeReified, uu____11323)
                     in
                  FStar_Errors.raise_error uu____11317
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
      let uu____11349 = destruct_wp_comp ct  in
      match uu____11349 with
      | (u_t,t,wp) ->
          let vc =
            let uu____11366 =
              let uu____11367 =
                let uu____11368 =
                  FStar_All.pipe_right md
                    FStar_Syntax_Util.get_wp_trivial_combinator
                   in
                FStar_All.pipe_right uu____11368 FStar_Util.must  in
              FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                uu____11367
               in
            let uu____11375 =
              let uu____11376 = FStar_Syntax_Syntax.as_arg t  in
              let uu____11385 =
                let uu____11396 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____11396]  in
              uu____11376 :: uu____11385  in
            let uu____11429 = FStar_TypeChecker_Env.get_range env  in
            FStar_Syntax_Syntax.mk_Tm_app uu____11366 uu____11375 uu____11429
             in
          let uu____11430 =
            FStar_All.pipe_left FStar_TypeChecker_Env.guard_of_guard_formula
              (FStar_TypeChecker_Common.NonTrivial vc)
             in
          (ct, vc, uu____11430)
  
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
                  let uu____11485 =
                    FStar_TypeChecker_Env.try_lookup_lid env f  in
                  match uu____11485 with
                  | FStar_Pervasives_Native.Some uu____11500 ->
                      ((let uu____11518 =
                          FStar_TypeChecker_Env.debug env
                            (FStar_Options.Other "Coercions")
                           in
                        if uu____11518
                        then
                          let uu____11522 = FStar_Ident.string_of_lid f  in
                          FStar_Util.print1 "Coercing with %s!\n" uu____11522
                        else ());
                       (let coercion =
                          let uu____11528 =
                            FStar_Ident.set_lid_range f
                              e.FStar_Syntax_Syntax.pos
                             in
                          FStar_Syntax_Syntax.fvar uu____11528
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_one) FStar_Pervasives_Native.None
                           in
                        let coercion1 =
                          FStar_Syntax_Syntax.mk_Tm_uinst coercion us  in
                        let coercion2 =
                          FStar_Syntax_Util.mk_app coercion1 eargs  in
                        let lc1 =
                          let uu____11535 =
                            let uu____11536 =
                              let uu____11537 = mkcomp ty  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____11537
                               in
                            (FStar_Pervasives_Native.None, uu____11536)  in
                          bind e.FStar_Syntax_Syntax.pos env
                            (FStar_Pervasives_Native.Some e) lc uu____11535
                           in
                        let e1 =
                          let uu____11541 =
                            let uu____11542 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____11542]  in
                          FStar_Syntax_Syntax.mk_Tm_app coercion2 uu____11541
                            e.FStar_Syntax_Syntax.pos
                           in
                        (e1, lc1)))
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____11576 =
                          let uu____11582 =
                            let uu____11584 = FStar_Ident.string_of_lid f  in
                            FStar_Util.format1
                              "Coercion %s was not found in the environment, not coercing."
                              uu____11584
                             in
                          (FStar_Errors.Warning_CoercionNotFound,
                            uu____11582)
                           in
                        FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
                          uu____11576);
                       (e, lc))
  
type isErased =
  | Yes of FStar_Syntax_Syntax.term 
  | Maybe 
  | No 
let (uu___is_Yes : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes _0 -> true | uu____11603 -> false
  
let (__proj__Yes__item___0 : isErased -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Yes _0 -> _0 
let (uu___is_Maybe : isErased -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____11621 -> false
  
let (uu___is_No : isErased -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____11632 -> false 
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
      let uu____11656 = FStar_Syntax_Util.head_and_args t2  in
      match uu____11656 with
      | (h,args) ->
          let h1 = FStar_Syntax_Util.un_uinst h  in
          let r =
            let uu____11701 =
              let uu____11716 =
                let uu____11717 = FStar_Syntax_Subst.compress h1  in
                uu____11717.FStar_Syntax_Syntax.n  in
              (uu____11716, args)  in
            match uu____11701 with
            | (FStar_Syntax_Syntax.Tm_fvar
               fv,(a,FStar_Pervasives_Native.None )::[]) when
                FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.erased_lid
                -> Yes a
            | (FStar_Syntax_Syntax.Tm_uvar uu____11764,uu____11765) -> Maybe
            | (FStar_Syntax_Syntax.Tm_unknown ,uu____11798) -> Maybe
            | (FStar_Syntax_Syntax.Tm_match
               (uu____11819,branches),uu____11821) ->
                FStar_All.pipe_right branches
                  (FStar_List.fold_left
                     (fun acc  ->
                        fun br  ->
                          match acc with
                          | Yes uu____11885 -> Maybe
                          | Maybe  -> Maybe
                          | No  ->
                              let uu____11886 =
                                FStar_Syntax_Subst.open_branch br  in
                              (match uu____11886 with
                               | (uu____11887,uu____11888,br_body) ->
                                   let uu____11906 =
                                     let uu____11907 =
                                       let uu____11912 =
                                         let uu____11913 =
                                           let uu____11916 =
                                             FStar_All.pipe_right br_body
                                               FStar_Syntax_Free.names
                                              in
                                           FStar_All.pipe_right uu____11916
                                             FStar_Util.set_elements
                                            in
                                         FStar_All.pipe_right uu____11913
                                           (FStar_TypeChecker_Env.push_bvs
                                              env)
                                          in
                                       check_erased uu____11912  in
                                     FStar_All.pipe_right br_body uu____11907
                                      in
                                   (match uu____11906 with
                                    | No  -> No
                                    | uu____11927 -> Maybe))) No)
            | uu____11928 -> No  in
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
            (((let uu____11980 = FStar_Options.use_two_phase_tc ()  in
               Prims.op_Negation uu____11980) ||
                env.FStar_TypeChecker_Env.phase1)
               || env.FStar_TypeChecker_Env.lax)
              || (FStar_Options.lax ())
             in
          if Prims.op_Negation should_coerce
          then (e, lc, FStar_TypeChecker_Env.trivial_guard)
          else
            (let is_t_term t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____11999 =
                 let uu____12000 = FStar_Syntax_Subst.compress t1  in
                 uu____12000.FStar_Syntax_Syntax.n  in
               match uu____11999 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_lid
               | uu____12005 -> false  in
             let is_t_term_view t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let uu____12015 =
                 let uu____12016 = FStar_Syntax_Subst.compress t1  in
                 uu____12016.FStar_Syntax_Syntax.n  in
               match uu____12015 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.term_view_lid
               | uu____12021 -> false  in
             let is_type t =
               let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
               let t2 = FStar_Syntax_Util.unrefine t1  in
               let uu____12032 =
                 let uu____12033 = FStar_Syntax_Subst.compress t2  in
                 uu____12033.FStar_Syntax_Syntax.n  in
               match uu____12032 with
               | FStar_Syntax_Syntax.Tm_type uu____12037 -> true
               | uu____12039 -> false  in
             let res_typ =
               FStar_Syntax_Util.unrefine lc.FStar_TypeChecker_Common.res_typ
                in
             let uu____12042 = FStar_Syntax_Util.head_and_args res_typ  in
             match uu____12042 with
             | (head,args) ->
                 ((let uu____12092 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "Coercions")
                      in
                   if uu____12092
                   then
                     let uu____12096 =
                       FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                        in
                     let uu____12098 = FStar_Syntax_Print.term_to_string e
                        in
                     let uu____12100 =
                       FStar_Syntax_Print.term_to_string res_typ  in
                     let uu____12102 =
                       FStar_Syntax_Print.term_to_string exp_t  in
                     FStar_Util.print4
                       "(%s) Trying to coerce %s from type (%s) to type (%s)\n"
                       uu____12096 uu____12098 uu____12100 uu____12102
                   else ());
                  (let mk_erased u t =
                     let uu____12120 =
                       let uu____12123 =
                         fvar_const env FStar_Parser_Const.erased_lid  in
                       FStar_Syntax_Syntax.mk_Tm_uinst uu____12123 [u]  in
                     let uu____12124 =
                       let uu____12135 = FStar_Syntax_Syntax.as_arg t  in
                       [uu____12135]  in
                     FStar_Syntax_Util.mk_app uu____12120 uu____12124  in
                   let uu____12160 =
                     let uu____12175 =
                       let uu____12176 = FStar_Syntax_Util.un_uinst head  in
                       uu____12176.FStar_Syntax_Syntax.n  in
                     (uu____12175, args)  in
                   match uu____12160 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.bool_lid)
                         && (is_type exp_t)
                       ->
                       let uu____12214 =
                         coerce_with env e lc FStar_Syntax_Util.ktype0
                           FStar_Parser_Const.b2t_lid [] []
                           FStar_Syntax_Syntax.mk_Total
                          in
                       (match uu____12214 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_lid)
                         && (is_t_term_view exp_t)
                       ->
                       let uu____12254 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                           FStar_Parser_Const.inspect [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12254 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.term_view_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12294 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.pack [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12294 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.binder_lid)
                         && (is_t_term exp_t)
                       ->
                       let uu____12334 =
                         coerce_with env e lc FStar_Syntax_Syntax.t_term
                           FStar_Parser_Const.binder_to_term [] []
                           FStar_Syntax_Syntax.mk_Tac
                          in
                       (match uu____12334 with
                        | (e1,lc1) ->
                            (e1, lc1, FStar_TypeChecker_Env.trivial_guard))
                   | uu____12355 ->
                       let uu____12370 =
                         let uu____12375 = check_erased env res_typ  in
                         let uu____12376 = check_erased env exp_t  in
                         (uu____12375, uu____12376)  in
                       (match uu____12370 with
                        | (No ,Yes ty) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12385 =
                              FStar_TypeChecker_Rel.get_subtyping_predicate
                                env res_typ ty
                               in
                            (match uu____12385 with
                             | FStar_Pervasives_Native.None  ->
                                 (e, lc, FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   FStar_TypeChecker_Env.apply_guard g e  in
                                 let uu____12396 =
                                   let uu____12401 =
                                     let uu____12402 =
                                       FStar_Syntax_Syntax.iarg ty  in
                                     [uu____12402]  in
                                   coerce_with env e lc exp_t
                                     FStar_Parser_Const.hide [u] uu____12401
                                     FStar_Syntax_Syntax.mk_Total
                                    in
                                 (match uu____12396 with
                                  | (e1,lc1) -> (e1, lc1, g1)))
                        | (Yes ty,No ) ->
                            let u =
                              env.FStar_TypeChecker_Env.universe_of env ty
                               in
                            let uu____12437 =
                              let uu____12442 =
                                let uu____12443 = FStar_Syntax_Syntax.iarg ty
                                   in
                                [uu____12443]  in
                              coerce_with env e lc ty
                                FStar_Parser_Const.reveal [u] uu____12442
                                FStar_Syntax_Syntax.mk_GTotal
                               in
                            (match uu____12437 with
                             | (e1,lc1) ->
                                 (e1, lc1,
                                   FStar_TypeChecker_Env.trivial_guard))
                        | uu____12476 ->
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
        let uu____12511 = FStar_Syntax_Util.head_and_args rt1  in
        match uu____12511 with
        | (hd,args) ->
            let uu____12560 =
              let uu____12575 =
                let uu____12576 = FStar_Syntax_Subst.compress hd  in
                uu____12576.FStar_Syntax_Syntax.n  in
              (uu____12575, args)  in
            (match uu____12560 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.term_lid
                 ->
                 let uu____12614 =
                   coerce_with env e lc FStar_Syntax_Syntax.t_term_view
                     FStar_Parser_Const.inspect [] []
                     FStar_Syntax_Syntax.mk_Tac
                    in
                 FStar_All.pipe_left
                   (fun uu____12641  ->
                      FStar_Pervasives_Native.Some uu____12641) uu____12614
             | uu____12642 -> FStar_Pervasives_Native.None)
  
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
          (let uu____12695 =
             FStar_TypeChecker_Env.debug env FStar_Options.High  in
           if uu____12695
           then
             let uu____12698 = FStar_Syntax_Print.term_to_string e  in
             let uu____12700 = FStar_TypeChecker_Common.lcomp_to_string lc
                in
             let uu____12702 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print3 "weaken_result_typ e=(%s) lc=(%s) t=(%s)\n"
               uu____12698 uu____12700 uu____12702
           else ());
          (let use_eq =
             (env.FStar_TypeChecker_Env.use_eq_strict ||
                env.FStar_TypeChecker_Env.use_eq)
               ||
               (let uu____12712 =
                  FStar_TypeChecker_Env.effect_decl_opt env
                    lc.FStar_TypeChecker_Common.eff_name
                   in
                match uu____12712 with
                | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                    FStar_All.pipe_right qualifiers
                      (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                | uu____12737 -> false)
              in
           let gopt =
             if use_eq
             then
               let uu____12763 =
                 FStar_TypeChecker_Rel.try_teq true env
                   lc.FStar_TypeChecker_Common.res_typ t
                  in
               (uu____12763, false)
             else
               (let uu____12773 =
                  FStar_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStar_TypeChecker_Common.res_typ t
                   in
                (uu____12773, true))
              in
           match gopt with
           | (FStar_Pervasives_Native.None ,uu____12786) ->
               if env.FStar_TypeChecker_Env.failhard
               then
                 let uu____12798 =
                   FStar_TypeChecker_Err.basic_type_error env
                     (FStar_Pervasives_Native.Some e) t
                     lc.FStar_TypeChecker_Common.res_typ
                    in
                 FStar_Errors.raise_error uu____12798
                   e.FStar_Syntax_Syntax.pos
               else
                 (FStar_TypeChecker_Rel.subtype_fail env e
                    lc.FStar_TypeChecker_Common.res_typ t;
                  (e,
                    ((let uu___1424_12814 = lc  in
                      {
                        FStar_TypeChecker_Common.eff_name =
                          (uu___1424_12814.FStar_TypeChecker_Common.eff_name);
                        FStar_TypeChecker_Common.res_typ = t;
                        FStar_TypeChecker_Common.cflags =
                          (uu___1424_12814.FStar_TypeChecker_Common.cflags);
                        FStar_TypeChecker_Common.comp_thunk =
                          (uu___1424_12814.FStar_TypeChecker_Common.comp_thunk)
                      })), FStar_TypeChecker_Env.trivial_guard))
           | (FStar_Pervasives_Native.Some g,apply_guard) ->
               let uu____12821 = FStar_TypeChecker_Env.guard_form g  in
               (match uu____12821 with
                | FStar_TypeChecker_Common.Trivial  ->
                    let strengthen_trivial uu____12837 =
                      let uu____12838 =
                        FStar_TypeChecker_Common.lcomp_comp lc  in
                      match uu____12838 with
                      | (c,g_c) ->
                          let res_t = FStar_Syntax_Util.comp_result c  in
                          let set_result_typ c1 =
                            FStar_Syntax_Util.set_result_typ c1 t  in
                          let uu____12858 =
                            let uu____12860 = FStar_Syntax_Util.eq_tm t res_t
                               in
                            uu____12860 = FStar_Syntax_Util.Equal  in
                          if uu____12858
                          then
                            ((let uu____12867 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____12867
                              then
                                let uu____12871 =
                                  FStar_Syntax_Print.term_to_string res_t  in
                                let uu____12873 =
                                  FStar_Syntax_Print.term_to_string t  in
                                FStar_Util.print2
                                  "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                                  uu____12871 uu____12873
                              else ());
                             (let uu____12878 = set_result_typ c  in
                              (uu____12878, g_c)))
                          else
                            (let is_res_t_refinement =
                               let res_t1 =
                                 FStar_TypeChecker_Normalize.normalize_refinement
                                   FStar_TypeChecker_Normalize.whnf_steps env
                                   res_t
                                  in
                               match res_t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_refine uu____12885 ->
                                   true
                               | uu____12893 -> false  in
                             if is_res_t_refinement
                             then
                               let x =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (res_t.FStar_Syntax_Syntax.pos)) res_t
                                  in
                               let cret =
                                 let uu____12902 =
                                   FStar_Syntax_Syntax.bv_to_name x  in
                                 return_value env (comp_univ_opt c) res_t
                                   uu____12902
                                  in
                               let lc1 =
                                 let uu____12904 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 let uu____12905 =
                                   let uu____12906 =
                                     FStar_TypeChecker_Common.lcomp_of_comp
                                       cret
                                      in
                                   ((FStar_Pervasives_Native.Some x),
                                     uu____12906)
                                    in
                                 bind e.FStar_Syntax_Syntax.pos env
                                   (FStar_Pervasives_Native.Some e)
                                   uu____12904 uu____12905
                                  in
                               ((let uu____12910 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12910
                                 then
                                   let uu____12914 =
                                     FStar_Syntax_Print.term_to_string e  in
                                   let uu____12916 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   let uu____12918 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   let uu____12920 =
                                     FStar_TypeChecker_Common.lcomp_to_string
                                       lc1
                                      in
                                   FStar_Util.print4
                                     "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                     uu____12914 uu____12916 uu____12918
                                     uu____12920
                                 else ());
                                (let uu____12925 =
                                   FStar_TypeChecker_Common.lcomp_comp lc1
                                    in
                                 match uu____12925 with
                                 | (c1,g_lc) ->
                                     let uu____12936 = set_result_typ c1  in
                                     let uu____12937 =
                                       FStar_TypeChecker_Env.conj_guard g_c
                                         g_lc
                                        in
                                     (uu____12936, uu____12937)))
                             else
                               ((let uu____12941 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____12941
                                 then
                                   let uu____12945 =
                                     FStar_Syntax_Print.term_to_string res_t
                                      in
                                   let uu____12947 =
                                     FStar_Syntax_Print.comp_to_string c  in
                                   FStar_Util.print2
                                     "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                                     uu____12945 uu____12947
                                 else ());
                                (let uu____12952 = set_result_typ c  in
                                 (uu____12952, g_c))))
                       in
                    let lc1 =
                      FStar_TypeChecker_Common.mk_lcomp
                        lc.FStar_TypeChecker_Common.eff_name t
                        lc.FStar_TypeChecker_Common.cflags strengthen_trivial
                       in
                    (e, lc1, g)
                | FStar_TypeChecker_Common.NonTrivial f ->
                    let g1 =
                      let uu___1461_12956 = g  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1461_12956.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1461_12956.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1461_12956.FStar_TypeChecker_Common.implicits)
                      }  in
                    let strengthen uu____12966 =
                      let uu____12967 =
                        env.FStar_TypeChecker_Env.lax &&
                          (FStar_Options.ml_ish ())
                         in
                      if uu____12967
                      then FStar_TypeChecker_Common.lcomp_comp lc
                      else
                        (let f1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Beta;
                             FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env f
                            in
                         let uu____12977 =
                           let uu____12978 = FStar_Syntax_Subst.compress f1
                              in
                           uu____12978.FStar_Syntax_Syntax.n  in
                         match uu____12977 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (uu____12985,{
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12987;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12988;_},uu____12989)
                             when
                             FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.true_lid
                             ->
                             let lc1 =
                               let uu___1477_13015 = lc  in
                               {
                                 FStar_TypeChecker_Common.eff_name =
                                   (uu___1477_13015.FStar_TypeChecker_Common.eff_name);
                                 FStar_TypeChecker_Common.res_typ = t;
                                 FStar_TypeChecker_Common.cflags =
                                   (uu___1477_13015.FStar_TypeChecker_Common.cflags);
                                 FStar_TypeChecker_Common.comp_thunk =
                                   (uu___1477_13015.FStar_TypeChecker_Common.comp_thunk)
                               }  in
                             FStar_TypeChecker_Common.lcomp_comp lc1
                         | uu____13016 ->
                             let uu____13017 =
                               FStar_TypeChecker_Common.lcomp_comp lc  in
                             (match uu____13017 with
                              | (c,g_c) ->
                                  ((let uu____13029 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____13029
                                    then
                                      let uu____13033 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env
                                          lc.FStar_TypeChecker_Common.res_typ
                                         in
                                      let uu____13035 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env t
                                         in
                                      let uu____13037 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c
                                         in
                                      let uu____13039 =
                                        FStar_TypeChecker_Normalize.term_to_string
                                          env f1
                                         in
                                      FStar_Util.print4
                                        "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                        uu____13033 uu____13035 uu____13037
                                        uu____13039
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
                                        let uu____13052 =
                                          let uu____13053 =
                                            FStar_Syntax_Syntax.as_arg xexp
                                             in
                                          [uu____13053]  in
                                        FStar_Syntax_Syntax.mk_Tm_app f1
                                          uu____13052
                                          f1.FStar_Syntax_Syntax.pos
                                      else f1  in
                                    let uu____13080 =
                                      let uu____13085 =
                                        FStar_All.pipe_left
                                          (fun uu____13106  ->
                                             FStar_Pervasives_Native.Some
                                               uu____13106)
                                          (FStar_TypeChecker_Err.subtyping_failed
                                             env
                                             lc.FStar_TypeChecker_Common.res_typ
                                             t)
                                         in
                                      let uu____13107 =
                                        FStar_TypeChecker_Env.set_range env
                                          e.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____13108 =
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                          cret
                                         in
                                      let uu____13109 =
                                        FStar_All.pipe_left
                                          FStar_TypeChecker_Env.guard_of_guard_formula
                                          (FStar_TypeChecker_Common.NonTrivial
                                             guard)
                                         in
                                      strengthen_precondition uu____13085
                                        uu____13107 e uu____13108 uu____13109
                                       in
                                    match uu____13080 with
                                    | (eq_ret,_trivial_so_ok_to_discard) ->
                                        let x1 =
                                          let uu___1495_13117 = x  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___1495_13117.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___1495_13117.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort =
                                              (lc.FStar_TypeChecker_Common.res_typ)
                                          }  in
                                        let c1 =
                                          let uu____13119 =
                                            FStar_TypeChecker_Common.lcomp_of_comp
                                              c
                                             in
                                          bind e.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some e)
                                            uu____13119
                                            ((FStar_Pervasives_Native.Some x1),
                                              eq_ret)
                                           in
                                        let uu____13122 =
                                          FStar_TypeChecker_Common.lcomp_comp
                                            c1
                                           in
                                        (match uu____13122 with
                                         | (c2,g_lc) ->
                                             ((let uu____13134 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   FStar_Options.Extreme
                                                  in
                                               if uu____13134
                                               then
                                                 let uu____13138 =
                                                   FStar_TypeChecker_Normalize.comp_to_string
                                                     env c2
                                                    in
                                                 FStar_Util.print1
                                                   "Strengthened to %s\n"
                                                   uu____13138
                                               else ());
                                              (let uu____13143 =
                                                 FStar_TypeChecker_Env.conj_guard
                                                   g_c g_lc
                                                  in
                                               (c2, uu____13143))))))))
                       in
                    let flags =
                      FStar_All.pipe_right lc.FStar_TypeChecker_Common.cflags
                        (FStar_List.collect
                           (fun uu___6_13152  ->
                              match uu___6_13152 with
                              | FStar_Syntax_Syntax.RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                  [FStar_Syntax_Syntax.PARTIAL_RETURN]
                              | FStar_Syntax_Syntax.CPS  ->
                                  [FStar_Syntax_Syntax.CPS]
                              | uu____13155 -> []))
                       in
                    let lc1 =
                      let uu____13157 =
                        FStar_TypeChecker_Env.norm_eff_name env
                          lc.FStar_TypeChecker_Common.eff_name
                         in
                      FStar_TypeChecker_Common.mk_lcomp uu____13157 t flags
                        strengthen
                       in
                    let g2 =
                      let uu___1511_13159 = g1  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          FStar_TypeChecker_Common.Trivial;
                        FStar_TypeChecker_Common.deferred =
                          (uu___1511_13159.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___1511_13159.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits =
                          (uu___1511_13159.FStar_TypeChecker_Common.implicits)
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
        let uu____13195 =
          let uu____13198 =
            let uu____13199 =
              let uu____13208 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_Syntax_Syntax.as_arg uu____13208  in
            [uu____13199]  in
          FStar_Syntax_Syntax.mk_Tm_app ens uu____13198
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____13195  in
      let norm t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.EraseUniverses] env t
         in
      let uu____13231 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____13231
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____13250 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____13266 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____13283 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____13283
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____13299)::(ens,uu____13301)::uu____13302 ->
                    let uu____13345 =
                      let uu____13348 = norm req  in
                      FStar_Pervasives_Native.Some uu____13348  in
                    let uu____13349 =
                      let uu____13350 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm uu____13350  in
                    (uu____13345, uu____13349)
                | uu____13353 ->
                    let uu____13364 =
                      let uu____13370 =
                        let uu____13372 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____13372
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____13370)
                       in
                    FStar_Errors.raise_error uu____13364
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____13392)::uu____13393 ->
                    let uu____13420 =
                      let uu____13425 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____13425
                       in
                    (match uu____13420 with
                     | (us_r,uu____13457) ->
                         let uu____13458 =
                           let uu____13463 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____13463
                            in
                         (match uu____13458 with
                          | (us_e,uu____13495) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____13498 =
                                  let uu____13499 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13499
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13498
                                  us_r
                                 in
                              let as_ens =
                                let uu____13501 =
                                  let uu____13502 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____13502
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____13501
                                  us_e
                                 in
                              let req =
                                let uu____13504 =
                                  let uu____13505 =
                                    let uu____13516 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13516]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13505
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_req
                                  uu____13504
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____13554 =
                                  let uu____13555 =
                                    let uu____13566 =
                                      FStar_Syntax_Syntax.as_arg wp  in
                                    [uu____13566]  in
                                  ((ct1.FStar_Syntax_Syntax.result_typ),
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.imp_tag))
                                    :: uu____13555
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app as_ens
                                  uu____13554
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____13603 =
                                let uu____13606 = norm req  in
                                FStar_Pervasives_Native.Some uu____13606  in
                              let uu____13607 =
                                let uu____13608 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm uu____13608  in
                              (uu____13603, uu____13607)))
                | uu____13611 -> failwith "Impossible"))
  
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
        (let uu____13650 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____13650
         then
           let uu____13655 = FStar_Syntax_Print.term_to_string tm  in
           let uu____13657 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____13655
             uu____13657
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
              head.FStar_Syntax_Syntax.pos
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
          (let uu____13716 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "SMTEncodingReify")
              in
           if uu____13716
           then
             let uu____13721 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13723 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print2 "Reified body %s \nto %s\n" uu____13721
               uu____13723
           else ());
          tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____13734 =
      let uu____13736 =
        let uu____13737 = FStar_Syntax_Subst.compress t  in
        uu____13737.FStar_Syntax_Syntax.n  in
      match uu____13736 with
      | FStar_Syntax_Syntax.Tm_app uu____13741 -> false
      | uu____13759 -> true  in
    if uu____13734
    then t
    else
      (let uu____13764 = FStar_Syntax_Util.head_and_args t  in
       match uu____13764 with
       | (head,args) ->
           let uu____13807 =
             let uu____13809 =
               let uu____13810 = FStar_Syntax_Subst.compress head  in
               uu____13810.FStar_Syntax_Syntax.n  in
             match uu____13809 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____13815 -> false  in
           if uu____13807
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____13847 ->
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
          ((let uu____13894 =
              FStar_TypeChecker_Env.debug env FStar_Options.High  in
            if uu____13894
            then
              let uu____13897 = FStar_Syntax_Print.term_to_string e  in
              let uu____13899 = FStar_Syntax_Print.term_to_string t  in
              let uu____13901 =
                let uu____13903 = FStar_TypeChecker_Env.expected_typ env  in
                FStar_Common.string_of_option
                  FStar_Syntax_Print.term_to_string uu____13903
                 in
              FStar_Util.print3
                "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
                uu____13897 uu____13899 uu____13901
            else ());
           (let unfolded_arrow_formals t1 =
              let rec aux bs t2 =
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf env t2  in
                let uu____13939 = FStar_Syntax_Util.arrow_formals t3  in
                match uu____13939 with
                | (bs',t4) ->
                    (match bs' with
                     | [] -> bs
                     | bs'1 -> aux (FStar_List.append bs bs'1) t4)
                 in
              aux [] t1  in
            let number_of_implicits t1 =
              let formals = unfolded_arrow_formals t1  in
              let n_implicits =
                let uu____13973 =
                  FStar_All.pipe_right formals
                    (FStar_Util.prefix_until
                       (fun uu____14051  ->
                          match uu____14051 with
                          | (uu____14059,imp) ->
                              (FStar_Option.isNone imp) ||
                                (let uu____14066 =
                                   FStar_Syntax_Util.eq_aqual imp
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Equality)
                                    in
                                 uu____14066 = FStar_Syntax_Util.Equal)))
                   in
                match uu____13973 with
                | FStar_Pervasives_Native.None  -> FStar_List.length formals
                | FStar_Pervasives_Native.Some
                    (implicits,_first_explicit,_rest) ->
                    FStar_List.length implicits
                 in
              n_implicits  in
            let inst_n_binders t1 =
              let uu____14185 = FStar_TypeChecker_Env.expected_typ env  in
              match uu____14185 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expected_t ->
                  let n_expected = number_of_implicits expected_t  in
                  let n_available = number_of_implicits t1  in
                  if n_available < n_expected
                  then
                    let uu____14199 =
                      let uu____14205 =
                        let uu____14207 = FStar_Util.string_of_int n_expected
                           in
                        let uu____14209 = FStar_Syntax_Print.term_to_string e
                           in
                        let uu____14211 =
                          FStar_Util.string_of_int n_available  in
                        FStar_Util.format3
                          "Expected a term with %s implicit arguments, but %s has only %s"
                          uu____14207 uu____14209 uu____14211
                         in
                      (FStar_Errors.Fatal_MissingImplicitArguments,
                        uu____14205)
                       in
                    let uu____14215 = FStar_TypeChecker_Env.get_range env  in
                    FStar_Errors.raise_error uu____14199 uu____14215
                  else
                    FStar_Pervasives_Native.Some (n_available - n_expected)
               in
            let decr_inst uu___7_14233 =
              match uu___7_14233 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some i ->
                  FStar_Pervasives_Native.Some (i - Prims.int_one)
               in
            let t1 = FStar_TypeChecker_Normalize.unfold_whnf env t  in
            match t1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let uu____14276 = FStar_Syntax_Subst.open_comp bs c  in
                (match uu____14276 with
                 | (bs1,c1) ->
                     let rec aux subst inst_n bs2 =
                       match (inst_n, bs2) with
                       | (FStar_Pervasives_Native.Some
                          uu____14407,uu____14394) when
                           uu____14407 = Prims.int_zero ->
                           ([], bs2, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                       | (uu____14440,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Implicit
                                       uu____14442))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14476 =
                             new_implicit_var
                               "Instantiation of implicit argument"
                               e.FStar_Syntax_Syntax.pos env t2
                              in
                           (match uu____14476 with
                            | (v,uu____14517,g) ->
                                ((let uu____14532 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14532
                                  then
                                    let uu____14535 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating implicit with %s\n"
                                      uu____14535
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14545 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14545 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14638 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14638))))
                       | (uu____14665,(x,FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Syntax.Meta tau))::rest)
                           ->
                           let t2 =
                             FStar_Syntax_Subst.subst subst
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____14702 =
                             let uu____14715 =
                               let uu____14722 =
                                 let uu____14727 = FStar_Dyn.mkdyn env  in
                                 (uu____14727, tau)  in
                               FStar_Pervasives_Native.Some uu____14722  in
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               "Instantiation of meta argument"
                               e.FStar_Syntax_Syntax.pos env t2
                               FStar_Syntax_Syntax.Strict uu____14715
                              in
                           (match uu____14702 with
                            | (v,uu____14760,g) ->
                                ((let uu____14775 =
                                    FStar_TypeChecker_Env.debug env
                                      FStar_Options.High
                                     in
                                  if uu____14775
                                  then
                                    let uu____14778 =
                                      FStar_Syntax_Print.term_to_string v  in
                                    FStar_Util.print1
                                      "maybe_instantiate: Instantiating meta argument with %s\n"
                                      uu____14778
                                  else ());
                                 (let subst1 =
                                    (FStar_Syntax_Syntax.NT (x, v)) :: subst
                                     in
                                  let uu____14788 =
                                    aux subst1 (decr_inst inst_n) rest  in
                                  match uu____14788 with
                                  | (args,bs3,subst2,g') ->
                                      let uu____14881 =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      (((v,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag)) ::
                                        args), bs3, subst2, uu____14881))))
                       | (uu____14908,bs3) ->
                           ([], bs3, subst,
                             FStar_TypeChecker_Env.trivial_guard)
                        in
                     let uu____14956 =
                       let uu____14983 = inst_n_binders t1  in
                       aux [] uu____14983 bs1  in
                     (match uu____14956 with
                      | (args,bs2,subst,guard) ->
                          (match (args, bs2) with
                           | ([],uu____15055) -> (e, torig, guard)
                           | (uu____15086,[]) when
                               let uu____15117 =
                                 FStar_Syntax_Util.is_total_comp c1  in
                               Prims.op_Negation uu____15117 ->
                               (e, torig,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____15119 ->
                               let t2 =
                                 match bs2 with
                                 | [] -> FStar_Syntax_Util.comp_result c1
                                 | uu____15147 ->
                                     FStar_Syntax_Util.arrow bs2 c1
                                  in
                               let t3 = FStar_Syntax_Subst.subst subst t2  in
                               let e1 =
                                 FStar_Syntax_Syntax.mk_Tm_app e args
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               (e1, t3, guard))))
            | uu____15158 -> (e, torig, FStar_TypeChecker_Env.trivial_guard)))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs  ->
    let uu____15170 =
      let uu____15174 = FStar_Util.set_elements univs  in
      FStar_All.pipe_right uu____15174
        (FStar_List.map
           (fun u  ->
              let uu____15186 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____15186 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____15170 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____15214 = FStar_Util.set_is_empty x  in
      if uu____15214
      then []
      else
        (let s =
           let uu____15234 =
             let uu____15237 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____15237  in
           FStar_All.pipe_right uu____15234 FStar_Util.set_elements  in
         (let uu____15255 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____15255
          then
            let uu____15260 =
              let uu____15262 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____15262  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____15260
          else ());
         (let r =
            let uu____15271 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____15271  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____15316 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____15316
                     then
                       let uu____15321 =
                         let uu____15323 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____15323
                          in
                       let uu____15327 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____15329 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____15321 uu____15327 uu____15329
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
        let uu____15359 =
          FStar_Util.set_difference tm_univnames ctx_univnames  in
        FStar_All.pipe_right uu____15359 FStar_Util.set_elements  in
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
        | ([],uu____15398) -> generalized_univ_names
        | (uu____15405,[]) -> explicit_univ_names
        | uu____15412 ->
            let uu____15421 =
              let uu____15427 =
                let uu____15429 = FStar_Syntax_Print.term_to_string t  in
                Prims.op_Hat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____15429
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____15427)
               in
            FStar_Errors.raise_error uu____15421 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____15451 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____15451
       then
         let uu____15456 = FStar_Syntax_Print.term_to_string t  in
         let uu____15458 = FStar_Syntax_Print.univ_names_to_string univnames
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____15456 uu____15458
       else ());
      (let univs = FStar_Syntax_Free.univs t  in
       (let uu____15467 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____15467
        then
          let uu____15472 = string_of_univs univs  in
          FStar_Util.print1 "univs to gen : %s\n" uu____15472
        else ());
       (let gen = gen_univs env univs  in
        (let uu____15481 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____15481
         then
           let uu____15486 = FStar_Syntax_Print.term_to_string t  in
           let uu____15488 = FStar_Syntax_Print.univ_names_to_string gen  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____15486 uu____15488
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
        let uu____15572 =
          let uu____15574 =
            FStar_Util.for_all
              (fun uu____15588  ->
                 match uu____15588 with
                 | (uu____15598,uu____15599,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____15574  in
        if uu____15572
        then FStar_Pervasives_Native.None
        else
          (let norm c =
             (let uu____15651 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____15651
              then
                let uu____15654 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____15654
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets] env c
                 in
              (let uu____15661 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____15661
               then
                 let uu____15664 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____15664
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____15682 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____15682 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____15716 =
             match uu____15716 with
             | (lbname,e,c) ->
                 let c1 = norm c  in
                 let t = FStar_Syntax_Util.comp_result c1  in
                 let univs = FStar_Syntax_Free.univs t  in
                 let uvt = FStar_Syntax_Free.uvars t  in
                 ((let uu____15753 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____15753
                   then
                     let uu____15758 =
                       let uu____15760 =
                         let uu____15764 = FStar_Util.set_elements univs  in
                         FStar_All.pipe_right uu____15764
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____15760
                         (FStar_String.concat ", ")
                        in
                     let uu____15820 =
                       let uu____15822 =
                         let uu____15826 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____15826
                           (FStar_List.map
                              (fun u  ->
                                 let uu____15839 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____15841 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____15839
                                   uu____15841))
                          in
                       FStar_All.pipe_right uu____15822
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____15758
                       uu____15820
                   else ());
                  (let univs1 =
                     let uu____15855 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs1  ->
                          fun uv  ->
                            let uu____15867 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs1 uu____15867) univs
                       uu____15855
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____15874 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____15874
                    then
                      let uu____15879 =
                        let uu____15881 =
                          let uu____15885 = FStar_Util.set_elements univs1
                             in
                          FStar_All.pipe_right uu____15885
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____15881
                          (FStar_String.concat ", ")
                         in
                      let uu____15941 =
                        let uu____15943 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____15957 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____15959 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____15957
                                    uu____15959))
                           in
                        FStar_All.pipe_right uu____15943
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                        uu____15879 uu____15941
                    else ());
                   (univs1, uvs, (lbname, e, c1))))
              in
           let uu____15980 =
             let uu____15997 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____15997  in
           match uu____15980 with
           | (univs,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____16087 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____16087
                 then ()
                 else
                   (let uu____16092 = lec_hd  in
                    match uu____16092 with
                    | (lb1,uu____16100,uu____16101) ->
                        let uu____16102 = lec2  in
                        (match uu____16102 with
                         | (lb2,uu____16110,uu____16111) ->
                             let msg =
                               let uu____16114 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16116 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____16114 uu____16116
                                in
                             let uu____16119 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____16119))
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
                 let uu____16187 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____16187
                 then ()
                 else
                   (let uu____16192 = lec_hd  in
                    match uu____16192 with
                    | (lb1,uu____16200,uu____16201) ->
                        let uu____16202 = lec2  in
                        (match uu____16202 with
                         | (lb2,uu____16210,uu____16211) ->
                             let msg =
                               let uu____16214 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____16216 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____16214 uu____16216
                                in
                             let uu____16219 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____16219))
                  in
               let lecs1 =
                 let uu____16230 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____16283 = univs_and_uvars_of_lec this_lec  in
                        match uu____16283 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____16230 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail rng k =
                   let uu____16393 = lec_hd  in
                   match uu____16393 with
                   | (lbname,e,c) ->
                       let uu____16403 =
                         let uu____16409 =
                           let uu____16411 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____16413 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____16415 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____16411 uu____16413 uu____16415
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____16409)
                          in
                       FStar_Errors.raise_error uu____16403 rng
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____16437 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____16437 with
                         | FStar_Pervasives_Native.Some uu____16446 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____16454 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____16458 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____16458 with
                              | (bs,kres) ->
                                  ((let uu____16478 =
                                      let uu____16479 =
                                        let uu____16482 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____16482
                                         in
                                      uu____16479.FStar_Syntax_Syntax.n  in
                                    match uu____16478 with
                                    | FStar_Syntax_Syntax.Tm_type uu____16483
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____16487 =
                                          let uu____16489 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____16489  in
                                        if uu____16487
                                        then
                                          fail
                                            u.FStar_Syntax_Syntax.ctx_uvar_range
                                            kres
                                        else ()
                                    | uu____16494 ->
                                        fail
                                          u.FStar_Syntax_Syntax.ctx_uvar_range
                                          kres);
                                   (let a =
                                      let uu____16496 =
                                        let uu____16499 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____16502  ->
                                             FStar_Pervasives_Native.Some
                                               uu____16502) uu____16499
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____16496
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____16510 ->
                                          let uu____16511 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____16511
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
                      (fun uu____16614  ->
                         match uu____16614 with
                         | (lbname,e,c) ->
                             let uu____16660 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____16721 ->
                                   let uu____16734 = (e, c)  in
                                   (match uu____16734 with
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
                                                (fun uu____16774  ->
                                                   match uu____16774 with
                                                   | (x,uu____16780) ->
                                                       let uu____16781 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____16781)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____16799 =
                                                let uu____16801 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____16801
                                                 in
                                              if uu____16799
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____16810 =
                                            let uu____16811 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____16811.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16810 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____16836 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____16836 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____16847 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____16851 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____16851, gen_tvars))
                                in
                             (match uu____16660 with
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
        (let uu____16998 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____16998
         then
           let uu____17001 =
             let uu____17003 =
               FStar_List.map
                 (fun uu____17018  ->
                    match uu____17018 with
                    | (lb,uu____17027,uu____17028) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____17003 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____17001
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____17054  ->
                match uu____17054 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____17083 = gen env is_rec lecs  in
           match uu____17083 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____17182  ->
                       match uu____17182 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____17244 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____17244
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____17292  ->
                           match uu____17292 with
                           | (l,us,e,c,gvs) ->
                               let uu____17326 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____17328 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____17330 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____17332 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____17334 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____17326 uu____17328 uu____17330
                                 uu____17332 uu____17334))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames  ->
              fun uu____17379  ->
                match uu____17379 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____17423 =
                      check_universe_generalization univnames
                        generalized_univs t
                       in
                    (l, uu____17423, t, c, gvs)) univnames_lecs
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
        let uu____17478 =
          let uu____17482 =
            let uu____17484 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____17484  in
          FStar_Pervasives_Native.Some uu____17482  in
        FStar_Profiling.profile
          (fun uu____17501  -> generalize' env is_rec lecs) uu____17478
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
              let uu____17558 =
                FStar_TypeChecker_Rel.get_teq_predicate env2 t1 t21  in
              match uu____17558 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some f ->
                  let uu____17564 = FStar_TypeChecker_Env.apply_guard f e  in
                  FStar_All.pipe_right uu____17564
                    (fun uu____17567  ->
                       FStar_Pervasives_Native.Some uu____17567)
            else
              if env2.FStar_TypeChecker_Env.use_eq
              then FStar_TypeChecker_Rel.try_teq true env2 t1 t21
              else
                (let uu____17576 =
                   FStar_TypeChecker_Rel.get_subtyping_predicate env2 t1 t21
                    in
                 match uu____17576 with
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some f ->
                     let uu____17582 = FStar_TypeChecker_Env.apply_guard f e
                        in
                     FStar_All.pipe_left
                       (fun uu____17585  ->
                          FStar_Pervasives_Native.Some uu____17585)
                       uu____17582)
             in
          let uu____17586 = maybe_coerce_lc env1 e lc t2  in
          match uu____17586 with
          | (e1,lc1,g_c) ->
              let uu____17602 =
                check env1 lc1.FStar_TypeChecker_Common.res_typ t2  in
              (match uu____17602 with
               | FStar_Pervasives_Native.None  ->
                   let uu____17611 =
                     FStar_TypeChecker_Err.expected_expression_of_type env1
                       t2 e1 lc1.FStar_TypeChecker_Common.res_typ
                      in
                   let uu____17617 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____17611 uu____17617
               | FStar_Pervasives_Native.Some g ->
                   ((let uu____17626 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____17626
                     then
                       let uu____17631 =
                         FStar_TypeChecker_Rel.guard_to_string env1 g  in
                       FStar_All.pipe_left
                         (FStar_Util.print1 "Applied guard is %s\n")
                         uu____17631
                     else ());
                    (let uu____17637 = FStar_TypeChecker_Env.conj_guard g g_c
                        in
                     (e1, lc1, uu____17637))))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.lcomp ->
        (Prims.bool * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        (let uu____17665 =
           FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
         if uu____17665
         then
           let uu____17668 = FStar_TypeChecker_Common.lcomp_to_string lc  in
           FStar_Util.print1 "check_top_level, lc = %s\n" uu____17668
         else ());
        (let discharge g1 =
           FStar_TypeChecker_Rel.force_trivial_guard env g1;
           FStar_TypeChecker_Common.is_pure_lcomp lc  in
         let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
         let uu____17682 = FStar_TypeChecker_Common.lcomp_comp lc  in
         match uu____17682 with
         | (c,g_c) ->
             let uu____17694 = FStar_TypeChecker_Common.is_total_lcomp lc  in
             if uu____17694
             then
               let uu____17702 =
                 let uu____17704 = FStar_TypeChecker_Env.conj_guard g1 g_c
                    in
                 discharge uu____17704  in
               (uu____17702, c)
             else
               (let steps =
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.NoFullNorm;
                  FStar_TypeChecker_Env.DoNotUnfoldPureLets]  in
                let c1 =
                  let uu____17712 =
                    let uu____17713 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                    FStar_All.pipe_right uu____17713
                      FStar_Syntax_Syntax.mk_Comp
                     in
                  FStar_All.pipe_right uu____17712
                    (FStar_TypeChecker_Normalize.normalize_comp steps env)
                   in
                let uu____17714 = check_trivial_precondition env c1  in
                match uu____17714 with
                | (ct,vc,g_pre) ->
                    ((let uu____17730 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Simplification")
                         in
                      if uu____17730
                      then
                        let uu____17735 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.print1 "top-level VC: %s\n" uu____17735
                      else ());
                     (let uu____17740 =
                        let uu____17742 =
                          let uu____17743 =
                            FStar_TypeChecker_Env.conj_guard g_c g_pre  in
                          FStar_TypeChecker_Env.conj_guard g1 uu____17743  in
                        discharge uu____17742  in
                      let uu____17744 =
                        FStar_All.pipe_right ct FStar_Syntax_Syntax.mk_Comp
                         in
                      (uu____17740, uu____17744)))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head  ->
    fun seen_args  ->
      let short_bin_op f uu___8_17778 =
        match uu___8_17778 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst,uu____17788)::[] -> f fst
        | uu____17813 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____17825 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____17825
          (fun uu____17826  ->
             FStar_TypeChecker_Common.NonTrivial uu____17826)
         in
      let op_or_e e =
        let uu____17837 =
          let uu____17838 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____17838  in
        FStar_All.pipe_right uu____17837
          (fun uu____17841  ->
             FStar_TypeChecker_Common.NonTrivial uu____17841)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun uu____17848  ->
             FStar_TypeChecker_Common.NonTrivial uu____17848)
         in
      let op_or_t t =
        let uu____17859 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____17859
          (fun uu____17862  ->
             FStar_TypeChecker_Common.NonTrivial uu____17862)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun uu____17869  ->
             FStar_TypeChecker_Common.NonTrivial uu____17869)
         in
      let short_op_ite uu___9_17875 =
        match uu___9_17875 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____17885)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____17912)::[] ->
            let uu____17953 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____17953
              (fun uu____17954  ->
                 FStar_TypeChecker_Common.NonTrivial uu____17954)
        | uu____17955 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____17967 =
          let uu____17975 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____17975)  in
        let uu____17983 =
          let uu____17993 =
            let uu____18001 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____18001)  in
          let uu____18009 =
            let uu____18019 =
              let uu____18027 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____18027)  in
            let uu____18035 =
              let uu____18045 =
                let uu____18053 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____18053)  in
              let uu____18061 =
                let uu____18071 =
                  let uu____18079 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____18079)  in
                [uu____18071; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____18045 :: uu____18061  in
            uu____18019 :: uu____18035  in
          uu____17993 :: uu____18009  in
        uu____17967 :: uu____17983  in
      match head.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____18141 =
            FStar_Util.find_map table
              (fun uu____18156  ->
                 match uu____18156 with
                 | (x,mk) ->
                     let uu____18173 = FStar_Ident.lid_equals x lid  in
                     if uu____18173
                     then
                       let uu____18178 = mk seen_args  in
                       FStar_Pervasives_Native.Some uu____18178
                     else FStar_Pervasives_Native.None)
             in
          (match uu____18141 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____18182 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____18190 =
      let uu____18191 = FStar_Syntax_Util.un_uinst l  in
      uu____18191.FStar_Syntax_Syntax.n  in
    match uu____18190 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____18196 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd,uu____18232)::uu____18233 -> FStar_Syntax_Syntax.range_of_bv hd
        | uu____18252 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____18261,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____18262))::uu____18263 -> bs
      | uu____18281 ->
          let uu____18282 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____18282 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____18286 =
                 let uu____18287 = FStar_Syntax_Subst.compress t  in
                 uu____18287.FStar_Syntax_Syntax.n  in
               (match uu____18286 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____18291) ->
                    let uu____18312 =
                      FStar_Util.prefix_until
                        (fun uu___10_18352  ->
                           match uu___10_18352 with
                           | (uu____18360,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____18361)) ->
                               false
                           | uu____18366 -> true) bs'
                       in
                    (match uu____18312 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____18402,uu____18403) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____18475,uu____18476) ->
                         let uu____18549 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____18570  ->
                                   match uu____18570 with
                                   | (x,uu____18579) ->
                                       let uu____18584 =
                                         FStar_Ident.string_of_id
                                           x.FStar_Syntax_Syntax.ppname
                                          in
                                       FStar_Util.starts_with uu____18584 "'"))
                            in
                         if uu____18549
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____18630  ->
                                     match uu____18630 with
                                     | (x,i) ->
                                         let uu____18649 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____18649, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____18660 -> bs))
  
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
            let uu____18689 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____18689
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                e.FStar_Syntax_Syntax.pos
  
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
          let uu____18720 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____18720
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              e.FStar_Syntax_Syntax.pos
  
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
        (let uu____18763 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____18763
         then
           ((let uu____18768 = FStar_Ident.string_of_lid lident  in
             d uu____18768);
            (let uu____18770 = FStar_Ident.string_of_lid lident  in
             let uu____18772 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____18770 uu____18772))
         else ());
        (let fv =
           let uu____18778 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____18778
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
         let uu____18790 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Range.dummyRange
            in
         ((let uu___2133_18792 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___2133_18792.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___2133_18792.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___2133_18792.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___2133_18792.FStar_Syntax_Syntax.sigattrs);
             FStar_Syntax_Syntax.sigopts =
               (uu___2133_18792.FStar_Syntax_Syntax.sigopts)
           }), uu____18790))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___11_18810 =
        match uu___11_18810 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18813 -> false  in
      let reducibility uu___12_18821 =
        match uu___12_18821 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____18828 -> false  in
      let assumption uu___13_18836 =
        match uu___13_18836 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____18840 -> false  in
      let reification uu___14_18848 =
        match uu___14_18848 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____18851 -> true
        | uu____18853 -> false  in
      let inferred uu___15_18861 =
        match uu___15_18861 with
        | FStar_Syntax_Syntax.Discriminator uu____18863 -> true
        | FStar_Syntax_Syntax.Projector uu____18865 -> true
        | FStar_Syntax_Syntax.RecordType uu____18871 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____18881 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____18894 -> false  in
      let has_eq uu___16_18902 =
        match uu___16_18902 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____18906 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____18985 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____18992 -> true  in
      let check_erasable quals se1 r =
        let lids = FStar_Syntax_Util.lids_of_sigelt se1  in
        let val_exists =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let uu____19025 =
                    FStar_TypeChecker_Env.try_lookup_val_decl env l  in
                  FStar_Option.isSome uu____19025))
           in
        let val_has_erasable_attr =
          FStar_All.pipe_right lids
            (FStar_Util.for_some
               (fun l  ->
                  let attrs_opt =
                    FStar_TypeChecker_Env.lookup_attrs_of_lid env l  in
                  (FStar_Option.isSome attrs_opt) &&
                    (let uu____19056 = FStar_Option.get attrs_opt  in
                     FStar_Syntax_Util.has_attribute uu____19056
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
           | FStar_Syntax_Syntax.Sig_bundle uu____19076 ->
               let uu____19085 =
                 let uu____19087 =
                   FStar_All.pipe_right quals
                     (FStar_Util.for_some
                        (fun uu___17_19093  ->
                           match uu___17_19093 with
                           | FStar_Syntax_Syntax.Noeq  -> true
                           | uu____19096 -> false))
                    in
                 Prims.op_Negation uu____19087  in
               if uu____19085
               then
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_QulifierListNotPermitted,
                     "Incompatible attributes and qualifiers: erasable types do not support decidable equality and must be marked `noeq`")
                   r
               else ()
           | FStar_Syntax_Syntax.Sig_declare_typ uu____19103 -> ()
           | FStar_Syntax_Syntax.Sig_fail uu____19110 -> ()
           | uu____19123 ->
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
      let uu____19137 =
        let uu____19139 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___18_19145  ->
                  match uu___18_19145 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____19148 -> false))
           in
        FStar_All.pipe_right uu____19139 Prims.op_Negation  in
      if uu____19137
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____19169 =
            let uu____19175 =
              let uu____19177 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____19177 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____19175)  in
          FStar_Errors.raise_error uu____19169 r  in
        let err msg = err' (Prims.op_Hat ": " msg)  in
        let err'1 uu____19195 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____19203 =
            let uu____19205 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____19205  in
          if uu____19203 then err "ill-formed combination" else ());
         check_erasable quals se r;
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____19216),uu____19217) ->
              ((let uu____19229 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____19229
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____19238 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____19238
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____19249 ->
              ((let uu____19259 =
                  let uu____19261 =
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
                  Prims.op_Negation uu____19261  in
                if uu____19259 then err'1 () else ());
               (let uu____19271 =
                  (FStar_All.pipe_right quals
                     (FStar_List.existsb
                        (fun uu___19_19277  ->
                           match uu___19_19277 with
                           | FStar_Syntax_Syntax.Unopteq  -> true
                           | uu____19280 -> false)))
                    &&
                    (FStar_Syntax_Util.has_attribute
                       se.FStar_Syntax_Syntax.sigattrs
                       FStar_Parser_Const.erasable_attr)
                   in
                if uu____19271
                then
                  err
                    "unopteq is not allowed on an erasable inductives since they don't have decidable equality"
                else ()))
          | FStar_Syntax_Syntax.Sig_declare_typ uu____19286 ->
              let uu____19293 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____19293 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____19301 ->
              let uu____19308 =
                let uu____19310 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____19310  in
              if uu____19308 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____19320 ->
              let uu____19321 =
                let uu____19323 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____19323  in
              if uu____19321 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19333 ->
              let uu____19346 =
                let uu____19348 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____19348  in
              if uu____19346 then err'1 () else ()
          | uu____19358 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec descend env t1 =
        let uu____19397 =
          let uu____19398 = FStar_Syntax_Subst.compress t1  in
          uu____19398.FStar_Syntax_Syntax.n  in
        match uu____19397 with
        | FStar_Syntax_Syntax.Tm_arrow uu____19402 ->
            let uu____19417 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____19417 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 (FStar_Syntax_Util.is_ghost_effect
                    (FStar_Syntax_Util.comp_effect_name c))
                   ||
                   ((FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
                      (aux env1 (FStar_Syntax_Util.comp_result c))))
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____19426;
               FStar_Syntax_Syntax.index = uu____19427;
               FStar_Syntax_Syntax.sort = t2;_},uu____19429)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_app (head,uu____19438) -> descend env head
        | FStar_Syntax_Syntax.Tm_uinst (head,uu____19464) -> descend env head
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_TypeChecker_Env.fv_has_attr env fv
              FStar_Parser_Const.must_erase_for_extraction_attr
        | uu____19470 -> false
      
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
        (let uu____19480 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____19480
         then
           let uu____19485 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____19485
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
                  let uu____19550 =
                    FStar_TypeChecker_Err.unexpected_signature_for_monad env
                      eff_name t
                     in
                  FStar_Errors.raise_error uu____19550 r  in
                let uu____19560 =
                  FStar_TypeChecker_Env.inst_tscheme signature_ts  in
                match uu____19560 with
                | (uu____19569,signature) ->
                    let uu____19571 =
                      let uu____19572 = FStar_Syntax_Subst.compress signature
                         in
                      uu____19572.FStar_Syntax_Syntax.n  in
                    (match uu____19571 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19580) ->
                         let bs1 = FStar_Syntax_Subst.open_binders bs  in
                         (match bs1 with
                          | a::bs2 ->
                              let uu____19628 =
                                FStar_TypeChecker_Env.uvars_for_binders env
                                  bs2
                                  [FStar_Syntax_Syntax.NT
                                     ((FStar_Pervasives_Native.fst a), a_tm)]
                                  (fun b  ->
                                     let uu____19644 =
                                       FStar_Syntax_Print.binder_to_string b
                                        in
                                     let uu____19646 =
                                       FStar_Ident.string_of_lid eff_name  in
                                     let uu____19648 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.format3
                                       "uvar for binder %s when creating a fresh repr for %s at %s"
                                       uu____19644 uu____19646 uu____19648) r
                                 in
                              (match uu____19628 with
                               | (is,g) ->
                                   let uu____19661 =
                                     match repr_ts_opt with
                                     | FStar_Pervasives_Native.None  ->
                                         let eff_c =
                                           let uu____19663 =
                                             let uu____19664 =
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
                                                 = uu____19664;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____19663
                                            in
                                         let uu____19683 =
                                           let uu____19684 =
                                             let uu____19699 =
                                               let uu____19708 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   FStar_Syntax_Syntax.t_unit
                                                  in
                                               [uu____19708]  in
                                             (uu____19699, eff_c)  in
                                           FStar_Syntax_Syntax.Tm_arrow
                                             uu____19684
                                            in
                                         FStar_Syntax_Syntax.mk uu____19683 r
                                     | FStar_Pervasives_Native.Some repr_ts
                                         ->
                                         let repr =
                                           let uu____19739 =
                                             FStar_TypeChecker_Env.inst_tscheme_with
                                               repr_ts [u]
                                              in
                                           FStar_All.pipe_right uu____19739
                                             FStar_Pervasives_Native.snd
                                            in
                                         let uu____19748 =
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg (a_tm
                                             :: is)
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app repr
                                           uu____19748 r
                                      in
                                   (uu____19661, g))
                          | uu____19757 -> fail signature)
                     | uu____19758 -> fail signature)
  
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
            let uu____19789 =
              FStar_All.pipe_right eff_name
                (FStar_TypeChecker_Env.get_effect_decl env)
               in
            FStar_All.pipe_right uu____19789
              (fun ed  ->
                 let uu____19797 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 fresh_effect_repr env r eff_name
                   ed.FStar_Syntax_Syntax.signature uu____19797 u a_tm)
  
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
              let uu____19833 =
                FStar_TypeChecker_Env.inst_tscheme_with sig_ts [u]  in
              match uu____19833 with
              | (uu____19838,sig_tm) ->
                  let fail t =
                    let uu____19846 =
                      FStar_TypeChecker_Err.unexpected_signature_for_monad
                        env eff_name t
                       in
                    FStar_Errors.raise_error uu____19846 r  in
                  let uu____19852 =
                    let uu____19853 = FStar_Syntax_Subst.compress sig_tm  in
                    uu____19853.FStar_Syntax_Syntax.n  in
                  (match uu____19852 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,uu____19857) ->
                       let bs1 = FStar_Syntax_Subst.open_binders bs  in
                       (match bs1 with
                        | (a',uu____19880)::bs2 ->
                            FStar_All.pipe_right bs2
                              (FStar_Syntax_Subst.subst_binders
                                 [FStar_Syntax_Syntax.NT (a', a_tm)])
                        | uu____19902 -> fail sig_tm)
                   | uu____19903 -> fail sig_tm)
  
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
          (let uu____19934 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____19934
           then
             let uu____19939 = FStar_Syntax_Print.comp_to_string c  in
             let uu____19941 = FStar_Syntax_Print.lid_to_string tgt  in
             FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
               uu____19939 uu____19941
           else ());
          (let r = FStar_TypeChecker_Env.get_range env  in
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let lift_name =
             let uu____19950 =
               FStar_Ident.string_of_lid ct.FStar_Syntax_Syntax.effect_name
                in
             let uu____19952 = FStar_Ident.string_of_lid tgt  in
             FStar_Util.format2 "%s ~> %s" uu____19950 uu____19952  in
           let uu____19955 =
             let uu____19966 =
               FStar_List.hd ct.FStar_Syntax_Syntax.comp_univs  in
             let uu____19967 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (FStar_List.map FStar_Pervasives_Native.fst)
                in
             (uu____19966, (ct.FStar_Syntax_Syntax.result_typ), uu____19967)
              in
           match uu____19955 with
           | (u,a,c_is) ->
               let uu____20015 =
                 FStar_TypeChecker_Env.inst_tscheme_with lift_ts [u]  in
               (match uu____20015 with
                | (uu____20024,lift_t) ->
                    let lift_t_shape_error s =
                      let uu____20035 =
                        FStar_Ident.string_of_lid
                          ct.FStar_Syntax_Syntax.effect_name
                         in
                      let uu____20037 = FStar_Ident.string_of_lid tgt  in
                      let uu____20039 =
                        FStar_Syntax_Print.term_to_string lift_t  in
                      FStar_Util.format4
                        "Lift from %s to %s has unexpected shape, reason: %s (lift:%s)"
                        uu____20035 uu____20037 s uu____20039
                       in
                    let uu____20042 =
                      let uu____20075 =
                        let uu____20076 = FStar_Syntax_Subst.compress lift_t
                           in
                        uu____20076.FStar_Syntax_Syntax.n  in
                      match uu____20075 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) when
                          (FStar_List.length bs) >= (Prims.of_int (2)) ->
                          let uu____20140 =
                            FStar_Syntax_Subst.open_comp bs c1  in
                          (match uu____20140 with
                           | (a_b::bs1,c2) ->
                               let uu____20200 =
                                 FStar_All.pipe_right bs1
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs1) -
                                         Prims.int_one))
                                  in
                               (a_b, uu____20200, c2))
                      | uu____20288 ->
                          let uu____20289 =
                            let uu____20295 =
                              lift_t_shape_error
                                "either not an arrow or not enough binders"
                               in
                            (FStar_Errors.Fatal_UnexpectedEffect,
                              uu____20295)
                             in
                          FStar_Errors.raise_error uu____20289 r
                       in
                    (match uu____20042 with
                     | (a_b,(rest_bs,f_b::[]),lift_c) ->
                         let uu____20413 =
                           let uu____20420 =
                             let uu____20421 =
                               let uu____20422 =
                                 let uu____20429 =
                                   FStar_All.pipe_right a_b
                                     FStar_Pervasives_Native.fst
                                    in
                                 (uu____20429, a)  in
                               FStar_Syntax_Syntax.NT uu____20422  in
                             [uu____20421]  in
                           FStar_TypeChecker_Env.uvars_for_binders env
                             rest_bs uu____20420
                             (fun b  ->
                                let uu____20446 =
                                  FStar_Syntax_Print.binder_to_string b  in
                                let uu____20448 =
                                  FStar_Ident.string_of_lid
                                    ct.FStar_Syntax_Syntax.effect_name
                                   in
                                let uu____20450 =
                                  FStar_Ident.string_of_lid tgt  in
                                let uu____20452 =
                                  FStar_Range.string_of_range r  in
                                FStar_Util.format4
                                  "implicit var for binder %s of %s~>%s at %s"
                                  uu____20446 uu____20448 uu____20450
                                  uu____20452) r
                            in
                         (match uu____20413 with
                          | (rest_bs_uvars,g) ->
                              ((let uu____20466 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____20466
                                then
                                  let uu____20471 =
                                    FStar_List.fold_left
                                      (fun s  ->
                                         fun u1  ->
                                           let uu____20480 =
                                             let uu____20482 =
                                               FStar_Syntax_Print.term_to_string
                                                 u1
                                                in
                                             Prims.op_Hat ";;;;" uu____20482
                                              in
                                           Prims.op_Hat s uu____20480) ""
                                      rest_bs_uvars
                                     in
                                  FStar_Util.print1 "Introduced uvars: %s\n"
                                    uu____20471
                                else ());
                               (let substs =
                                  FStar_List.map2
                                    (fun b  ->
                                       fun t  ->
                                         let uu____20513 =
                                           let uu____20520 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           (uu____20520, t)  in
                                         FStar_Syntax_Syntax.NT uu____20513)
                                    (a_b :: rest_bs) (a :: rest_bs_uvars)
                                   in
                                let guard_f =
                                  let f_sort =
                                    let uu____20539 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort
                                        (FStar_Syntax_Subst.subst substs)
                                       in
                                    FStar_All.pipe_right uu____20539
                                      FStar_Syntax_Subst.compress
                                     in
                                  let f_sort_is =
                                    let uu____20545 =
                                      FStar_TypeChecker_Env.is_layered_effect
                                        env
                                        ct.FStar_Syntax_Syntax.effect_name
                                       in
                                    effect_args_from_repr f_sort uu____20545
                                      r
                                     in
                                  FStar_List.fold_left2
                                    (fun g1  ->
                                       fun i1  ->
                                         fun i2  ->
                                           let uu____20554 =
                                             FStar_TypeChecker_Rel.layered_effect_teq
                                               env i1 i2
                                               (FStar_Pervasives_Native.Some
                                                  lift_name)
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             g1 uu____20554)
                                    FStar_TypeChecker_Env.trivial_guard c_is
                                    f_sort_is
                                   in
                                let lift_ct =
                                  let uu____20557 =
                                    FStar_All.pipe_right lift_c
                                      (FStar_Syntax_Subst.subst_comp substs)
                                     in
                                  FStar_All.pipe_right uu____20557
                                    FStar_Syntax_Util.comp_to_comp_typ
                                   in
                                let is =
                                  let uu____20561 =
                                    FStar_TypeChecker_Env.is_layered_effect
                                      env tgt
                                     in
                                  effect_args_from_repr
                                    lift_ct.FStar_Syntax_Syntax.result_typ
                                    uu____20561 r
                                   in
                                let fml =
                                  let uu____20566 =
                                    let uu____20571 =
                                      FStar_List.hd
                                        lift_ct.FStar_Syntax_Syntax.comp_univs
                                       in
                                    let uu____20572 =
                                      let uu____20573 =
                                        FStar_List.hd
                                          lift_ct.FStar_Syntax_Syntax.effect_args
                                         in
                                      FStar_Pervasives_Native.fst uu____20573
                                       in
                                    (uu____20571, uu____20572)  in
                                  match uu____20566 with
                                  | (u1,wp) ->
                                      FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                        env u1
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                        wp FStar_Range.dummyRange
                                   in
                                (let uu____20599 =
                                   (FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects"))
                                     &&
                                     (FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme)
                                    in
                                 if uu____20599
                                 then
                                   let uu____20605 =
                                     FStar_Syntax_Print.term_to_string fml
                                      in
                                   FStar_Util.print1 "Guard for lift is: %s"
                                     uu____20605
                                 else ());
                                (let c1 =
                                   let uu____20611 =
                                     let uu____20612 =
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
                                         uu____20612;
                                       FStar_Syntax_Syntax.flags = []
                                     }  in
                                   FStar_Syntax_Syntax.mk_Comp uu____20611
                                    in
                                 (let uu____20636 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "LayeredEffects")
                                     in
                                  if uu____20636
                                  then
                                    let uu____20641 =
                                      FStar_Syntax_Print.comp_to_string c1
                                       in
                                    FStar_Util.print1 "} Lifted comp: %s\n"
                                      uu____20641
                                  else ());
                                 (let uu____20646 =
                                    let uu____20647 =
                                      FStar_TypeChecker_Env.conj_guard g
                                        guard_f
                                       in
                                    let uu____20648 =
                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                        (FStar_TypeChecker_Common.NonTrivial
                                           fml)
                                       in
                                    FStar_TypeChecker_Env.conj_guard
                                      uu____20647 uu____20648
                                     in
                                  (c1, uu____20646)))))))))
  
let lift_tf_layered_effect_term :
  'uuuuuu20662 .
    'uuuuuu20662 ->
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
              let uu____20691 =
                let uu____20696 =
                  FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift
                    FStar_Util.must
                   in
                FStar_All.pipe_right uu____20696
                  (fun ts  -> FStar_TypeChecker_Env.inst_tscheme_with ts [u])
                 in
              FStar_All.pipe_right uu____20691 FStar_Pervasives_Native.snd
               in
            let rest_bs =
              let lift_t =
                FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
                  FStar_Util.must
                 in
              let uu____20739 =
                let uu____20740 =
                  let uu____20743 =
                    FStar_All.pipe_right lift_t FStar_Pervasives_Native.snd
                     in
                  FStar_All.pipe_right uu____20743
                    FStar_Syntax_Subst.compress
                   in
                uu____20740.FStar_Syntax_Syntax.n  in
              match uu____20739 with
              | FStar_Syntax_Syntax.Tm_arrow (uu____20766::bs,uu____20768)
                  when (FStar_List.length bs) >= Prims.int_one ->
                  let uu____20808 =
                    FStar_All.pipe_right bs
                      (FStar_List.splitAt
                         ((FStar_List.length bs) - Prims.int_one))
                     in
                  FStar_All.pipe_right uu____20808
                    FStar_Pervasives_Native.fst
              | uu____20914 ->
                  let uu____20915 =
                    let uu____20921 =
                      let uu____20923 =
                        FStar_Syntax_Print.tscheme_to_string lift_t  in
                      FStar_Util.format1
                        "lift_t tscheme %s is not an arrow with enough binders"
                        uu____20923
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____20921)  in
                  FStar_Errors.raise_error uu____20915
                    (FStar_Pervasives_Native.snd lift_t).FStar_Syntax_Syntax.pos
               in
            let args =
              let uu____20950 = FStar_Syntax_Syntax.as_arg a  in
              let uu____20959 =
                let uu____20970 =
                  FStar_All.pipe_right rest_bs
                    (FStar_List.map
                       (fun uu____21006  ->
                          FStar_Syntax_Syntax.as_arg
                            FStar_Syntax_Syntax.unit_const))
                   in
                let uu____21013 =
                  let uu____21024 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____21024]  in
                FStar_List.append uu____20970 uu____21013  in
              uu____20950 :: uu____20959  in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (lift, args))
              e.FStar_Syntax_Syntax.pos
  
let (get_field_projector_name :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> FStar_Ident.lident)
  =
  fun env  ->
    fun datacon  ->
      fun index  ->
        let uu____21095 = FStar_TypeChecker_Env.lookup_datacon env datacon
           in
        match uu____21095 with
        | (uu____21100,t) ->
            let err n =
              let uu____21110 =
                let uu____21116 =
                  let uu____21118 = FStar_Ident.string_of_lid datacon  in
                  let uu____21120 = FStar_Util.string_of_int n  in
                  let uu____21122 = FStar_Util.string_of_int index  in
                  FStar_Util.format3
                    "Data constructor %s does not have enough binders (has %s, tried %s)"
                    uu____21118 uu____21120 uu____21122
                   in
                (FStar_Errors.Fatal_UnexpectedDataConstructor, uu____21116)
                 in
              let uu____21126 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____21110 uu____21126  in
            let uu____21127 =
              let uu____21128 = FStar_Syntax_Subst.compress t  in
              uu____21128.FStar_Syntax_Syntax.n  in
            (match uu____21127 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____21132) ->
                 let bs1 =
                   FStar_All.pipe_right bs
                     (FStar_List.filter
                        (fun uu____21187  ->
                           match uu____21187 with
                           | (uu____21195,q) ->
                               (match q with
                                | FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit (true )) ->
                                    false
                                | uu____21204 -> true)))
                    in
                 if (FStar_List.length bs1) <= index
                 then err (FStar_List.length bs1)
                 else
                   (let b = FStar_List.nth bs1 index  in
                    FStar_Syntax_Util.mk_field_projector_name datacon
                      (FStar_Pervasives_Native.fst b) index)
             | uu____21238 -> err Prims.int_zero)
  
let (get_mlift_for_subeff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.mlift)
  =
  fun env  ->
    fun sub  ->
      let uu____21251 =
        (FStar_TypeChecker_Env.is_layered_effect env
           sub.FStar_Syntax_Syntax.source)
          ||
          (FStar_TypeChecker_Env.is_layered_effect env
             sub.FStar_Syntax_Syntax.target)
         in
      if uu____21251
      then
        let uu____21254 =
          let uu____21267 =
            FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
              FStar_Util.must
             in
          lift_tf_layered_effect sub.FStar_Syntax_Syntax.target uu____21267
           in
        {
          FStar_TypeChecker_Env.mlift_wp = uu____21254;
          FStar_TypeChecker_Env.mlift_term =
            (FStar_Pervasives_Native.Some
               (lift_tf_layered_effect_term env sub))
        }
      else
        (let mk_mlift_wp ts env1 c =
           let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
           let uu____21302 =
             FStar_TypeChecker_Env.inst_tscheme_with ts
               ct.FStar_Syntax_Syntax.comp_univs
              in
           match uu____21302 with
           | (uu____21311,lift_t) ->
               let wp = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
               let uu____21330 =
                 let uu____21331 =
                   let uu___2510_21332 = ct  in
                   let uu____21333 =
                     let uu____21344 =
                       let uu____21353 =
                         let uu____21354 =
                           let uu____21355 =
                             let uu____21372 =
                               let uu____21383 =
                                 FStar_Syntax_Syntax.as_arg
                                   ct.FStar_Syntax_Syntax.result_typ
                                  in
                               [uu____21383; wp]  in
                             (lift_t, uu____21372)  in
                           FStar_Syntax_Syntax.Tm_app uu____21355  in
                         FStar_Syntax_Syntax.mk uu____21354
                           (FStar_Pervasives_Native.fst wp).FStar_Syntax_Syntax.pos
                          in
                       FStar_All.pipe_right uu____21353
                         FStar_Syntax_Syntax.as_arg
                        in
                     [uu____21344]  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___2510_21332.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (sub.FStar_Syntax_Syntax.target);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___2510_21332.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args = uu____21333;
                     FStar_Syntax_Syntax.flags =
                       (uu___2510_21332.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____21331  in
               (uu____21330, FStar_TypeChecker_Common.trivial_guard)
            in
         let mk_mlift_term ts u r e =
           let uu____21483 = FStar_TypeChecker_Env.inst_tscheme_with ts [u]
              in
           match uu____21483 with
           | (uu____21490,lift_t) ->
               let uu____21492 =
                 let uu____21493 =
                   let uu____21510 =
                     let uu____21521 = FStar_Syntax_Syntax.as_arg r  in
                     let uu____21530 =
                       let uu____21541 =
                         FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                          in
                       let uu____21550 =
                         let uu____21561 = FStar_Syntax_Syntax.as_arg e  in
                         [uu____21561]  in
                       uu____21541 :: uu____21550  in
                     uu____21521 :: uu____21530  in
                   (lift_t, uu____21510)  in
                 FStar_Syntax_Syntax.Tm_app uu____21493  in
               FStar_Syntax_Syntax.mk uu____21492 e.FStar_Syntax_Syntax.pos
            in
         let uu____21614 =
           let uu____21627 =
             FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift_wp
               FStar_Util.must
              in
           FStar_All.pipe_right uu____21627 mk_mlift_wp  in
         {
           FStar_TypeChecker_Env.mlift_wp = uu____21614;
           FStar_TypeChecker_Env.mlift_term =
             (match sub.FStar_Syntax_Syntax.lift with
              | FStar_Pervasives_Native.None  ->
                  FStar_Pervasives_Native.Some
                    ((fun uu____21663  ->
                        fun uu____21664  -> fun e  -> FStar_Util.return_all e))
              | FStar_Pervasives_Native.Some ts ->
                  FStar_Pervasives_Native.Some (mk_mlift_term ts))
         })
  
let (update_env_sub_eff :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun sub  ->
      let uu____21687 = get_mlift_for_subeff env sub  in
      FStar_TypeChecker_Env.update_effect_lattice env
        sub.FStar_Syntax_Syntax.source sub.FStar_Syntax_Syntax.target
        uu____21687
  
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
  